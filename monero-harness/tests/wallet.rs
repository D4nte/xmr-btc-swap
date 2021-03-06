use curve25519_dalek::scalar::Scalar;
use monero::{Address, Network, PrivateKey, PublicKey};
use monero_harness::Monero;
use rand::rngs::OsRng;
use spectral::prelude::*;
use testcontainers::clients::Cli;

#[tokio::test]
async fn fund_transfer_and_check_tx_key() {
    let fund_alice: u64 = 1_000_000_000_000;
    let fund_bob = 0;
    let send_to_bob = 5_000_000_000;

    let tc = Cli::default();
    let (monero, _containers) = Monero::new(&tc, Some("test_".to_string()), vec![
        "alice".to_string(),
        "bob".to_string(),
    ])
    .await
    .unwrap();
    let alice_wallet = monero.wallet("alice").unwrap();
    let bob_wallet = monero.wallet("bob").unwrap();
    let miner_wallet = monero.wallet("miner").unwrap();

    let miner_address = miner_wallet.address().await.unwrap().address;

    // fund alice
    monero
        .init(vec![("alice", fund_alice), ("bob", fund_bob)])
        .await
        .unwrap();

    // check alice balance
    alice_wallet.refresh().await.unwrap();
    let got_alice_balance = alice_wallet.balance().await.unwrap();
    assert_that(&got_alice_balance).is_equal_to(fund_alice);

    // transfer from alice to bob
    let bob_address = bob_wallet.address().await.unwrap().address;
    let transfer = alice_wallet
        .transfer(&bob_address, send_to_bob)
        .await
        .unwrap();

    monero
        .monerod()
        .client()
        .generate_blocks(10, &miner_address)
        .await
        .unwrap();

    bob_wallet.refresh().await.unwrap();
    let got_bob_balance = bob_wallet.balance().await.unwrap();
    assert_that(&got_bob_balance).is_equal_to(send_to_bob);

    // check if tx was actually seen
    let tx_id = transfer.tx_hash;
    let tx_key = transfer.tx_key;
    let res = bob_wallet
        .client()
        .check_tx_key(&tx_id, &tx_key, &bob_address)
        .await
        .expect("failed to check tx by key");

    assert_that!(res.received).is_equal_to(send_to_bob);
}

#[tokio::test]
async fn load_watch_only_wallet() {
    let tc = Cli::default();
    let (monero, _containers) = Monero::new(&tc, None, vec!["watch-only".into()])
        .await
        .unwrap();
    let miner_wallet = monero.wallet("miner").unwrap();

    let (_spend_sk, spend_pk) = {
        let scalar = Scalar::random(&mut OsRng);
        let sk = PrivateKey::from_scalar(scalar);
        let pk = PublicKey::from_private_key(&sk);

        (sk, pk)
    };
    let (view_sk, view_pk) = {
        let scalar = Scalar::random(&mut OsRng);
        let sk = PrivateKey::from_scalar(scalar);
        let pk = PublicKey::from_private_key(&sk);

        (sk, pk)
    };
    let address = Address::standard(Network::Mainnet, spend_pk, view_pk);

    let one_xmr = 1_000_000_000_000;

    monero.init(Vec::new()).await.unwrap();

    miner_wallet
        .client()
        .transfer(0, one_xmr, &address.to_string())
        .await
        .unwrap();

    let watch_only_wallet = monero.wallet("watch-only").unwrap();

    watch_only_wallet
        .client()
        .generate_from_keys(&address.to_string(), None, &view_sk.to_string())
        .await
        .unwrap();
    watch_only_wallet.client().refresh().await.unwrap();

    let balance = watch_only_wallet.client().get_balance(0).await.unwrap();

    assert_eq!(balance, one_xmr);
}
