use foundationdb::*;
use futures::prelude::*;
use std::sync::Arc;
use tokio::runtime::Runtime;

mod common;

#[test]
#[ignore]
// FIXME: reenable this test in CI until issue #170 is resolved
// dropping a future while it's in the pending state should not crash
fn test_tokio_send() {
    common::boot();

    let mut rt = Runtime::new().unwrap();
    rt.block_on(async {
        do_transact().await;
        do_trx().await;
    });
}
async fn do_transact() {
    let db = Arc::new(
        foundationdb::Database::new_compat(None)
            .await
            .expect("failed to open fdb"),
    );

    let adb = db.clone();
    tokio::spawn(async move {
        async fn txnfn(_txn: &Transaction) -> FdbResult<()> {
            Ok(())
        }

        adb.transact_boxed(
            (),
            |txn: &Transaction, ()| txnfn(txn).boxed(),
            TransactOption::default(),
        )
        .await
        .expect("failed to transact")
    });
}

async fn do_trx() {
    let db = Arc::new(
        foundationdb::Database::new_compat(None)
            .await
            .expect("failed to open fdb"),
    );

    let adb = db.clone();
    tokio::spawn(async move {
        adb.create_trx()
            .expect("failed to create trx")
            .commit()
            .await
            .expect("failed to commit");
    });
}
