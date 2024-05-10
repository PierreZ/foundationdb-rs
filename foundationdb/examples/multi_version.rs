use byteorder::ByteOrder;
use foundationdb::api::FdbApiBuilder;
use foundationdb::options::NetworkOption;
use foundationdb::tuple::Subspace;
use foundationdb::{options, Database, FdbError, Transaction};

/// This example demonstrate usage of multi_version compatibility client.
///
/// While you still need to compile the crate with a specific FoundationDB library version,
/// it allows you to connect to a cluster with a different API version. Be aware that using
/// this feature might lead to divergent behaviors.
///
/// Ref: https://apple.github.io/foundationdb/api-general.html#multi-version-client-api

const NETWORK_OPTION_EXTERNAL_CLIENT_DIRECTORY: &str = "FDB_NETWORK_OPTION_EXTERNAL_CLIENT_DIRECTORY";

#[tokio::main]
async fn main() {
    let mut network_builder = FdbApiBuilder::default().build().expect("Failed to build API");
    // You can either use FoundationDB network option through environment variables
    // or through network options in code.
    // directory specified should contain at least one libfdb.so
    if !std::env::var(NETWORK_OPTION_EXTERNAL_CLIENT_DIRECTORY).is_ok() {
        network_builder = network_builder
            .set_option(NetworkOption::ExternalClientDirectory("/usr/lib/foundationdb/".to_string()))
            .expect("Failed to add external library directory");
    }
    let _guard = unsafe { 
        network_builder.boot()
    };

    // You can replace `None` with an `Option` with the path to your `fdb.cluster` file
    let db = Database::new_compat(None)
        .await
        .expect("failed to get database");

    let counter_key = Subspace::all().subspace(&"stats").pack(&"my_counter");

	// used to catch the first cluster_version_changed error when using external clients
	// when using external clients, it will throw cluster_version_changed for the first time establish the connection to
	// the cluster. Thus, we catch it by doing a get version request to establish the connection
	// The 3000ms timeout is a guard to avoid waiting forever when the cli cannot talk to any coordinators
    loop {
        let trx = db.create_trx().expect("could not create transaction");
        trx.set_option(options::TransactionOption::Timeout(3000)).expect("Failed to set timeout option");
        if let Err(e) = trx.get_read_version().await {
            // 1039: cluster_version_changed
            if e.code() == 1039 {
                continue;
            }

            panic!("Unexpected error {} while initializing the multiversion client", e.code());
        }
        break;
    }
    // write initial value
    let trx = db.create_trx().expect("could not create transaction");
    increment(&trx, &counter_key, 1);
    trx.commit().await.expect("could not commit");

    // read counter
    let trx = db.create_trx().expect("could not create transaction");
    let v1 = read_counter(&trx, &counter_key)
        .await
        .expect("could not read counter");
    dbg!(v1);
    assert!(v1 > 0);
}

async fn read_counter(trx: &Transaction, key: &[u8]) -> Result<i64, FdbError> {
    let raw_counter = trx
        .get(key, true)
        .await
        .expect("could not read key")
        .expect("no value found");

    let counter = byteorder::LE::read_i64(raw_counter.as_ref());
    Ok(counter)
}

fn increment(trx: &Transaction, key: &[u8], incr: i64) {
    // generate the right buffer for atomic_op
    let mut buf = [0u8; 8];
    byteorder::LE::write_i64(&mut buf, incr);

    trx.atomic_op(key, &buf, options::MutationType::Add);
}
