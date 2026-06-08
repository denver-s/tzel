//! Print the L2 asset_id (hex) that the kernel derives for a given
//! FA2 ticketer KT1 address. Used by `scripts/originate_fa2_bridge.sh`
//! to keep the printed asset_id in lock-step with whatever
//! `tzel_core::derive_asset_id` actually computes — no risk of the
//! shell script and the kernel disagreeing about the derivation.
//!
//! Usage:
//!   cargo run --package tzel-services --bin derive_asset_id_cli -- <KT1...>
//!
//! Prints the asset_id as 64 lowercase hex chars on stdout. Any
//! parsing or hash error is printed to stderr and the program exits
//! with status 1.

use tzel_core::derive_asset_id;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 1 {
        eprintln!("usage: derive_asset_id_cli <ticketer-KT1-address>");
        std::process::exit(64);
    }
    let ticketer = &args[0];
    let asset_id = derive_asset_id(ticketer);
    println!("{}", hex::encode(asset_id));
}
