//! Headless acceptance harness.
//! `cargo run --release --no-default-features --bin harness -- [episodes] [--threads N] [--quick] [--extended] [--coverage]`
use cityflight::harness::*;
use cityflight::world::World;
use std::io::Write;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    #[cfg(feature = "jsb")]
    if args.iter().any(|a| a == "--jsb") {
        cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    let episodes = args
        .iter()
        .enumerate()
        .find(|(i, a)| a.parse::<usize>().is_ok() && (*i == 0 || args[i - 1] != "--threads"))
        .map(|(_, a)| a.parse().unwrap())
        .unwrap_or(200);
    let extended = args.iter().any(|a| a == "--extended");
    let kamikaze_secs = if args.iter().any(|a| a == "--quick") { 60.0 } else { 300.0 };
    let threads = args
        .iter()
        .position(|a| a == "--threads")
        .and_then(|i| args.get(i + 1)?.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
    let t0 = Instant::now();
    let world = World::new(1337);
    eprintln!("world: {} boxes, built in {:.2}s; {} threads", world.boxes.len(), t0.elapsed().as_secs_f64(), threads);
    if args.iter().any(|a| a == "--coverage") {
        let t = Instant::now();
        print!("{}", format_coverage(&street_coverage(&world, 2000, threads, 0.0), ""));
        print!("{}", format_coverage(&street_coverage(&world, 2000, threads, 4.0), " (4 deg heading error)"));
        println!("({:.1}s)", t.elapsed().as_secs_f64());
        return;
    }
    let opts = HarnessOpts { episodes, threads, kamikaze_secs, extended };
    let rep = run_harness(&world, &opts, &|name, d, n| {
        if d == n || d % 10 == 0 {
            eprint!("\r{:<28} {:>4}/{:<4}", name, d, n);
            if d == n {
                eprintln!();
            }
            let _ = std::io::stderr().flush();
        }
    });
    println!("{}", format_report(&rep));
    println!("total {:.1}s", t0.elapsed().as_secs_f64());
    if !rep.checks.iter().all(|c| c.1) {
        std::process::exit(1);
    }
}
