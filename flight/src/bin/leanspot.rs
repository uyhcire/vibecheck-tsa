//! Lean vs Rust gate, every escape from a map's starts: `leanspot [N] [--map grid|sf] [--frames F]`.
use cityflight::envfilter::{rollout, Outcome, N_ESC};
use cityflight::jsb::JsbPlant;
use cityflight::leangate::LeanGate;
use cityflight::sim::{random_start, scenario_names, scenario_start};
use cityflight::world::{MapId, Rng, World};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let arg = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let n: usize = args.first().and_then(|s| s.parse().ok()).unwrap_or(6);
    let map = arg("--map").map_or(MapId::SanFrancisco, |m| MapId::parse(&m).expect("--map takes grid or sf"));
    let frames: usize = arg("--frames").and_then(|s| s.parse().ok()).unwrap_or(2048);
    let world = World::load(map);
    let mut starts: Vec<(String, [f64; 10])> =
        scenario_names(map).iter().enumerate().map(|(k, name)| (name.replace(' ', "_"), scenario_start(&world, k))).collect();
    let mut rng = Rng::new(0x5F5);
    for k in 0..n {
        starts.push((format!("random{k}"), random_start(&world, &mut rng)));
    }
    let (mut same_path, mut same_end, mut lean_cautious, mut rust_cautious, mut total) = (0, 0, 0, 0, 0);
    println!("start esc | samples same | rust end frame | lean end frame | verdict");
    for (name, s) in &starts {
        let g = LeanGate::new(&world, s);
        let p = JsbPlant::new(s);
        for esc in 0..N_ESC {
            let r = rollout(&world, &p, esc, frames);
            let (lp, lend) = g.rollout(esc, frames);
            // Rust samples the start and every 8th frame; Lean reports every frame.
            let k = r.path.len().min(lp.len() / 8 + 1);
            let first_diff = (1..k).find(|&i| (0..3).any(|c| r.path[i][c].to_bits() != lp[8 * i - 1].0[c].to_bits()));
            let start_same = (0..3).all(|c| r.path.first().map_or(true, |q| q[c].to_bits() == g.pos[c].to_bits()));
            let path_same = first_diff.is_none() && start_same;
            let rust_end = match r.outcome {
                Outcome::Ok => "end-test",
                Outcome::Hit => "clearance",
                Outcome::Horizon => "horizon",
                Outcome::Budget => "budget",
            };
            let lean_end = match lend {
                0 => "clearance",
                1 => "cap/street",
                3 => "end-test",
                _ => "frames",
            };
            let verdict = match (r.outcome == Outcome::Ok, lend == 3) {
                (true, true) if r.frames == lp.len() => "same (end test passes on the same frame)",
                (true, true) => "both pass (different frames)",
                (false, false) => "both fail",
                (true, false) => "Lean more cautious",
                (false, true) => "Rust more cautious",
            };
            total += 1;
            same_path += path_same as usize;
            same_end += ((r.outcome == Outcome::Ok) == (lend == 3)) as usize;
            lean_cautious += (r.outcome == Outcome::Ok && lend != 3) as usize;
            rust_cautious += (r.outcome != Outcome::Ok && lend == 3) as usize;
            println!(
                "{name} {esc} | {} | {rust_end} {} | {lean_end} {} | {verdict}",
                if path_same { format!("all {k}") } else { format!("differ from sample {}", first_diff.unwrap_or(0)) },
                r.frames,
                lp.len(),
            );
        }
    }
    println!(
        "{}: {total} escapes from {} starts; paths bit-identical {same_path}; verdicts agree {same_end}; Lean alone fails {lean_cautious}; Rust alone fails {rust_cautious}",
        map.name(),
        starts.len()
    );
}
