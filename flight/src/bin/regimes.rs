//! Boundary-regime slices of the gate filter: markers, binding causes and plots (`docs/boundary-regimes`).
//! `cargo run --release --no-default-features --features jsb --bin regimes -- [calib | find | probe ...]`
use cityflight::regimes::*;
use cityflight::world::*;

const DOCS: &str = "../docs/boundary-regimes";

fn slices() -> Vec<SliceDef> {
    use cityflight::model::*;
    use std::f64::consts::FRAC_PI_2;
    let sd = |key, title, param, unit, lo, hi, make: fn(&World, f64) -> State| SliceDef { key, title, param, unit, lo, hi, n: 41, tol: 0.5, make, lead: 3.0, flip: false, cam: "--cinematic --cam 0" };
    vec![
        SliceDef { cam: "--cinematic", ..sd("01a-street-dive", "Dive at the Tower gap street floor", "height above the street", "m", 2.0, 250.0, |w, d| {
            let (x, y) = (-120.0, -150.0);
            trimmed(x, y, w.terrain(x, y) + d, 50.0, -30f64.to_radians(), FRAC_PI_2, 0.6)
        }) },
        SliceDef { cam: "--cinematic", ..sd("01b-park-dive", "Dive at the park", "height above the park", "m", 2.0, 250.0, |w, d| {
            let (x, y) = (-360.0, 260.0);
            trimmed(x, y, w.terrain(x, y) + d, 50.0, -35f64.to_radians(), FRAC_PI_2, 0.6)
        }) },
        sd("01c-slow-valley", "Slow and low over the valley", "airspeed", "m/s", 20.0, 36.0, |w, d| {
            let (x, y) = (0.0, -1600.0);
            trimmed(x, y, w.terrain(x, y) + 12.0, d, 8f64.to_radians(), 0.0, 0.0)
        }),
        SliceDef { flip: true, cam: "--cinematic", ..sd("01d-fast-dive", "Fast dive at the park", "airspeed", "m/s", -95.0, -35.0, |w, d| {
            let (x, y) = (-360.0, 260.0);
            trimmed(x, y, w.terrain(x, y) + 45.0, -d, -35f64.to_radians(), FRAC_PI_2, 0.6)
        }) },
        sd("02a-wall-beside-park", "Beside the park-side tower", "distance to the face", "m", 0.0, 80.0, |w, d| {
            let (x, y) = (-218.1 - d, 265.0);
            let mut s = trimmed(x, y, w.terrain(x, y) + 50.0, 45.0, 0.0, FRAC_PI_2 - 10f64.to_radians(), 0.7);
            s[PHI] = 0.0;
            s
        }),
        SliceDef { flip: true, ..sd("02b-wall-beside-angle", "Closing on the park-side tower at an angle", "heading angle into the face", "deg", -45.0, 0.0, |w, d| {
            let (x, y) = (-218.1 - 25.0, 265.0);
            trimmed(x, y, w.terrain(x, y) + 50.0, 45.0, 0.0, FRAC_PI_2 + d.to_radians(), 0.7)
        }) },
        sd("03-canyon", "Canyon run east along y = 120", "height above the street", "m", 15.0, 170.0, |w, d| {
            let (x, y) = (-470.0, 120.0);
            trimmed(x, y, w.terrain(x, y) + d, 45.0, 0.0, 0.0, 0.7)
        }),
        sd("04a-wall-ahead", "Wall ahead across the park", "distance to the face", "m", 5.0, 250.0, |w, d| {
            let (x, y) = (-218.1 - d, 295.0);
            trimmed(x, y, w.terrain(x, y) + 50.0, 45.0, 0.0, 0.0, 0.7)
        }),
        sd("04b-slow-wallow", "Slow wallow toward the park-side tower", "distance to the face", "m", 5.0, 250.0, |w, d| {
            let (x, y) = (-218.1 - d, 295.0);
            trimmed(x, y, w.terrain(x, y) + 40.0, 27.0, 6f64.to_radians(), 0.0, 0.25)
        }),
        sd("05-ridge", "Level run at the ridge", "distance to the crest", "m", 150.0, 1100.0, |w, d| {
            let (x, y) = (150.0, w.ridge_y + d);
            trimmed(x, y, w.terrain(x, w.ridge_y + 900.0) + 60.0, 45.0, 0.0, -FRAC_PI_2, 0.7)
        }),
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let what = args.first().map_or("all", |s| s.as_str());
    let world = World::new(1337);
    cityflight::jsb::JSB_PLANT.store(true, std::sync::atomic::Ordering::Relaxed);
    cityflight::envfilter::ENV_FILTER.store(cityflight::envfilter::parse("gate"), std::sync::atomic::Ordering::Relaxed);
    match what {
        "calib" => calib(),
        "find" => {
            // Tall boxes with wide faces.
            let mut v: Vec<(f64, usize)> = world.boxes.iter().enumerate().map(|(i, b)| (b.z1 - world.terrain(0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1)), i)).collect();
            v.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
            for (h, i) in v.iter().take(60) {
                let b = &world.boxes[*i];
                println!("box {i:4} lot {:4} h {h:5.0} x [{:7.1},{:7.1}] y [{:7.1},{:7.1}] w {:5.1} d {:5.1}", b.lot, b.x0, b.x1, b.y0, b.y1, b.x1 - b.x0, b.y1 - b.y0);
            }
            println!("parks {:?}", world.parks);
            println!("streets {:?}", (0..21).map(|k| (street_x(k), world.street_w[k])).collect::<Vec<_>>());
            println!("top {:.0}", cityflight::envfilter::top(&world));
        }
        "near" => {
            // regimes near X0 X1 Y0 Y1: boxes in a window.
            let f = |i: usize| args[i].parse::<f64>().unwrap();
            let (x0, x1, y0, y1) = (f(1), f(2), f(3), f(4));
            for (i, b) in world.boxes.iter().enumerate() {
                if b.x1 >= x0 && b.x0 <= x1 && b.y1 >= y0 && b.y0 <= y1 {
                    println!("box {i:4} h {:5.0} top {:5.0} x [{:7.1},{:7.1}] y [{:7.1},{:7.1}] w {:5.1} d {:5.1}", b.z1 - world.terrain(0.5 * (b.x0 + b.x1), 0.5 * (b.y0 + b.y1)), b.z1, b.x0, b.x1, b.y0, b.y1, b.x1 - b.x0, b.y1 - b.y0);
                }
            }
            for y in [y0, 0.5 * (y0 + y1), y1] {
                println!("terrain at y {y:.0}: {:?}", (0..=8).map(|k| (world.terrain(x0 + (x1 - x0) * k as f64 / 8.0, y) * 10.0).round() / 10.0).collect::<Vec<_>>());
            }
        }
        "canyons" => {
            // Street runs whose walls (highest roof within 30 m of each street edge) stay uniform.
            for ns in [true, false] {
                for k in 1..20usize {
                    let c = street_x(k);
                    let hw = world.street_w[k] / 2.0;
                    let mut prof = Vec::new();
                    let mut u = -1150.0;
                    while u <= 1150.0 {
                        let side = |sgn: f64| {
                            let mut m = 0f64;
                            let mut o = hw + 1.0;
                            while o < hw + 30.0 {
                                let (x, y) = if ns { (c + sgn * o, u) } else { (u, c + sgn * o) };
                                m = m.max(world.surface(x, y) - world.terrain(x, y));
                                o += 2.5;
                            }
                            m
                        };
                        prof.push((u, side(-1.0), side(1.0)));
                        u += 5.0;
                    }
                    // Windows of 240 m: share of samples with both walls above 60 m, and the walls' 20th percentile.
                    let win = 48;
                    let mut best = (0.0, 0.0, 0.0, 0.0);
                    for i in (0..prof.len().saturating_sub(win)).step_by(4) {
                        let w = &prof[i..i + win];
                        let both = w.iter().filter(|p| p.1.min(p.2) > 60.0).count() as f64 / win as f64;
                        let mut m: Vec<f64> = w.iter().map(|p| p.1.min(p.2)).collect();
                        m.sort_by(|a, b| a.partial_cmp(b).unwrap());
                        if both > best.0 {
                            best = (both, m[win / 5], w[0].0, w[win - 1].0);
                        }
                    }
                    if best.0 > 0.5 {
                        println!("{} k={k} c={c} u {:6.0}..{:6.0} both>60m {:.0}% p20 wall {:.0}", if ns { "NS" } else { "EW" }, best.2, best.3, best.0 * 100.0, best.1);
                    }
                }
            }
        }
        "run" => {
            // regimes run [KEY..] [--threads N]: every slice (or those named): grid, markers, JSON and SVG.
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(6);
            let keys: Vec<&String> = args[1..].iter().take_while(|a| !a.starts_with("--")).collect();
            for def in slices().into_iter().filter(|d| keys.is_empty() || keys.iter().any(|k| d.key.starts_with(k.as_str()))) {
                let t0 = std::time::Instant::now();
                let pts = cityflight::harness::par_map(grid_ds(&def), threads, |&d| eval_point(&world, &def, d), |_, _| {});
                let m = markers(&world, &def, &pts, threads);
                let dir = format!("{DOCS}/{}", folder(&def));
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(format!("{dir}/{}.json", def.key), json_slice(&def, &pts, &m)).unwrap();
                std::fs::write(format!("{dir}/{}.svg", def.key), svg_slice(&def, &pts, &m)).unwrap();
                let f = |x: Option<f64>| x.map_or("-".into(), |v| format!("{:.1}", def.show(v)));
                println!("{}: gate accepts {} | proven safe {} | best found {} | proven unsafe {} ({}) [{:.0} s] nz max {:.2}", def.key, f(m.gate), f(m.safe), f(m.best), f(m.unsafe_), def.unit, t0.elapsed().as_secs_f64(), m.nz_max);
                println!("   program at best found: {:?}", m.best_prog);
            }
        }
        "demo" => {
            // regimes demo [KEY..]: the demo flights of each slice, headless, and their commands.
            // As the GUI does: full-horizon checks (`CHECK_THREADS` ≥ 1; the verdict does not depend on the count).
            cityflight::envfilter::CHECK_THREADS.store(1, std::sync::atomic::Ordering::Relaxed);
            let keys: Vec<&String> = args[1..].iter().take_while(|a| !a.starts_with("--")).collect();
            for def in slices().into_iter().filter(|d| keys.is_empty() || keys.iter().any(|k| d.key.starts_with(k.as_str()))) {
                let cam = def.cam;
                match demo_slice(&world, &def, cam) {
                    Some(d) => {
                        let md = demo_md(&def, &d);
                        std::fs::write(format!("{DOCS}/{}/{}-shots.sh", folder(&def), def.key), shots_sh(&def, &d)).unwrap();
                        std::fs::write(format!("{DOCS}/{}/{}-demos.md", folder(&def), def.key), &md).unwrap();
                        println!("{md}");
                    }
                    None => println!("{}: no proven-safe marker", def.key),
                }
            }
        }
        "index" => {
            // regimes index: the markers and gaps of every slice as a markdown table (from the JSON files).
            println!("| Slice | Parameter | Gate accepts (4 m) | Proven safe | Best found | Proven unsafe | Gate's margin | Escape library | Outer-bound slack |\n|---|---|---|---|---|---|---|---|---|");
            for def in slices() {
                let g = |n: &str| read_marker(&def, n).map(|v| def.show(v));
                let (ga, s0, b, u) = (g("gate_accepts"), g("proven_safe"), g("best_found"), g("proven_unsafe"));
                let f = |x: Option<f64>| x.map_or("–".into(), |v| format!("{v:.1}"));
                let gap = |a: Option<f64>, b: Option<f64>| match (a, b) { (Some(a), Some(b)) => format!("{:.1}", (a - b).abs()), _ => "–".into() };
                println!("| [{}]({}/README.md) | {} ({}) | {} | {} | {} | {} | {} | {} | {} |", def.key, folder(&def), def.param, def.unit, f(ga), f(s0), f(b), f(u), gap(ga, s0), gap(s0, b), gap(b, u));
            }
        }
        "probe" => {
            // regimes probe KEY: grid only, printed.
            let key = args.get(1).cloned().unwrap_or_default();
            let def = slices().into_iter().find(|d| d.key.starts_with(&key)).expect("slice");
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(6);
            let t0 = std::time::Instant::now();
            let pts = cityflight::harness::par_map(grid_ds(&def), threads, |&d| eval_point(&world, &def, d), |_, _| {});
            for p in &pts {
                let causes: Vec<String> = p.lib.per_esc.iter().map(|e| format!("{}{}", e.cause.short(), if e.env.is_empty() { String::new() } else { format!("[{}]", e.env) })).collect();
                println!("{} {:6.1} gate {} safe {} best {} ({} ev) bound {:?} | {} | {}", def.param, def.show(p.d), p.gate.ok as u8, p.lib.ok as u8, p.best.ok as u8, p.best.evals, p.bound.as_ref().map(|b| (b.test, (b.t * 100.0).round() / 100.0)), causes.join(" "), p.best.prog.as_ref().map_or(String::new(), |g| g.text()));
            }
            println!("{:.0} s", t0.elapsed().as_secs_f64());
        }
        "wild" => {
            // regimes wild [EPISODES] [--threads N]: commit runs of the harness episodes, by regime.
            let n: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(200);
            let threads: usize = args.iter().position(|a| a == "--threads").and_then(|i| args.get(i + 1)?.parse().ok()).unwrap_or(6);
            let evs: Vec<WildEvent> = cityflight::harness::par_map((0..n).collect(), threads, |&e| wild_episode(&world, e, 60.0), |d, t| eprint!("\r{d}/{t}")).into_iter().flatten().collect();
            let mut csv = String::from("episode,t,regime,cause,v,min_clear,crashed\n");
            for e in &evs {
                csv += &format!("{},{:.2},{},{},{:.1},{:.2},{}\n", e.episode, e.t, e.regime.map_or("none", |k| REGIMES[k]), e.cause.short(), e.v, e.min_clear, e.crashed);
            }
            std::fs::create_dir_all(DOCS).unwrap();
            std::fs::write(format!("{DOCS}/wild.csv"), csv).unwrap();
            for (k, r) in REGIMES.iter().enumerate() {
                println!("{r}: {} commit runs", evs.iter().filter(|e| e.regime == Some(k)).count());
            }
        }
        _ => {}
    }
}

/// The regime folder a slice belongs to.
fn folder(def: &SliceDef) -> &'static str {
    let n: usize = def.key[..2].parse().unwrap();
    REGIMES[n - 1]
}

fn esc_names() -> Vec<&'static str> {
    cityflight::envfilter::ESCAPES.iter().map(|e| e.name).collect()
}

/// The cause that binds at a slice point: the cause of the escape that failed latest (verified if any verified).
fn dominant(p: &Point) -> Cause {
    if p.lib.ok {
        return Cause::Ok;
    }
    p.lib.per_esc.iter().filter(|e| e.cause != Cause::NoStreet).max_by(|a, b| a.t.partial_cmp(&b.t).unwrap()).map_or(Cause::NoStreet, |e| e.cause)
}

fn json_slice(def: &SliceDef, pts: &[Point], m: &Markers) -> String {
    let opt = |x: Option<f64>| x.map_or("null".to_string(), |v| format!("{:.2}", def.show(v)));
    let mut o = format!(
        "{{\"key\":\"{}\",\"title\":\"{}\",\"param\":\"{}\",\"unit\":\"{}\",\"markers\":{{\"gate_accepts\":{},\"proven_safe\":{},\"best_found\":{},\"proven_unsafe\":{}}},\"best_program\":\"{}\",\"nz_max_search\":{:.2},\"points\":[",
        def.key, def.title, def.param, def.unit, opt(m.gate), opt(m.safe), opt(m.best), opt(m.unsafe_), m.best_prog.clone().unwrap_or_default(), m.nz_max
    );
    for (i, p) in pts.iter().enumerate() {
        let gate_ok = p.gate.ok;
        let esc: Vec<String> = p.lib.per_esc.iter().map(|e| format!("{{\"outcome\":\"{:?}\",\"cause\":\"{}\",\"envelope\":\"{}\",\"t\":{:.2},\"min_clear\":{:.2},\"nz_max\":{:.2}}}", e.outcome, e.cause.short(), e.env, e.t, e.min_clear.min(999.0), e.nz_max)).collect();
        o += &format!(
            "{}{{\"d\":{:.3},\"gate\":{},\"safe\":{},\"best\":{},\"bound\":{},\"escapes_at_contact\":[{}]}}",
            if i > 0 { "," } else { "" },
            def.show(p.d),
            gate_ok,
            p.lib.ok,
            p.best.ok,
            p.bound.as_ref().map_or("null".into(), |b| format!("{{\"test\":\"{}\",\"t\":{:.2}}}", b.test, b.t)),
            esc.join(",")
        );
    }
    o + "]}"
}

fn svg_slice(def: &SliceDef, pts: &[Point], m: &Markers) -> String {
    let (w, h) = (1000.0, 614.0);
    let (x0, x1) = (140.0, w - 30.0);
    let (lo, hi) = (def.show(def.lo).min(def.show(def.hi)), def.show(def.lo).max(def.show(def.hi)));
    // Danger on the left: for flipped slices (speed) the axis runs from high to low values.
    let xs = |v: f64| if def.flip { x1 - (v - lo) / (hi - lo) * (x1 - x0) } else { x0 + (v - lo) / (hi - lo) * (x1 - x0) };
    let mut o = format!("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" viewBox=\"0 0 {w} {h}\" font-family=\"Helvetica, Arial, sans-serif\" font-size=\"12\">\n<rect width=\"100%\" height=\"100%\" fill=\"white\"/>\n");
    o += &format!("<text x=\"{x0}\" y=\"24\" font-size=\"16\" font-weight=\"bold\">{}: {}</text>\n", def.key, def.title);
    // Panel A: clearance of the best verified filter escape and of the found program.
    let (ay0, ay1) = (85.0, 235.0);
    let cmax = 40.0;
    let ys = |c: f64| ay1 - (c.clamp(0.0, cmax) / cmax) * (ay1 - ay0);
    // Gap bands.
    let band = |a: Option<f64>, b: Option<f64>, col: &str, label: &str, o: &mut String| {
        if let (Some(a), Some(b)) = (a, b) {
            let (xa, xb) = (xs(def.show(a)), xs(def.show(b)));
            let (l, r) = (xa.min(xb), xa.max(xb));
            if r - l > 0.5 {
                let label = if r - l > 6.0 * label.len() as f64 { label } else { "" };
                *o += &format!("<rect x=\"{l:.1}\" y=\"{ay0}\" width=\"{:.1}\" height=\"{}\" fill=\"{col}\" opacity=\"0.35\"/>\n", r - l, ay1 - ay0);
                *o += &format!("<text x=\"{:.1}\" y=\"{}\" text-anchor=\"middle\" font-size=\"10\" fill=\"#444\">{label}</text>\n", 0.5 * (l + r), ay0 + 12.0);
            }
        }
    };
    band(m.safe, m.gate, "#bcd7f5", "gate's 4 m margin", &mut o);
    band(m.best, m.safe, "#9fd8b0", "escape library", &mut o);
    band(m.unsafe_, m.best, "#d6d6d6", "outer-bound slack", &mut o);
    o += &format!("<line x1=\"{x0}\" y1=\"{ay1}\" x2=\"{x1}\" y2=\"{ay1}\" stroke=\"#333\"/>\n<line x1=\"{x0}\" y1=\"{ay0}\" x2=\"{x0}\" y2=\"{ay1}\" stroke=\"#333\"/>\n");
    for c in [0.0, 4.0, 10.0, 20.0, 30.0, 40.0] {
        o += &format!("<text x=\"{}\" y=\"{:.1}\" text-anchor=\"end\" font-size=\"10\">{c:.0}</text>\n", x0 - 4.0, ys(c) + 3.0);
    }
    o += &format!("<line x1=\"{x0}\" y1=\"{:.1}\" x2=\"{x1}\" y2=\"{:.1}\" stroke=\"#3b78c4\" stroke-dasharray=\"4 3\"/>\n", ys(4.0), ys(4.0));
    o += &format!("<text x=\"{}\" y=\"{:.1}\" font-size=\"10\" fill=\"#3b78c4\" text-anchor=\"end\">the gate's own margin, 4 m</text>\n", x1, ys(4.0) - 3.0);
    o += &format!("<text x=\"14\" y=\"{}\" font-size=\"11\" transform=\"rotate(-90 14 {})\" text-anchor=\"middle\">min airframe clearance (m)</text>\n", 0.5 * (ay0 + ay1), 0.5 * (ay0 + ay1));
    let line = |vals: Vec<(f64, f64)>, col: &str, dash: &str| -> String {
        let mut s = String::new();
        let mut seg: Vec<String> = Vec::new();
        for (d, c) in vals {
            if c.is_finite() {
                seg.push(format!("{:.1},{:.1}", xs(d), ys(c)));
            } else if !seg.is_empty() {
                s += &format!("<polyline points=\"{}\" fill=\"none\" stroke=\"{col}\" stroke-width=\"2\" stroke-dasharray=\"{dash}\"/>\n", seg.join(" "));
                seg.clear();
            }
        }
        if !seg.is_empty() {
            s += &format!("<polyline points=\"{}\" fill=\"none\" stroke=\"{col}\" stroke-width=\"2\" stroke-dasharray=\"{dash}\"/>\n", seg.join(" "));
        }
        s
    };
    let fbest: Vec<(f64, f64)> = pts.iter().map(|p| (def.show(p.d), p.lib.per_esc.iter().filter(|e| e.outcome == cityflight::envfilter::Outcome::Ok).map(|e| e.min_clear).fold(f64::NAN, f64::max))).collect();
    o += &line(fbest, "#2e9e5b", "");
    o += &format!("<text x=\"{}\" y=\"{}\" font-size=\"10\" fill=\"#2e9e5b\">— the gate's escapes at contact: clearance of the best one that verifies</text>\n", x0 + 6.0, ay1 - 6.0);
    // Markers, labels stacked when close.
    let mut ms: Vec<(f64, &str, &str)> = [(m.unsafe_, "#c0392b", "proven unsafe"), (m.best, "#e08a00", "best found"), (m.safe, "#1e7d45", "proven safe"), (m.gate, "#3b78c4", "gate accepts")]
        .iter()
        .filter_map(|(v, c, l)| v.map(|v| (v, *c, *l)))
        .collect();
    ms.sort_by(|a, b| xs(def.show(a.0)).partial_cmp(&xs(def.show(b.0))).unwrap());
    let mut last_x = f64::NEG_INFINITY;
    let mut row = 0.0;
    for (v, col, label) in ms {
        let x = xs(def.show(v));
        row = if x - last_x < 120.0 { row + 1.0 } else { 0.0 };
        last_x = x;
        let anchor = if x > x1 - 110.0 { "end" } else { "start" };
        let tx = if anchor == "end" { x - 3.0 } else { x + 3.0 };
        o += &format!("<line x1=\"{x:.1}\" y1=\"{}\" x2=\"{x:.1}\" y2=\"{}\" stroke=\"{col}\" stroke-width=\"2\"/>\n", ay0 - 4.0, h - 104.0);
        o += &format!("<text x=\"{tx:.1}\" y=\"{}\" font-size=\"10\" fill=\"{col}\" font-weight=\"bold\" text-anchor=\"{anchor}\">{label} {:.1}</text>\n", ay0 - 6.0 - row * 11.0, def.show(v));
    }
    // Panel B: cause strip per escape, then the three other predicates.
    let names = esc_names();
    let rows: Vec<String> = names.iter().map(|n| n.to_string()).chain(["gate, 4 m", "search", "outer bound"].iter().map(|s| s.to_string())).collect();
    let (by0, rh) = (250.0, 22.0);
    let n = pts.len();
    let cw = (x1 - x0) / (n as f64 - 1.0);
    let mut used: std::collections::BTreeSet<Cause> = Default::default();
    for (ri, name) in rows.iter().enumerate() {
        let y = by0 + ri as f64 * rh;
        o += &format!("<text x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"end\" font-size=\"11\">{name}</text>\n", x0 - cw / 2.0 - 4.0, y + rh * 0.65);
        for p in pts {
            let x = xs(def.show(p.d)) - cw / 2.0;
            let (col, tip) = if ri < names.len() {
                let e = &p.lib.per_esc[ri];
                used.insert(e.cause);
                (e.cause.color().to_string(), format!("{} {}", e.cause.label(), if e.env.is_empty() { String::new() } else { format!("[{} cap]", e.env) }))
            } else {
                let ok = match ri - names.len() {
                    0 => p.gate.ok,
                    1 => p.best.ok,
                    _ => p.bound.is_none(),
                };
                let lab = match (ri - names.len(), ok) { (0, true) => "gate accepts", (0, false) => "gate rejects", (1, true) => "escape found", (1, false) => "none found", (_, true) => "not proven unsafe", _ => "proven unsafe" };
                ((if ok { "#2e9e5b" } else { "#c0392b" }).to_string(), lab.to_string())
            };
            o += &format!("<rect x=\"{x:.1}\" y=\"{y:.1}\" width=\"{:.1}\" height=\"{:.1}\" fill=\"{col}\" stroke=\"white\" stroke-width=\"0.5\"><title>{:.1} {}: {tip}</title></rect>\n", cw, rh - 3.0, def.show(p.d), def.unit);
            if ri < names.len() && !p.lib.per_esc[ri].env.is_empty() {
                o += &format!("<text x=\"{:.1}\" y=\"{:.1}\" font-size=\"8\" fill=\"white\" text-anchor=\"middle\">{}</text>\n", x + cw / 2.0, y + rh * 0.6, if p.lib.per_esc[ri].env.contains("alpha") { "α" } else { "n" });
            }
        }
    }
    // Binding-cause switches along the slice.
    let ys_b = by0 + rows.len() as f64 * rh + 4.0;
    let mut k = 0;
    for w2 in pts.windows(2) {
        let (a, b) = (dominant(&w2[0]), dominant(&w2[1]));
        if a != b && a != Cause::Ok && b != Cause::Ok {
            let x = 0.5 * (xs(def.show(w2[0].d)) + xs(def.show(w2[1].d)));
            let (l, r) = if def.flip { (b, a) } else { (a, b) };
            o += &format!("<path d=\"M{x:.1},{ys_b} l-4,8 l8,0 z\" fill=\"#333\"/><text x=\"{x:.1}\" y=\"{:.1}\" font-size=\"9\" text-anchor=\"middle\">{} | {}</text>\n", ys_b + 18.0 + (k % 2) as f64 * 10.0, l.short(), r.short());
            k += 1;
        }
    }
    // Axis.
    let ax = h - 104.0;
    o += &format!("<line x1=\"{x0}\" y1=\"{ax}\" x2=\"{x1}\" y2=\"{ax}\" stroke=\"#333\"/>\n");
    for k in 0..=8 {
        let v = lo + (hi - lo) * k as f64 / 8.0;
        o += &format!("<text x=\"{:.1}\" y=\"{}\" text-anchor=\"middle\" font-size=\"10\">{:.0}</text>\n", xs(v), ax + 14.0, v);
    }
    o += &format!("<text x=\"{:.1}\" y=\"{}\" text-anchor=\"middle\" font-size=\"12\">{} ({}) — danger on the left</text>\n", 0.5 * (x0 + x1), ax + 30.0, def.param, def.unit);
    // Legend.
    let (mut lx, mut ly) = (x0, h - 54.0);
    for c in Cause::all().iter().filter(|c| used.contains(c)) {
        let wd = 26.0 + 5.6 * c.label().len() as f64;
        if lx + wd > w {
            lx = x0;
            ly += 14.0;
        }
        o += &format!("<rect x=\"{lx:.1}\" y=\"{ly}\" width=\"10\" height=\"10\" fill=\"{}\"/><text x=\"{:.1}\" y=\"{}\" font-size=\"10\">{}</text>\n", c.color(), lx + 13.0, ly + 9.0, c.label());
        lx += wd;
    }
    o += &format!("<text x=\"{x0}\" y=\"{}\" font-size=\"9\" fill=\"#555\">rows 1-6: the gate's escapes judged at contact; gate: its own acceptance with its 4 m margin; search: green = an escape found; outer bound: red = proven unsafe.</text>\n", h - 15.0);
    o += &format!("<text x=\"{x0}\" y=\"{}\" font-size=\"9\" fill=\"#555\" dx=\"0\">n / α in a cell: the escape law's load-factor / angle-of-attack cap bound on over 15% of its frames</text>\n", h - 4.0);
    o + "</svg>\n"
}

/// A marker read back from a slice's JSON (internal parameter, i.e. un-flipped).
fn read_marker(def: &SliceDef, name: &str) -> Option<f64> {
    let path = format!("{DOCS}/{}/{}.json", folder(def), def.key);
    let txt = std::fs::read_to_string(path).ok()?;
    let i = txt.find(&format!("\"{name}\":"))? + name.len() + 3;
    let v: f64 = txt[i..].split(|c| c == ',' || c == '}').next()?.parse().ok()?;
    Some(if def.flip { -v } else { v })
}

/// Each escape flown from `s` with no margin (true contact) for the filter's horizon: whether it hits.
fn escapes_crash(world: &World, s: &cityflight::model::State) -> Vec<(String, bool, f64)> {
    use cityflight::envfilter::*;
    let p = cityflight::jsb::JsbPlant::new(s);
    (0..n_esc())
        .map(|e| {
            let r = rollout_cfg(world, &p, Law::new(e), usize::MAX, None, &cityflight::regimes::CONTACT);
            (ESCAPES[e].name.to_string(), r.outcome == Outcome::Hit, r.t)
        })
        .collect()
}

const GUI: &str = "cargo run --release --features jsb -- --env gate --time-cap 0";

struct Call {
    cmd: String,
    lead: f64,
    on: DemoRun,
    off: DemoRun,
}

struct DemoOut {
    /// The gate with a zero margin, from the proven-safe marker; the deployed gate (4 m) from its own marker.
    zero: Option<Call>,
    deployed: Option<Call>,
    twin_cmd: Option<String>,
    twin_run: Option<DemoRun>,
    twin_delta: f64,
    unsafe_cmd: Option<(String, String)>,
    unsafe_runs: Option<(DemoRun, DemoRun, Vec<(String, bool, f64)>)>,
}

/// The longest lead-in (up to `max`, in 0.25 s steps) whose straight path to `s` keeps 10 m clear.
fn clear_lead(world: &World, s: &cityflight::model::State, max: f64) -> f64 {
    let mut lead = 0.0;
    while lead + 0.25 <= max + 1e-9 {
        let l = lead + 0.25;
        if !(0..=40).all(|k| {
            let q = lead_state(s, l * k as f64 / 40.0);
            world.true_clearance([q[0], q[1], q[2]]) > 10.0
        }) {
            break;
        }
        lead = l;
    }
    lead
}

const ZERO: &str = "--margin 0 --check-every 1";

fn with_margin<R>(zero: bool, f: impl FnOnce() -> R) -> R {
    use cityflight::envfilter::*;
    if zero {
        set_filter_margin(0.0, 1);
    }
    let r = f();
    set_filter_margin(MARGIN, SAMPLE);
    r
}

fn demo_slice(world: &World, def: &SliceDef, cam: &str) -> Option<DemoOut> {
    let label = |what: &str| format!("--label \"{}: {what}\"", def.key);
    let call = |d: f64, zero: bool, what: &str| -> Call {
        let s = (def.make)(world, d);
        let lead = clear_lead(world, &s, def.lead);
        let s0 = lead_state(&s, lead);
        let (on, off) = with_margin(zero, || (demo_run(world, &s0, true, 25.0), demo_run(world, &s0, false, 25.0)));
        let cmd = format!("{GUI}{} --start {} --lead {lead} {cam} --paths {}", if zero { format!(" {ZERO}") } else { String::new() }, start_arg(&s), label(&format!("{what}, {:.1} {}", def.show(d), def.unit)));
        Call { cmd, lead, on, off }
    };
    let d_safe = read_marker(def, "proven_safe");
    let zero = d_safe.map(|d| call(d, true, "closest safe call, zero-margin gate"));
    let deployed = read_marker(def, "gate_accepts").map(|d| call(d, false, "closest call, deployed gate"));
    // The twin: the first start just inside the proven-safe marker that crashes under the zero-margin gate.
    let floor = read_marker(def, "proven_unsafe").unwrap_or(def.lo);
    let mut twin = None;
    if let Some(d_safe) = d_safe {
        let mut delta = def.tol;
        while d_safe - delta > floor {
            let s = (def.make)(world, d_safe - delta);
            let r = with_margin(true, || demo_run(world, &s, true, 25.0));
            if r.crashed {
                twin = Some((s, r, delta));
                break;
            }
            delta *= 2.0;
        }
    }
    let (twin_cmd, twin_run, twin_delta) = match (twin, d_safe) {
        (Some((s, r, dl)), Some(ds)) => (Some(format!("{GUI} {ZERO} --start {} {cam} --paths {}", start_arg(&s), label(&format!("unverified twin, {:.1} {}", def.show(ds - dl), def.unit)))), Some(r), dl),
        _ => (None, None, 0.0),
    };
    let (unsafe_cmd, unsafe_runs) = match read_marker(def, "proven_unsafe") {
        Some(du) => {
            let s = (def.make)(world, du);
            let on = demo_run(world, &s, true, 25.0);
            let off = demo_run(world, &s, false, 25.0);
            let esc = escapes_crash(world, &s);
            let c = format!("{GUI} --start {} {cam} --paths {}", start_arg(&s), label(&format!("proven unsafe, {:.1} {}", def.show(du), def.unit)));
            (Some((c.clone(), c.replace("--paths", "--paths --off"))), Some((on, off, esc)))
        }
        None => (None, None),
    };
    if zero.is_none() && deployed.is_none() {
        return None;
    }
    Some(DemoOut { zero, deployed, twin_cmd, twin_run, twin_delta, unsafe_cmd, unsafe_runs })
}

fn run_text(r: &DemoRun) -> String {
    let commit = match (r.first_commit, r.release) {
        (Some(a), Some(b)) => format!("filter takes over at t = {a:.1} s, hands back at {b:.1} s"),
        (Some(a), None) => format!("filter takes over at t = {a:.1} s"),
        _ => "filter never takes over".into(),
    };
    let runs = if r.commit_runs > 1 { format!(", {} takeovers in all", r.commit_runs) } else { String::new() };
    if r.crashed {
        format!("**crashes** at t = {:.1} s ({commit}{runs}; start {})", r.t_end, if r.first_accept { "verified" } else { "not verified" })
    } else if r.first_commit.is_some() {
        format!("no crash; closest pass during the save **{:.2} m** at t = {:.1} s; minimum over 25 s {:.2} m ({commit}{runs})", r.save_min, r.t_save_min, r.min_clear, runs = runs)
    } else {
        format!("no crash; minimum airframe clearance {:.1} m ({commit})", r.min_clear)
    }
}

fn demo_md(def: &SliceDef, d: &DemoOut) -> String {
    let mut o = format!("### {} ({})\n\n", def.title, def.key);
    if let Some(c) = &d.zero {
        o += &format!("**Closest safe call** (the proven-safe state; the gate with its margin set to zero and clearance checked every frame, `{ZERO}`; pilot lead-in {:.2} s with the sticks released, so the fly-by-wire holds flight path and bank into the obstacle):\n\n```sh\n{}\n```\n\n- filter on: {}\n- filter off (`--off`): {}\n\n", c.lead, c.cmd, run_text(&c.on), run_text(&c.off));
    }
    match (&d.twin_cmd, &d.twin_run) {
        (Some(c), Some(r)) => {
            o += &format!("**Just-barely-unsafe twin**: {:.1} {} closer than the proven-safe marker, no lead-in, same zero-margin gate. No escape verifies at the start, so the gate commits blind to the escape that got farthest:\n\n```sh\n{c}\n```\n\n- filter on: {}\n\n", d.twin_delta, def.unit, run_text(r));
        }
        _ => o += "**Twin**: no start between the proven-safe marker and the outer bound (or the slice's end) crashed under the zero-margin gate: its blind fallback escape survived every one tried.\n\n",
    }
    if let Some(c) = &d.deployed {
        o += &format!("**The deployed gate (4 m margin)** from its own acceptance marker (lead-in {:.2} s):\n\n```sh\n{}\n```\n\n- filter on: {}\n- filter off: {}\n\n", c.lead, c.cmd, run_text(&c.on), run_text(&c.off));
    }
    if let (Some((c_on, c_off)), Some((on, off, esc))) = (&d.unsafe_cmd, &d.unsafe_runs) {
        let n_hit = esc.iter().filter(|e| e.1).count();
        o += &format!("**Closest proven-unsafe call**:\n\n```sh\n{c_on}\n{c_off}\n```\n\n- filter on: {}\n- filter off: {}\n- the gate's escapes flown with no margin: {n_hit} of {} touch ({})\n\n", run_text(on), run_text(off), esc.len(), esc.iter().map(|e| format!("{} {}", e.0, if e.1 { format!("hits at {:.1} s", e.2) } else { "clear".into() })).collect::<Vec<_>>().join(", "));
    }
    o
}

/// Screenshot commands for a slice's demos (`--shot` at the closest pass, or just before the crash).
fn shots_sh(def: &SliceDef, d: &DemoOut) -> String {
    let dir = format!("docs/boundary-regimes/{}/shots", folder(def));
    let bin = "flight/target/release/cityflight --env gate --time-cap 0";
    let strip = |c: &str| c.replacen(GUI, bin, 1);
    let frames = |t: f64| ((t * 60.0).round() as i64 + 2).max(12);
    let mut o = format!("mkdir -p {dir}\n");
    for (c, tag) in [(&d.zero, "safe"), (&d.deployed, "gate")] {
        if let Some(c) = c {
            if c.on.first_commit.is_some() && !c.on.crashed {
                o += &format!("{} --shot {dir}/{}-{tag}.png --frames {}\n", strip(&c.cmd), def.key, frames(c.on.t_save_min));
            }
        }
    }
    if let (Some(c), Some(r)) = (&d.twin_cmd, &d.twin_run) {
        o += &format!("{} --shot {dir}/{}-twin.png --frames {}\n", strip(c), def.key, frames(r.t_end - 0.25));
    }
    if let (Some((_, off)), Some((_, r_off, _))) = (&d.unsafe_cmd, &d.unsafe_runs) {
        o += &format!("{} --shot {dir}/{}-unsafe-off.png --frames {}\n", strip(off), def.key, frames(r_off.t_end - 0.1));
    }
    o
}
