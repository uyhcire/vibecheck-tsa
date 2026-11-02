//! Axis-aligned boxes that contain a world's buildings exactly (interval arithmetic), for the Lean city gate.

use crate::world::World;

/// Most distance (m) from a covering box's point to its footprint, unless `MAX_STRIPS` strips do not reach it.
pub const COVER_TOL: f64 = 1.0;
pub const MAX_STRIPS: usize = 64;

/// Boxes `[x_min, y_min, x_max, y_max, z_min, z_max]`, and the building each covers.
pub struct Cover {
    pub boxes: Vec<[f64; 6]>,
    pub of: Vec<u32>,
}

#[inline]
fn dn(x: f64) -> f64 {
    x.next_down()
}
#[inline]
fn up(x: f64) -> f64 {
    x.next_up()
}

/// An interval holding exactly where segment `v w` crosses `coordinate a = c`, along the other axis.
fn crossing(v: [f64; 2], w: [f64; 2], a: usize, c: f64) -> (f64, f64) {
    let o = 1 - a;
    let ival = |x: f64| (dn(x), up(x));
    let sub = |p: (f64, f64), q: (f64, f64)| (dn(p.0 - q.1), up(p.1 - q.0));
    let mul = |p: (f64, f64), q: (f64, f64)| {
        let c = [p.0 * q.0, p.0 * q.1, p.1 * q.0, p.1 * q.1];
        (dn(c.iter().cloned().fold(f64::INFINITY, f64::min)), up(c.iter().cloned().fold(f64::NEG_INFINITY, f64::max)))
    };
    let num = sub((c, c), (v[a], v[a]));
    let den = sub((w[a], w[a]), (v[a], v[a]));
    let t = if den.0 > 0.0 {
        let q = [num.0 / den.0, num.0 / den.1, num.1 / den.0, num.1 / den.1];
        (dn(q.iter().cloned().fold(f64::INFINITY, f64::min)), up(q.iter().cloned().fold(f64::NEG_INFINITY, f64::max)))
    } else if den.1 < 0.0 {
        let q = [num.0 / den.0, num.0 / den.1, num.1 / den.0, num.1 / den.1];
        (dn(q.iter().cloned().fold(f64::INFINITY, f64::min)), up(q.iter().cloned().fold(f64::NEG_INFINITY, f64::max)))
    } else {
        (0.0, 1.0)
    };
    let t = (t.0.max(0.0), t.1.min(1.0));
    let d = sub(ival(w[o]), ival(v[o]));
    let r = mul(t, d);
    (dn(v[o] + r.0), up(v[o] + r.1))
}

/// Extent along the other axis of the footprint's part with coordinate `a` in `[lo, hi]`, rounded outward.
pub fn slab(poly: &[[f64; 2]], a: usize, lo: f64, hi: f64) -> Option<(f64, f64)> {
    let o = 1 - a;
    let n = poly.len();
    let (mut mn, mut mx) = (f64::INFINITY, f64::NEG_INFINITY);
    for i in 0..n {
        let (v, w) = (poly[i], poly[(i + 1) % n]);
        if v[a] >= lo && v[a] <= hi {
            (mn, mx) = (mn.min(v[o]), mx.max(v[o]));
        }
        for c in [lo, hi] {
            if (v[a] < c && w[a] > c) || (v[a] > c && w[a] < c) {
                let (p, q) = crossing(v, w, a, c);
                (mn, mx) = (mn.min(p), mx.max(q));
            }
        }
    }
    (mn <= mx).then_some((mn, mx))
}

/// `k` strips across axis `a`; neighbours share their boundary value exactly, so they tile the footprint's range.
fn strips(poly: &[[f64; 2]], a: usize, k: usize) -> Vec<(f64, f64, f64, f64)> {
    let lo = poly.iter().map(|p| p[a]).fold(f64::INFINITY, f64::min);
    let hi = poly.iter().map(|p| p[a]).fold(f64::NEG_INFINITY, f64::max);
    let cut = |s: usize| if s == 0 { lo } else if s == k { hi } else { lo + (hi - lo) * s as f64 / k as f64 };
    (0..k)
        .filter_map(|s| {
            let (p, q) = (cut(s), cut(s + 1));
            slab(poly, a, p, q).map(|(m, n)| (p, q, m, n))
        })
        .collect()
}

/// Largest distance from a box point to the footprint: at a corner, since distance to a convex set is convex.
fn excess(poly: &[[f64; 2]], a: usize, st: &[(f64, f64, f64, f64)]) -> f64 {
    let mut e: f64 = 0.0;
    for &(p, q, m, n) in st {
        for u in [p, q] {
            for v in [m, n] {
                let c = if a == 0 { [u, v] } else { [v, u] };
                e = e.max(crate::world::pt_poly_dist2(c, poly));
            }
        }
    }
    e.sqrt()
}

/// Fewest strips within `COVER_TOL` (x before y on a tie), or the tightest at `MAX_STRIPS`.
fn cover_poly(poly: &[[f64; 2]]) -> (usize, Vec<(f64, f64, f64, f64)>) {
    let mut best: Option<(usize, Vec<(f64, f64, f64, f64)>, f64)> = None;
    for a in [0, 1] {
        let mut k = 1;
        loop {
            let st = strips(poly, a, k);
            let e = excess(poly, a, &st);
            if e <= COVER_TOL || k >= MAX_STRIPS {
                let better = match &best {
                    None => true,
                    Some((_, b, be)) => (e <= COVER_TOL && (*be > COVER_TOL || st.len() < b.len())) || (*be > COVER_TOL && e < *be),
                };
                if better {
                    best = Some((a, st, e));
                }
                break;
            }
            k += 1;
        }
    }
    let (a, st, _) = best.unwrap();
    (a, st)
}

/// `f` over `0..n` on every core, results in order.
pub fn par_range<T: Send>(n: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let th = std::thread::available_parallelism().map_or(1, |t| t.get()).min(n.max(1));
    let chunk = n.div_ceil(th.max(1)).max(1);
    std::thread::scope(|sc| {
        let hs: Vec<_> = (0..n).step_by(chunk).map(|a| { let f = &f; sc.spawn(move || (a..(a + chunk).min(n)).map(f).collect::<Vec<T>>()) }).collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    })
}

pub fn cover(w: &World) -> Cover {
    let per = par_range(w.boxes.len(), |k| {
        let b = &w.boxes[k];
        if b.pn == 0 {
            return vec![[b.x0, b.y0, b.x1, b.y1, b.z0, b.z1]];
        }
        let (a, st) = cover_poly(w.footprint(b));
        st.into_iter().map(|(p, q, m, n)| if a == 0 { [p, m, q, n, b.z0, b.z1] } else { [m, p, n, q, b.z0, b.z1] }).collect()
    });
    let mut c = Cover { boxes: Vec::new(), of: Vec::new() };
    for (k, bs) in per.into_iter().enumerate() {
        c.of.extend(std::iter::repeat_n(k as u32, bs.len()));
        c.boxes.extend(bs);
    }
    c
}

/// Do `boxes` contain the prism `poly × [z0, z1]`: they tile its range along one axis, each holding its part there?
pub fn covers(poly: &[[f64; 2]], z0: f64, z1: f64, boxes: &[[f64; 6]]) -> bool {
    if boxes.is_empty() || !boxes.iter().all(|b| b[4] <= z0 && b[5] >= z1) {
        return false;
    }
    (0..2).any(|a| {
        let mut r: Vec<(f64, f64, f64, f64)> = boxes.iter().map(|b| (b[a], b[a + 2], b[1 - a], b[3 - a])).collect();
        r.sort_by(|p, q| p.0.partial_cmp(&q.0).unwrap());
        let lo = poly.iter().map(|p| p[a]).fold(f64::INFINITY, f64::min);
        let hi = poly.iter().map(|p| p[a]).fold(f64::NEG_INFINITY, f64::max);
        if r[0].0 > lo || r.windows(2).any(|w| w[1].0 > w[0].1) || r.iter().map(|s| s.1).fold(f64::NEG_INFINITY, f64::max) < hi {
            return false;
        }
        r.iter().all(|&(p, q, m, n)| match slab(poly, a, p, q) {
            None => true,
            Some((s, t)) => m <= s && t <= n,
        })
    })
}
