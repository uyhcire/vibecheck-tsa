//! The Golden Gate Bridge, described once for the renderer and the collision world, so what is drawn is
//! what the filter avoids. Towers are OpenStreetMap's tower parts (both towers agree to 5 cm); the deck,
//! cables, suspenders, anchorage pylons, the Fort Point arch and the San Francisco approach follow the
//! published dimensions (1,280 m main span, 343 m side spans, 227 m towers, 67 m clearance).
//!
//! Positions are `s` metres along the axis from the south tower centre and `a` metres across it (left of
//! the axis positive), heights NAVD88 metres.

use crate::world::SF_WATER;

/// South tower centre (map metres), and the unit vector from it to the north tower.
pub const S: [f64; 2] = [-6432.1, 2515.1];
pub const U: [f64; 2] = [-0.09788, 0.99520];
/// Main and side spans (m).
pub const MAIN: f64 = 1280.1;
pub const SIDE: f64 = 343.0;
/// Deck extent along the axis: the San Francisco approach to the north abutment.
pub const DECK: (f64, f64) = (-676.0, 1660.0);
/// One tower's parts from OpenStreetMap: centre and half-size across the bridge, centre and half-size along
/// it, bottom and top above the water (m).
pub const TOWER: [[f64; 6]; 18] = [
    [-13.75, 4.81, -0.01, 7.82, 13.0, 21.0],
    [13.72, 4.81, -0.03, 7.82, 13.0, 21.0],
    [-13.74, 3.77, 0.01, 6.91, 21.0, 74.0],
    [13.73, 3.77, -0.01, 6.91, 21.0, 74.0],
    [-0.01, 9.98, -0.01, 1.88, 24.0, 26.0],
    [-0.01, 9.98, -0.01, 1.88, 50.0, 52.0],
    [-13.74, 3.77, 0.01, 5.84, 74.0, 123.0],
    [13.73, 3.77, -0.01, 5.84, 74.0, 123.0],
    [-0.01, 9.98, -0.01, 1.88, 111.0, 121.0],
    [-13.74, 3.77, 0.02, 4.89, 123.0, 162.0],
    [13.73, 3.77, 0.01, 4.89, 123.0, 162.0],
    [-0.01, 9.98, -0.01, 1.88, 151.0, 161.0],
    [-13.72, 2.69, 0.02, 4.89, 162.0, 195.0],
    [13.74, 2.69, 0.01, 4.89, 162.0, 195.0],
    [0.01, 11.04, -0.01, 1.87, 185.0, 193.0],
    [-13.73, 1.62, 0.02, 3.74, 195.0, 225.0],
    [13.74, 1.62, 0.00, 3.74, 195.0, 225.0],
    [-0.01, 12.13, -0.01, 1.86, 215.0, 223.0],
];
/// Concrete pier under each tower: half-size along and across, top above the water.
pub const PIER: (f64, f64, f64) = (16.0, 24.0, 13.0);
/// Cable planes across the axis, main-cable radius, suspender radius and spacing (50 ft), all m.
pub const CABLE: f64 = 13.73;
pub const CABLE_R: f64 = 0.6;
pub const SUSP_R: f64 = 0.15;
pub const SUSP: f64 = 15.24;
/// Railing height above the roadway (m).
pub const RAIL: f64 = 1.2;
/// Concrete blocks reaching from the ground to 10 m above the roadway: (s centre, half along, half across)
/// for the south anchorage pylon, the north anchorage and the pylon south of the Fort Point arch.
pub const PYLONS: [(f64, f64, f64); 3] = [(-SIDE + 4.0, 20.0, 25.0), (MAIN + SIDE, 22.0, 26.0), (-459.0, 6.0, 16.0)];
/// The Fort Point arch under the deck: from, to (along) and the ribs' offset across (m).
pub const ARCH: (f64, f64, f64) = (-453.0, -359.0, 10.0);
pub const ARCH_R: f64 = 1.4;
/// San Francisco approach piers: first one, spacing, last one before the arch (along, m), half-sizes.
pub const APPROACH_PIERS: (f64, f64, f64) = (DECK.0 + 20.0, 45.0, -469.0);
pub const APPROACH_PIER: (f64, f64) = (2.0, 9.0);

/// Point `s` along the axis and `a` across it.
pub fn at(s: f64, a: f64) -> [f64; 2] {
    [S[0] + U[0] * s - U[1] * a, S[1] + U[1] * s + U[0] * a]
}

/// Is `s` on the suspended spans (anchorage to anchorage)?
pub fn suspended(s: f64) -> bool {
    (-SIDE..=MAIN + SIDE).contains(&s)
}

/// Deck half-width and depth below the roadway at `s`: the stiffening truss on the suspended spans, a
/// shallower girder on the approaches.
pub fn deck_section(s: f64) -> (f64, f64) {
    if suspended(s) {
        (CABLE + 0.5, 7.6)
    } else {
        (12.0, 4.0)
    }
}

/// Roadway height at `s`: cambered from 70 m at the towers to 75 m mid-span (67 m clearance below the
/// truss), 66 m at the anchorages, easing down the approaches.
pub fn deck(s: f64) -> f64 {
    let w = SF_WATER;
    if (0.0..=MAIN).contains(&s) {
        let t = (s - 0.5 * MAIN) / (0.5 * MAIN);
        w + 70.0 + 5.0 * (1.0 - t * t)
    } else if s < 0.0 {
        if s >= -SIDE {
            w + 70.0 + 4.0 * s / SIDE
        } else {
            w + 66.0 - 4.0 * (-SIDE - s) / (-SIDE - DECK.0)
        }
    } else {
        let t = s - MAIN;
        if t <= SIDE {
            w + 70.0 - 4.0 * t / SIDE
        } else {
            w + 66.0 - 4.0 * (t - SIDE) / (DECK.1 - MAIN - SIDE)
        }
    }
}

/// Main-cable centre height at `s` (suspended spans): a parabola from the tower tops to just above the deck
/// mid-span, and the side spans sagging down to the anchorages at deck level. Convex on each span, so its
/// maximum over an interval within one span is at an end.
pub fn cable(s: f64) -> f64 {
    let top = SF_WATER + 225.0;
    if (0.0..=MAIN).contains(&s) {
        let t = (s - 0.5 * MAIN) / (0.5 * MAIN);
        let low = deck(0.5 * MAIN) + 1.5;
        low + (top - low) * t * t
    } else {
        let t = if s < 0.0 { (s + SIDE) / SIDE } else { (MAIN + SIDE - s) / SIDE };
        let anchor = deck(if s < 0.0 { -SIDE } else { MAIN + SIDE }) + 2.0;
        anchor + (top - anchor) * t - 12.0 * 4.0 * t * (1.0 - t)
    }
}

/// Stations along the suspended spans every `SUSP`, split at the towers so each interval lies within one
/// span.
pub fn cable_stations() -> Vec<f64> {
    let mut v = Vec::new();
    for (a, b) in [(-SIDE, 0.0), (0.0, MAIN), (MAIN, MAIN + SIDE)] {
        let n = ((b - a) / SUSP).ceil() as usize;
        for k in 0..n {
            v.push(a + (b - a) * k as f64 / n as f64);
        }
    }
    v.push(MAIN + SIDE);
    v
}
