//! The bandit's fly brain: a FlyGM-style network (Wang et al., "Whole-Brain Connectomic Graph Model Enables
//! Whole-Body Locomotion Control in Fruit Fly", arXiv 2602.17997) on the fly's visual pursuit pathway cut out of
//! the FlyWire v783 connectome (`flybrain/build_graph.py`): LC10 visual projection neurons in, central neurons
//! (mostly anterior optic tubercle) in the middle, descending neurons out. The wiring and the signed synapse
//! weights are the connectome's and stay fixed; the per-neuron descriptors, the shared neuron update, the
//! afferent gate, the proprioception encoder and the decoder were fine-tuned to imitate `combat::pursuit_law`
//! (`flybrain/train.py`).
//!
//! Vision is a retina of the LC10s' receptive fields (`flybrain/retina.py`): each LC10 responds to the target
//! falling in its field (a Gaussian in angle, widened by the target's apparent size), to how fast that response
//! changes (motion), and to the target's apparent size (range). Each tick, from a zero state, `K` rounds of:
//! every LC10 is gated from its own state, its retinal response and the encoded proprioception; every neuron sums
//! its synaptic inputs; a shared MLP conditioned on the neuron's descriptor updates it. The descending neurons'
//! states are decoded into bank, flight path, throttle and a fire logit.

use crate::combat::{NACT, NOBS};

/// Neuron state channels, update-MLP width, retinal channels per LC10 and proprioceptive inputs.
const C: usize = 16;
const HF: usize = 32;
const NR: usize = 3;
const NOWN: usize = 4;
/// Retina scalings (`flybrain/train.py` uses the same): motion channel gain (on the response's rate of change,
/// 1/s), and the log apparent radius that reads as zero size.
const RET_MOTION: f32 = 0.3;
const LN_RHO0: f32 = -5.3;

pub struct Brain {
    pub n: usize,
    pub n_aff: usize,
    pub n_eff: usize,
    k: usize,
    own_mean: [f32; NOWN],
    own_std: [f32; NOWN],
    enc1: Lin,
    enc2: Lin,
    gate_b: [f32; C],
    /// Transposed (input-major) weights for the per-neuron loops: the gate's state, proprioception and retina
    /// parts, the update MLP's synaptic-input half and second layer; per neuron, the first layer's descriptor
    /// half plus bias.
    gate_ht: Vec<[f32; C]>,
    gate_xt: Vec<[f32; C]>,
    gate_rt: Vec<[f32; C]>,
    f1_mt: Vec<[f32; HF]>,
    f1_bias: Vec<[f32; HF]>,
    f2_t: Vec<[f32; C]>,
    f2_b: [f32; C],
    /// Output-major copies for the backward pass (rows are axpy'd, so it vectorises).
    f2_rows: Vec<[f32; HF]>,
    f1_m_rows: Vec<[f32; C]>,
    gate_h_rows: Vec<[f32; C]>,
    gate_r_rows: Vec<[f32; NR]>,
    dec1: Lin,
    dec2: Lin,
    act_mean: Vec<f32>,
    act_std: Vec<f32>,
    /// LC10 receptive fields: centre (body frame: forward, left, up) and width^2 [rad^2].
    pub rf_c: Vec<[f32; 3]>,
    pub rf_s2: Vec<f32>,
    src: Vec<u32>,
    dst: Vec<u32>,
    w: Vec<f32>,
    h: Vec<[f32; C]>,
    m: Vec<[f32; C]>,
    /// The retina's last responses, per LC10: in field, motion, size.
    pub ret: Vec<[f32; NR]>,
    /// Firing, per neuron: how far its state moved from its running baseline (`ema`), jumping up at once and
    /// fading over about 0.2 s, for the GUI's panel.
    pub activity: Vec<f32>,
    ema: Vec<[f32; C]>,
    primed: bool,
    /// The last decision (bank, flight path, throttle, fire).
    pub last: [f64; NACT],
    /// Where each neuron sits in the brain, and wiring to draw (`flybrain/layout.py`), if exported.
    pub layout: Option<Layout>,
    /// Saliency (GUI only, off by default): per LC10, how strongly its input moves bank, flight path and the fire
    /// logit (gradient magnitudes, each output scaled to its largest), one output refreshed every ten ticks.
    pub saliency_on: bool,
    pub saliency: Vec<f32>,
    sal_parts: [Vec<f32>; 3],
    ticks: u64,
    tape: Tape,
}

/// What the backward pass needs from the forward one, per round: the state after the gate, the update MLP's
/// hidden layer and its output; and the decoder's hidden layer.
#[derive(Default)]
struct Tape {
    hp: Vec<Vec<[f32; C]>>,
    hid: Vec<Vec<[f32; HF]>>,
    hout: Vec<Vec<[f32; C]>>,
    d1: Vec<f32>,
}

/// Front view of the neurons (µm, y ventral) and the strongest connections, for drawing.
pub struct Layout {
    pub pos: Vec<[f32; 2]>,
    pub edges: Vec<(u32, u32, f32)>,
    pub lo: [f32; 2],
    pub hi: [f32; 2],
}

pub const LAYOUT_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/assets/flybrain_layout.bin");

impl Layout {
    fn from_bytes(b: &[u8], n: usize) -> Option<Layout> {
        let mut r = Reader(b.strip_prefix(b"FLYL")?);
        if r.u32()? as usize != n {
            return None;
        }
        let xy = r.f32s(2 * n)?;
        let pos: Vec<[f32; 2]> = xy.chunks_exact(2).map(|p| [p[0], p[1]]).collect();
        let m = r.u32()? as usize;
        let mut edges = Vec::with_capacity(m);
        for _ in 0..m {
            let (s, d, w) = (r.u32()?, r.u32()?, f32::from_bits(r.u32()?));
            if s as usize >= n || d as usize >= n {
                return None;
            }
            edges.push((s, d, w));
        }
        let lo = [pos.iter().map(|p| p[0]).fold(f32::MAX, f32::min), pos.iter().map(|p| p[1]).fold(f32::MAX, f32::min)];
        let hi = [pos.iter().map(|p| p[0]).fold(f32::MIN, f32::max), pos.iter().map(|p| p[1]).fold(f32::MIN, f32::max)];
        Some(Layout { pos, edges, lo, hi })
    }
}

/// A linear layer, PyTorch layout: `w` is out × in, row-major.
struct Lin {
    w: Vec<f32>,
    b: Vec<f32>,
    n_in: usize,
}

impl Lin {
    fn apply(&self, x: &[f32], y: &mut [f32]) {
        for (o, yo) in y.iter_mut().enumerate() {
            let row = &self.w[o * self.n_in..(o + 1) * self.n_in];
            // Eight partial sums, so the reduction vectorises.
            let mut acc = [0.0f32; 8];
            for (rc, xc) in row.chunks(8).zip(x.chunks(8)) {
                for i in 0..rc.len() {
                    acc[i] += rc[i] * xc[i];
                }
            }
            *yo = self.b[o] + acc.iter().sum::<f32>();
        }
    }
}

/// tanh as a (7, 6) Padé approximant, clamped: within 2e-6 of tanh, branch-free so it vectorises.
#[inline(always)]
fn tanh(x: f32) -> f32 {
    let x = x.clamp(-4.97, 4.97);
    let x2 = x * x;
    let p = x * (135135.0 + x2 * (17325.0 + x2 * (378.0 + x2)));
    let q = 135135.0 + x2 * (62370.0 + x2 * (3150.0 + 28.0 * x2));
    (p / q).clamp(-1.0, 1.0)
}

struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn u32(&mut self) -> Option<u32> {
        let (a, rest) = self.0.split_at_checked(4)?;
        self.0 = rest;
        Some(u32::from_le_bytes(a.try_into().ok()?))
    }
    fn f32s(&mut self, n: usize) -> Option<Vec<f32>> {
        let (a, rest) = self.0.split_at_checked(4 * n)?;
        self.0 = rest;
        Some(a.chunks_exact(4).map(|c| f32::from_le_bytes(c.try_into().unwrap())).collect())
    }
    fn u32s(&mut self, n: usize) -> Option<Vec<u32>> {
        let (a, rest) = self.0.split_at_checked(4 * n)?;
        self.0 = rest;
        Some(a.chunks_exact(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect())
    }
    fn lin(&mut self, n_out: usize, n_in: usize) -> Option<Lin> {
        Some(Lin { w: self.f32s(n_out * n_in)?, b: self.f32s(n_out)?, n_in })
    }
}

/// Where the trained brain lives (`flybrain/train.py` writes it).
pub const DEFAULT_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/assets/flybrain.bin");

/// The LC10 responses to a target seen in direction `t` (unit, body frame), moving across the field at `t_dot`
/// [1/s], with log apparent radius `ln_rho`: in field, motion, size.
pub fn retina(c: &[f32; 3], s2: f32, t: &[f32; 3], t_dot: &[f32; 3], ln_rho: f32) -> [f32; NR] {
    let den = s2 + (2.0 * ln_rho).exp();
    let g = 1.0 - (c[0] * t[0] + c[1] * t[1] + c[2] * t[2]);
    let r = (-g / den).exp();
    let motion = tanh(r * (c[0] * t_dot[0] + c[1] * t_dot[1] + c[2] * t_dot[2]) / den * RET_MOTION);
    [r, motion, r * (ln_rho - LN_RHO0) * 0.5]
}

impl Brain {
    /// The trained brain, with its layout if that was exported too.
    pub fn load_default() -> Option<Brain> {
        let mut b = Brain::from_bytes(&std::fs::read(DEFAULT_PATH).ok()?)?;
        b.layout = std::fs::read(LAYOUT_PATH).ok().and_then(|l| Layout::from_bytes(&l, b.n));
        Some(b)
    }

    /// Parse `train.py`'s export: magic, dimensions, then the arrays in the order below (little endian).
    pub fn from_bytes(b: &[u8]) -> Option<Brain> {
        let mut r = Reader(b.strip_prefix(b"FLYB")?);
        let version = r.u32()?;
        let [n, n_aff, n_eff, c, k, n_obs, n_own, n_act, h_enc, hf, h_dec, n_edges] = std::array::from_fn(|_| r.u32().unwrap_or(0) as usize);
        if version != 2 || n_obs != NOBS || n_own != NOWN || n_act != NACT || n == 0 || c != C || hf != HF {
            return None;
        }
        let own_mean = r.f32s(NOWN)?.try_into().ok()?;
        let own_std = r.f32s(NOWN)?.try_into().ok()?;
        let enc1 = r.lin(h_enc, NOWN)?;
        let enc2 = r.lin(C, h_enc)?;
        let gate = r.lin(C, 2 * C + NR)?;
        let eta = r.f32s(n * C)?;
        let f1 = r.lin(HF, 2 * C)?;
        let f2 = r.lin(C, HF)?;
        let dec1 = r.lin(h_dec, n_eff * C)?;
        let dec2 = r.lin(n_act, h_dec)?;
        let act_mean = r.f32s(n_act)?;
        let act_std = r.f32s(n_act)?;
        let rf_c: Vec<[f32; 3]> = r.f32s(3 * n_aff)?.chunks_exact(3).map(|p| [p[0], p[1], p[2]]).collect();
        let rf_s2 = r.f32s(n_aff)?;
        let src = r.u32s(n_edges)?;
        let dst = r.u32s(n_edges)?;
        let w = r.f32s(n_edges)?;
        if !r.0.is_empty() || src.iter().chain(&dst).any(|&i| i as usize >= n) {
            return None;
        }
        let gi = 2 * C + NR;
        let col = |w: &[f32], off: usize, j: usize| -> [f32; C] { std::array::from_fn(|o| w[o * gi + off + j]) };
        // f1([m, eta_v]) = W_m m + (W_eta eta_v + b): precompute the second part per neuron.
        let f1_mt: Vec<[f32; HF]> = (0..C).map(|j| std::array::from_fn(|o| f1.w[o * 2 * C + j])).collect();
        let f1_bias: Vec<[f32; HF]> = (0..n)
            .map(|v| std::array::from_fn(|o| f1.b[o] + (0..C).map(|j| f1.w[o * 2 * C + C + j] * eta[v * C + j]).sum::<f32>()))
            .collect();
        Some(Brain {
            n,
            n_aff,
            n_eff,
            k,
            own_mean,
            own_std,
            enc1,
            enc2,
            gate_b: std::array::from_fn(|o| gate.b[o]),
            gate_ht: (0..C).map(|j| col(&gate.w, 0, j)).collect(),
            gate_xt: (0..C).map(|j| col(&gate.w, C, j)).collect(),
            gate_rt: (0..NR).map(|j| col(&gate.w, 2 * C, j)).collect(),
            f1_mt,
            f1_bias,
            f2_t: (0..HF).map(|j| std::array::from_fn(|o| f2.w[o * HF + j])).collect(),
            f2_b: std::array::from_fn(|o| f2.b[o]),
            f2_rows: (0..C).map(|o| std::array::from_fn(|j| f2.w[o * HF + j])).collect(),
            f1_m_rows: (0..HF).map(|o| std::array::from_fn(|j| f1.w[o * 2 * C + j])).collect(),
            gate_h_rows: (0..C).map(|o| std::array::from_fn(|j| gate.w[o * gi + j])).collect(),
            gate_r_rows: (0..C).map(|o| std::array::from_fn(|j| gate.w[o * gi + 2 * C + j])).collect(),
            dec1,
            dec2,
            act_mean,
            act_std,
            rf_c,
            rf_s2,
            src,
            dst,
            w,
            h: vec![[0.0; C]; n],
            m: vec![[0.0; C]; n],
            ret: vec![[0.0; NR]; n_aff],
            activity: vec![0.0; n],
            ema: vec![[0.0; C]; n],
            primed: false,
            last: [0.0; NACT],
            layout: None,
            saliency_on: false,
            saliency: vec![0.0; n_aff],
            sal_parts: std::array::from_fn(|_| vec![0.0; n_aff]),
            ticks: 0,
            tape: Tape::default(),
        })
    }

    pub fn n_edges(&self) -> usize {
        self.w.len()
    }

    /// One decision: bank and flight-path references [rad], throttle, and fire (1) or hold (0).
    pub fn act(&mut self, obs: &[f32; NOBS]) -> [f64; NACT] {
        self.ticks += 1;
        // Saliency: one output's gradient every ten ticks, in turn (each refreshes every 0.6 s).
        let sal_out = (self.saliency_on && self.ticks % 10 == 0).then(|| [0usize, 1, 3][(self.ticks / 10 % 3) as usize]);
        self.run(obs, sal_out)
    }

    /// Per LC10, the summed magnitude of decoder output `o`'s gradient with respect to its three retinal inputs
    /// (normalised output units; 3 is the fire logit), for checking against PyTorch.
    pub fn grad_magnitudes(&mut self, obs: &[f32; NOBS], o: usize) -> Vec<f32> {
        self.run(obs, Some(o));
        self.input_grad(o).iter().map(|r| r.iter().map(|x| x.abs()).sum()).collect()
    }

    fn run(&mut self, obs: &[f32; NOBS], sal_out: Option<usize>) -> [f64; NACT] {
        let keep = sal_out.is_some();
        let n = self.n;
        let t = [obs[0], obs[1], obs[2]];
        let t_dot = [obs[3], obs[4], obs[5]];
        for a in 0..self.n_aff {
            self.ret[a] = retina(&self.rf_c[a], self.rf_s2[a], &t, &t_dot, obs[6]);
        }
        let own: [f32; NOWN] = std::array::from_fn(|i| (obs[7 + i] - self.own_mean[i]) / self.own_std[i]);
        let mut e1 = vec![0.0; self.enc1.b.len()];
        self.enc1.apply(&own, &mut e1);
        e1.iter_mut().for_each(|v| *v = tanh(*v));
        let mut x = [0.0f32; C];
        self.enc2.apply(&e1, &mut x);
        // The gate's proprioception part is the same for every afferent and every round.
        let mut gx = self.gate_b;
        for j in 0..C {
            for o in 0..C {
                gx[o] += x[j] * self.gate_xt[j][o];
            }
        }
        if keep {
            self.tape.hp.clear();
            self.tape.hid.clear();
            self.tape.hout.clear();
        }
        self.h.fill([0.0; C]);
        for _ in 0..self.k {
            for a in 0..self.n_aff {
                let (ha, ra) = (self.h[a], self.ret[a]);
                let mut y = gx;
                for j in 0..C {
                    for o in 0..C {
                        y[o] += ha[j] * self.gate_ht[j][o];
                    }
                }
                for j in 0..NR {
                    for o in 0..C {
                        y[o] += ra[j] * self.gate_rt[j][o];
                    }
                }
                self.h[a] = y.map(tanh);
            }
            if keep {
                self.tape.hp.push(self.h.clone());
            }
            self.m.fill([0.0; C]);
            for e in 0..self.w.len() {
                let (hs, w) = (self.h[self.src[e] as usize], self.w[e]);
                let md = &mut self.m[self.dst[e] as usize];
                for j in 0..C {
                    md[j] += w * hs[j];
                }
            }
            let mut hids = if keep { vec![[0.0; HF]; n] } else { Vec::new() };
            for v in 0..n {
                let mut y = self.f1_bias[v];
                let mv = self.m[v];
                for j in 0..C {
                    for o in 0..HF {
                        y[o] += mv[j] * self.f1_mt[j][o];
                    }
                }
                let y = y.map(tanh);
                if keep {
                    hids[v] = y;
                }
                let mut z = self.f2_b;
                for j in 0..HF {
                    for o in 0..C {
                        z[o] += y[j] * self.f2_t[j][o];
                    }
                }
                self.h[v] = z.map(tanh);
            }
            if keep {
                self.tape.hid.push(hids);
                self.tape.hout.push(self.h.clone());
            }
        }
        if !self.primed {
            self.ema.copy_from_slice(&self.h);
            self.primed = true;
        }
        for v in 0..n {
            let (hv, ev) = (&self.h[v], &mut self.ema[v]);
            let mut d = 0.0;
            for j in 0..C {
                d += (hv[j] - ev[j]).abs();
                ev[j] += 0.05 * (hv[j] - ev[j]);
            }
            self.activity[v] = (d / C as f32).max(self.activity[v] * 0.85);
        }
        let eff: Vec<f32> = self.h[n - self.n_eff..].iter().flatten().copied().collect();
        let mut d1 = vec![0.0; self.dec1.b.len()];
        self.dec1.apply(&eff, &mut d1);
        d1.iter_mut().for_each(|v| *v = tanh(*v));
        let mut out = [0.0f32; NACT];
        self.dec2.apply(&d1, &mut out);
        if let Some(o) = sal_out {
            self.tape.d1 = d1;
            let g = self.input_grad(o);
            let part = [0usize, 1, 3].iter().position(|&p| p == o).unwrap_or(0);
            let mags: Vec<f32> = g.iter().map(|r| r.iter().map(|x| x.abs()).sum()).collect();
            let mx = mags.iter().fold(1e-9f32, |a, &b| a.max(b));
            self.sal_parts[part] = mags.iter().map(|m| m / mx).collect();
            for a in 0..self.n_aff {
                self.saliency[a] = self.sal_parts.iter().map(|p| p[a]).sum::<f32>() / 3.0;
            }
        }
        let a: [f64; NACT] = std::array::from_fn(|i| (out[i] * self.act_std[i] + self.act_mean[i]) as f64);
        // The last output is a fire logit.
        self.last = [a[0], a[1], a[2], (a[3] > 0.0) as u8 as f64];
        self.last
    }

    /// Gradient of decoder output `o` (normalised units; 3 is the fire logit) with respect to every LC10's three
    /// retinal inputs, by reverse mode through the taped forward pass.
    fn input_grad(&self, o: usize) -> Vec<[f32; NR]> {
        let (n, na, c0) = (self.n, self.n_aff, self.n - self.n_eff);
        let hd = self.dec1.b.len();
        let d_pre: Vec<f32> = (0..hd).map(|j| self.dec2.w[o * hd + j] * (1.0 - self.tape.d1[j] * self.tape.d1[j])).collect();
        let mut dh = vec![[0.0f32; C]; n];
        let ni = self.n_eff * C;
        for (j, dp) in d_pre.iter().enumerate() {
            let row = &self.dec1.w[j * ni..(j + 1) * ni];
            for (i, w) in row.iter().enumerate() {
                dh[c0 + i / C][i % C] += dp * w;
            }
        }
        let mut d_ret = vec![[0.0f32; NR]; na];
        let mut dm = vec![[0.0f32; C]; n];
        let mut dhp = vec![[0.0f32; C]; n];
        for k in (0..self.k).rev() {
            let (hp, hid, hout) = (&self.tape.hp[k], &self.tape.hid[k], &self.tape.hout[k]);
            for v in 0..n {
                let dz: [f32; C] = std::array::from_fn(|i| dh[v][i] * (1.0 - hout[v][i] * hout[v][i]));
                let mut dhid = [0.0f32; HF];
                for i in 0..C {
                    for j in 0..HF {
                        dhid[j] += dz[i] * self.f2_rows[i][j];
                    }
                }
                let mut dmv = [0.0f32; C];
                for i in 0..HF {
                    let dp = dhid[i] * (1.0 - hid[v][i] * hid[v][i]);
                    for j in 0..C {
                        dmv[j] += dp * self.f1_m_rows[i][j];
                    }
                }
                dm[v] = dmv;
            }
            dhp.fill([0.0; C]);
            for e in 0..self.w.len() {
                let (s, w) = (self.src[e] as usize, self.w[e]);
                let dd = dm[self.dst[e] as usize];
                for j in 0..C {
                    dhp[s][j] += w * dd[j];
                }
            }
            // Through the gate to the retina and the previous round's afferent states; other neurons pass through.
            dh.copy_from_slice(&dhp);
            for a in 0..na {
                let dy: [f32; C] = std::array::from_fn(|i| dhp[a][i] * (1.0 - hp[a][i] * hp[a][i]));
                let (mut dr, mut dha) = ([0.0f32; NR], [0.0f32; C]);
                for i in 0..C {
                    for j in 0..NR {
                        dr[j] += dy[i] * self.gate_r_rows[i][j];
                    }
                    for j in 0..C {
                        dha[j] += dy[i] * self.gate_h_rows[i][j];
                    }
                }
                for j in 0..NR {
                    d_ret[a][j] += dr[j];
                }
                dh[a] = dha;
            }
        }
        d_ret
    }

    /// No decision this tick (no fly in the air): let the firing fade.
    pub fn rest(&mut self) {
        self.activity.iter_mut().for_each(|a| *a *= 0.85);
    }
}
