"""Two probes reported in the document (section "Results"):
(a) local contraction of the one-second map at a single altitude, sampled at small radii in Q_N (eps = 1e-4);
(b) settling of real straight escapes from escape-like starts: first time the state is within a box around the
    reference climb (|dV| <= 0.5 m/s, |d climb| <= 0.5 m/s, |d phi| <= 0.02 rad, |d psi| <= 0.02 rad, plus the
    integrators |d ia|, |d ib|, |d iphi| <= 0.02), and the largest later excursion from c(h) over 60 s.
"""
import pickle, sys
import numpy as np
from tsmap import TsMap, NY, NAMES
from trim import SCALE
import ref as refmod
from nstep import EN, c_of

def say(*a):
    print(*a); sys.stdout.flush()

QN = pickle.load(open("/tmp/ts_QN_0.0001.pkl", "rb"))["QN"]
qn = lambda z: float(np.sqrt(z @ QN @ z))
LTi = np.linalg.inv(np.linalg.cholesky(QN).T)
rng = np.random.default_rng(11)
dirs = []
for _ in range(40):
    w = rng.normal(size=NY); w /= np.linalg.norm(w); dirs.append(LTi @ w)
dirs += [-d for d in dirs]
say("(a) one-second map, Q_N (eps 1e-4): max ||E_N(xi) - E_N(0)||_QN / ||xi||_QN")
for h in (600.0, 900.0, 300.0):
    e0, _, _, _ = EN(h, [np.zeros(NY)])
    for r in (1e-4, 1e-3, 1e-2, 3e-2, 1e-1):
        e, _, _, _ = EN(h, [r * d for d in dirs])
        say(f"  h {h:5.0f} r {r:7.4f}: {max(qn(x - e0[0]) for x in e) / r:.4f}")
Qi = np.linalg.inv(QN)
say("  half-widths of {||xi||_QN <= 0.01}:", {NAMES[i]: round(0.01 * float(np.sqrt(Qi[i, i]) * SCALE[i]), 5) for i in (0, 1, 2, 3, 4, 5, 27, 29, 30, 31)})

say("(b) settling of real straight escapes")
ref = refmod.load()
m = TsMap()
idx = [NAMES.index(n) for n in ("v_al", "v_dn", "phi", "dpsi", "ia", "ib", "iphi")]
tol = np.array([0.5, 0.5, 0.02, 0.02, 0.02, 0.02, 0.02])
res = []
for v0 in (25.0, 35.0, 45.0, 60.0):
    for g0 in (-0.35, -0.15, 0.0, 0.2):
        for ph in (0.0, 0.6, 1.1):
            rows = m.run(0, 0, 150.0, v0, g0, np.pi / 2, ph, 1, 1, 128 * 60, 4)
            t_in = None; later = 0.0
            for row in rows:
                if row[1] == 0 or not (10 <= row[4] <= ref["h"][-1]):
                    continue
                d = np.abs(row[5:] - c_of(row[4]))[idx] / tol
                if t_in is None and d.max() <= 1:
                    t_in = row[0] / 128
                elif t_in is not None:
                    later = max(later, d.max())
            res.append((v0, g0, ph, t_in, later, rows[:, 4].min()))
            say(f"  v {v0:4.0f} gam {g0:5.2f} phi {ph:3.1f}: in box at {t_in} s; later max excursion / box {later:.2f}; min h {rows[:, 4].min():.1f}")
ent = [x[3] for x in res if x[3] is not None]
say(f"  {len(res)} starts, {len(ent)} settled within 60 s, {sum(t <= 16 for t in ent)} within 16 s; "
    f"median {np.median(ent):.1f} s, max {max(ent):.1f} s")
pickle.dump(res, open("/tmp/ts_probe.pkl", "wb"))
