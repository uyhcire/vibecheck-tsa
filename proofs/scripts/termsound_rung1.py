"""TermSound rung 1: parameter design check and random-disturbance simulation.

Mirrors proofs/Proofs/TermSound/{Model,Long,Helix,Ray}.lean. Exact rationals for the side conditions the Lean
proofs discharge with norm_num; floats for the simulation. Run: python3 proofs/scripts/termsound_rung1.py
"""
import cmath, math, random, sys
from fractions import Fraction as Fr

h = Fr(1, 128); g = Fr(49, 5)
# longitudinal law and point-mass parameters
ur, kD, kG, kV, v0, E1 = Fr(35), Fr(1, 20), Fr(5, 2), Fr(7, 10), Fr(21, 4), Fr(7, 4000)
K = kV * E1                                  # d vz*/dz
# Lyapunov forms
PL, r2L, c2L, tL = (Fr(28), Fr(-3), Fr(1)), Fr(1, 4), Fr(9964, 10000), Fr(18, 10000)
PT, r2T, c2T, tT = (Fr(5), Fr(7, 4), Fr(1)), Fr(1, 625), Fr(9944, 10000), Fr(28, 10000)
thN = Fr(3, 10)                             # nominal g/u in the lateral linear part
tau, kchi, lc = Fr(1, 2), Fr(1), Fr(4, 7)   # bank lag, heading gain, tan(bank) of the 30 deg helix
ZT = Fr(1200)                                # highest z_top the end sets are stated for
# disturbance budget (per frame)
dU, dVZ, dZ, dL, dPSI, dP = Fr(5, 10**5), Fr(1, 10**4), Fr(1, 10**4), Fr(1, 10**5), Fr(1, 10**6), Fr(1, 10**4)

def A(F): return (1 + h * F[0][0], h * F[0][1], h * F[1][0], 1 + h * F[1][1])
AL = A([[-kD, -g / ur], [kG * kV, -kG]])
AT = A([[0, thN], [-kchi / tau, -1 / tau]])

def Ms(P, A, c2):
    p11, p12, p22 = P; a11, a12, a21, a22 = A
    m11 = c2 * p11 - (a11 * a11 * p11 + 2 * a11 * a21 * p12 + a21 * a21 * p22)
    m12 = c2 * p12 - (a11 * a12 * p11 + (a11 * a22 + a12 * a21) * p12 + a21 * a22 * p22)
    m22 = c2 * p22 - (a12 * a12 * p11 + 2 * a12 * a22 * p12 + a22 * a22 * p22)
    return m11, m12, m22

def qbox(P, a, b): return P[0] * a * a + 2 * abs(P[1]) * a * b + P[2] * b * b
def ext(P, r2): d = P[0] * P[2] - P[1] ** 2; return (r2 * P[2] / d, r2 * P[0] / d)   # squared extents

ok = True
def check(name, cond):
    global ok
    print(("ok  " if cond else "FAIL"), name); ok &= bool(cond)

for nm, P, AA, c2 in [("long", PL, AL, c2L), ("lat", PT, AT, c2T)]:
    m11, m12, m22 = Ms(P, AA, c2)
    check(f"{nm}: c2 P - A^T P A psd", m11 > 0 and m12 * m12 <= m11 * m22)

eu2, evz2 = ext(PL, r2L); EU, EVZ = Fr(23, 200), Fr(61, 100)     # |e_u| <= EU, |e_vz| <= EVZ
check("long extents", eu2 <= EU ** 2 and evz2 <= EVZ ** 2)
ech2, el2 = ext(PT, r2T); ECH, EL = Fr(3, 100), Fr(13, 200)
check("lat extents", ech2 <= ECH ** 2 and el2 <= EL ** 2)

def kind(name, E0, zcap):
    """Longitudinal block for one end-set kind: u*(z) = ur + E0 - E1 z, vz*(z) = v0 + kV (E0 - E1 z)."""
    vzs = lambda z: v0 + kV * (E0 - E1 * z)
    us = lambda z: ur + E0 - E1 * z
    vzabs = max(abs(vzs(0)), abs(vzs(zcap))) + EVZ
    DZ = h * vzabs + dZ
    K_ = qbox(PL, dU + E1 * DZ, dVZ + K * DZ)
    check(f"{name}: long budget", (1 + tL) * c2L * r2L + (1 + 1 / tL) * K_ <= r2L)
    check(f"{name}: z cap invariant", h * (vzs(zcap) + EVZ) + dZ <= 0)
    vzlo = vzs(ZT) - EVZ
    check(f"{name}: climbs below z_top (vz >= {float(vzlo):.3f})", h * vzlo - dZ > 0)
    print(f"   {name}: u*(0)={float(us(0)):.2f} vz*(0)={float(vzs(0)):.2f} ceiling={float((v0 + kV * E0) / K):.0f} m"
          f" zcap={zcap} DZ={float(DZ):.4g} sqrtK/sqrt(r2)={math.sqrt(float(K_ / r2L)):.3g}")
    return vzs, us, vzlo, DZ

# straight climb (ray)
vzsR, usR, vzloR, DZR = kind("ray", Fr(-1, 2), Fr(4600))
ulo, uhi = usR(ZT) - EU, usR(0) + EU
mis = h * g * EL * max(1 / ulo - thN / g, thN / g - 1 / uhi)            # |h g l (1/u - thN/g)|
KT = qbox(PT, dPSI + mis, dL)
check("ray: lat budget", (1 + tT) * c2T * r2T + (1 + 1 / tT) * KT <= r2T)
dsmin = h * ulo * (1 - ECH ** 2 / 2) - dP
kap_y = (h * uhi * ECH + dP) / dsmin
Gr = (h * vzloR - dZ) / (h * uhi + dP)
print(f"   ray: u in [{float(ulo):.2f},{float(uhi):.2f}] kappa_y={float(kap_y):.4f} gradient G={float(Gr):.4f}")

# 30 deg helix
vzsH, usH, vzloH, DZH = kind("helix", Fr(-3, 2), Fr(4100))
RL = Fr(1, 200)                                 # |l - lc| <= RL
check("helix: bank budget", (1 - h / tau) * RL + dL <= RL)
uloH, uhiH = usH(ZT) - EU, usH(0) + EU
llo, lhi = lc - RL, lc + RL
Rs = lambda z: usH(z) ** 2 / (g * lc)
dR = (2 * uhiH * EU / llo + uhiH ** 2 * RL / (llo * lc)) / g   # |R - R*(z)| bound
omax = g * lhi / uloH
LR = E1 * 2 * uhiH / (g * lc)                               # |dR*/dz|
D0 = dR * h * omax + Rs(0) * dPSI + dP                      # per-frame drift not proportional to climb
dzmin = h * vzloH - dZ
kap = LR + D0 / dzmin
print(f"   helix: R*(0)={float(Rs(0)):.1f} R*(ZT)={float(Rs(ZT)):.1f} |R-R*|<={float(dR):.2f} omega<={float(omax):.4f}"
      f" L_R={float(LR):.4f} kappa={float(kap):.4f}")
print("all side conditions hold" if ok else "SOME CONDITION FAILS")

kapH = Fr(1, 3); kapY = Fr(1, 30); G = Fr(2, 25)        # the constants the Lean statements use
check("helix: kappa covers the drift", kap >= kap - 0 and kapH >= kap)
check("ray: kapY, G cover the corridor", kapY >= kap_y and G <= Gr)


# ---------------- how large can the budget be (proved side conditions, all deltas scaled together) ----------------
def conditions(scale):
    """All side conditions of dynH_robust / dynR_robust with every per-frame budget multiplied by `scale`."""
    sdU, sdVZ, sdZ, sdL, sdPSI, sdP = (x * scale for x in (dU, dVZ, dZ, dL, dPSI, dP))
    DZ = Fr(44, 1000)
    res = {}
    res["long"] = (1 + tL) * c2L * r2L + (1 + 1 / tL) * qbox(PL, sdU + E1 * DZ, sdVZ + K * DZ) <= r2L
    res["DZ"] = h * Fr(551, 100) + sdZ <= DZ
    res["bank"] = (1 - h / tau) * RL + sdL <= RL
    misr = h * g * EL * Fr(17, 1000) / g
    res["lat"] = (1 + tT) * c2T * r2T + (1 + 1 / tT) * qbox(PT, sdPSI + h * EL * Fr(17, 1000), sdL) <= r2T
    dzminH = h * (vzsH(ZT) - EVZ) - sdZ
    res["helix drift"] = Fr(16, 5) * h * Fr(181, 1000) + 201 * sdPSI + 2 * sdP <= (kapH - Fr(21, 1000)) * dzminH
    dxmin = h * (Fr(324, 10) - EU) * (1 - ECH ** 2 / 2) - sdP
    res["ray cone"] = h * (Fr(69, 2) + EU) * ECH + sdP <= kapY * dxmin
    res["ray gradient"] = G * (h * (Fr(69, 2) + EU) + sdP) <= h * (vzsR(ZT) - EVZ) - sdZ
    return res

lo, hi = Fr(1), Fr(1000)
for _ in range(40):
    mid = (lo + hi) / 2
    if all(conditions(mid).values()): lo = mid
    else: hi = mid
binding = [k for k, v in conditions(hi).items() if not v]
print(f"proved budget can be scaled by {float(lo):.3f} before {binding} fails")
for k in ["long", "lat", "bank", "helix drift", "ray cone", "ray gradient"]:
    lo2, hi2 = Fr(0), Fr(1000)
    for _ in range(40):
        mid = (lo2 + hi2) / 2
        if conditions(mid)[k]: lo2 = mid
        else: hi2 = mid
    print(f"   {k:13s} alone allows scale {float(lo2):8.3f}")


# ---------------- simulation: states in Dyn stay in Dyn under random and adversarial disturbances ----------------
F = float
def in_long(E0, u, vz, z):
    eu, ev = u - F(ur + E0 - E1 * z), vz - F(v0 + kV * (E0 - E1 * z))
    return F(PL[0]) * eu * eu + 2 * F(PL[1]) * eu * ev + F(PL[2]) * ev * ev

def sample_ellipse(P, r2, rnd, frac):
    """A point with q = frac * r2."""
    th = rnd.uniform(0, 2 * math.pi); a, b = math.cos(th), math.sin(th)
    qq = F(P[0]) * a * a + 2 * F(P[1]) * a * b + F(P[2]) * b * b
    k = math.sqrt(frac * F(r2) / qq)
    return k * a, k * b

def run(kind_, seconds, seed, scale, mode):
    rnd = random.Random(seed)
    E0 = F(EH if False else (Fr(-3, 2) if kind_ == "helix" else Fr(-1, 2)))
    hh, gg = F(h), F(g)
    us_ = lambda z: F(ur) + E0 - F(E1) * z
    vs_ = lambda z: F(v0) + F(kV) * (E0 - F(E1) * z)
    z0, ztop = 300.0, 1000.0
    eu, ev = sample_ellipse(PL, r2L, rnd, rnd.uniform(0.9, 1.0))
    st = dict(x=0.0, y=0.0, z=z0, psi=0.0, u=us_(z0) + eu, vz=vs_(z0) + ev, l=0.0)
    m0 = 0.0
    if kind_ == "helix":
        st["l"] = F(lc) + F(RL) * rnd.uniform(-1, 1)
        Rs_ = lambda z: us_(z) ** 2 / (gg * F(lc))
        c0 = complex(st["x"], st["y"]) + Rs_(z0) * 1j * cmath.exp(1j * st["psi"])
    else:
        a, b = sample_ellipse(PT, r2T, rnd, rnd.uniform(0.9, 1.0)); st["psi"], st["l"] = a, b
    worst = {}
    def note(k, v): worst[k] = max(worst.get(k, -1e9), v)
    budget = dict(x=F(dP), y=F(dP), z=F(dZ), psi=F(dPSI), u=F(dU), vz=F(dVZ), l=F(dL))
    for k in range(int(seconds * 128)):
        s = st
        # disturbance: uniform, or adversarial (push the Lyapunov functions and the cone outwards)
        if mode == "uniform":
            d = {k_: scale * b * rnd.uniform(-1, 1) for k_, b in budget.items()}
        else:
            eu, ev = s["u"] - us_(s["z"]), s["vz"] - vs_(s["z"])
            gu, gv = F(PL[0]) * eu + F(PL[1]) * ev, F(PL[1]) * eu + F(PL[2]) * ev
            d = {k_: scale * b for k_, b in budget.items()}
            d["u"] *= math.copysign(1, gu); d["vz"] *= math.copysign(1, gv); d["z"] = -d["z"]
            if kind_ == "helix":
                d["l"] *= math.copysign(1, s["l"] - F(lc))
                # pump the centre: speed/bank error that makes R - R* change sign with the heading
                ph = math.cos(s["psi"])
                d["u"] = scale * budget["u"] * math.copysign(1, ph); d["l"] = -scale * budget["l"] * math.copysign(1, ph)
                d["x"], d["y"] = scale * budget["x"], 0.0
            else:
                gp, gl = F(PT[0]) * s["psi"] + F(PT[1]) * s["l"], F(PT[1]) * s["psi"] + F(PT[2]) * s["l"]
                d["psi"] *= math.copysign(1, gp); d["l"] *= math.copysign(1, gl)
                d["y"] = scale * budget["y"]; d["x"] = -scale * budget["x"]
        if kind_ == "helix":
            om = gg * s["l"] / s["u"]; R = s["u"] ** 2 / (gg * s["l"])
            psin = s["psi"] + hh * om
            p = complex(s["x"], s["y"]) + R * 1j * (cmath.exp(1j * s["psi"]) - cmath.exp(1j * psin))
            nl = s["l"] + hh / F(tau) * (F(lc) - s["l"])
        else:
            psin = s["psi"] + hh * gg * s["l"] / s["u"]
            p = complex(s["x"] + hh * s["u"] * math.cos(s["psi"]), s["y"] + hh * s["u"] * math.sin(s["psi"]))
            nl = s["l"] + hh / F(tau) * (-F(kchi) * s["psi"] - s["l"])
        fu = -F(kD) * (s["u"] - us_(s["z"])) - F(g / ur) * (s["vz"] - vs_(s["z"]))
        fvz = F(kG) * (F(v0) + F(kV) * (s["u"] - F(ur)) - s["vz"])
        st = dict(x=p.real + d["x"], y=p.imag + d["y"], z=s["z"] + hh * s["vz"] + d["z"], psi=psin + d["psi"],
                  u=s["u"] + hh * fu + d["u"], vz=s["vz"] + hh * fvz + d["vz"], l=nl + d["l"])
        note("long q/r2", in_long(E0, st["u"], st["vz"], st["z"]) / F(r2L))
        note("z0 - z", z0 - st["z"])
        if st["z"] < ztop:
            if kind_ == "helix":
                note("bank/RL", abs(st["l"] - F(lc)) / F(RL))
                c = complex(st["x"], st["y"]) + Rs_(st["z"]) * 1j * cmath.exp(1j * st["psi"])
                note("centre/cone", abs(c - c0) - (m0 + F(kapH) * (st["z"] - z0)))
            else:
                qt = F(PT[0]) * st["psi"] ** 2 + 2 * F(PT[1]) * st["psi"] * st["l"] + F(PT[2]) * st["l"] ** 2
                note("lat q/r2", qt / F(r2T))
                note("|y|-cone", abs(st["y"]) - (5.0 + F(kapY) * st["x"]))
                note("grad", z0 + F(G) * st["x"] - st["z"])
    return worst

def inside(w):
    return all(v <= 1 for k, v in w.items() if "/" in k) and all(v <= 0 for k, v in w.items() if "/" not in k)

if __name__ == "__main__":
    print("\nsimulation: 4 seeds x 60 s from states sampled at 90-100% of each Lyapunov level")
    for scale in [1, 3, 10, 30, 100]:
        for mode in ["uniform", "adversarial"]:
            for kind_ in ["helix", "ray"]:
                ws = [run(kind_, 60, sd, scale, mode) for sd in range(4)]
                agg = {k: max(w[k] for w in ws) for k in ws[0]}
                print(f"  scale {scale:4d} {mode:11s} {kind_:5s} {'IN ' if all(inside(w) for w in ws) else 'OUT'} "
                      + " ".join(f"{k}={v:.3g}" for k, v in agg.items()))
