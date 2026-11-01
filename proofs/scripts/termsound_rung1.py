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

# ---------------- simulation ----------------
def sim(kind_, E0, n_frames, seed, scale=1.0):
    rnd = random.Random(seed); fl = float
    u_s = lambda z: fl(ur + E0) - fl(E1) * z
    vz_s = lambda z: fl(v0) + fl(kV) * (fl(E0) - fl(E1) * z)
    hh, gg = fl(h), fl(g)
    z = 300.0; u = u_s(z); vz = vz_s(z); psi = 0.0; x = y = 0.0
    l = fl(lc) if kind_ == "helix" else 0.0
    # start on the boundary-ish of the sets
    u += 0.9 * fl(EU) * rnd.choice([-1, 1]) * 0.5
    worstQ = worstT = 0.0; worstL = 0.0
    z0 = z; x0 = x
    c0 = complex(x, y) + fl(Rs(z)) * 1j * cmath.exp(1j * psi) if kind_ == "helix" else 0
    maxdev = 0.0; ok_ = True
    for k in range(n_frames):
        d = lambda b: fl(b) * scale * rnd.uniform(-1, 1)
        du, dvz, dz, dl, dpsi = d(dU), d(dVZ), d(dZ), d(dL), d(dPSI)
        dp = complex(d(dP), d(dP)) / math.sqrt(2)
        a0 = fl(g / ur) * vz_s(z) + 0  # trim-consistent excess acceleration at z, via the trim identity
        fu = -fl(kD) * (u - u_s(z)) - fl(g / ur) * (vz - vz_s(z))
        fvz = fl(kG) * (fl(v0) + fl(kV) * (u - fl(ur)) - vz)
        if kind_ == "helix":
            om = gg * l / u; R = u * u / (gg * l)
            psin = psi + hh * om
            p = complex(x, y) + R * 1j * (cmath.exp(1j * psi) - cmath.exp(1j * psin)) + dp
            l = l + hh / fl(tau) * (fl(lc) - l) + dl
            psi = psin + dpsi
        else:
            p = complex(x + hh * u * math.cos(psi), y + hh * u * math.sin(psi)) + dp
            lnew = l + hh / fl(tau) * (-fl(kchi) * psi - l) + dl
            psi = psi + hh * gg * l / u + dpsi
            l = lnew
        x, y = p.real, p.imag
        u, vz, z = u + hh * fu + du, vz + hh * fvz + dvz, z + hh * vz + dz
        eu, ev = u - u_s(z), vz - vz_s(z)
        Q = fl(PL[0]) * eu * eu + 2 * fl(PL[1]) * eu * ev + fl(PL[2]) * ev * ev
        worstQ = max(worstQ, Q / fl(r2L))
        if kind_ == "helix":
            worstL = max(worstL, abs(l - fl(lc)) / fl(RL))
            if z < fl(ZT):
                ct = complex(x, y) + fl(Rs(z)) * 1j * cmath.exp(1j * psi)
                maxdev = max(maxdev, abs(ct - c0) / max(1e-9, fl(kap) * (z - z0) + 1e-9) if z > z0 else 0)
        else:
            QT = fl(PT[0]) * psi * psi + 2 * fl(PT[1]) * psi * l + fl(PT[2]) * l * l
            worstT = max(worstT, QT / fl(r2T))
            if z < fl(ZT) and x > x0:
                maxdev = max(maxdev, abs(y) / (fl(kap_y) * (x - x0) + 1e-9), fl(Gr) * (x - x0) / max(z - z0, 1e-9))
    return worstQ, worstT, worstL, maxdev

if "--sim" in sys.argv or True:
    for scale in [1.0, 4.0, 16.0]:
        rs = [sim("ray", Fr(-1, 2), 128 * 120, s, scale) for s in range(4)]
        hs = [sim("helix", Fr(-3, 2), 128 * 120, s, scale) for s in range(4)]
        print(f"scale {scale}: ray max Q/r2 long {max(r[0] for r in rs):.3f} lat {max(r[1] for r in rs):.3f}"
              f" cone usage {max(r[3] for r in rs):.3f} | helix Q/r2 {max(r[0] for r in hs):.3f}"
              f" bank {max(r[2] for r in hs):.3f} centre/cone {max(r[3] for r in hs):.3f}")
