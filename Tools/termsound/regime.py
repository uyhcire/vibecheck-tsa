"""What changes the straight climb's linearisation between 450 and 600 m (docs/termsound-proof.tex, section 5.5).

1. Sweep: frozen trims every 10 m on 300-800 m; per-frame and one-second eigenvalues of the frame map (average of
   the one-sided Jacobians at the |beta| kink), the slowest mode's eigenvector, and every discrete quantity the frame
   reads (table segments, law clamps, flags) from `tsmap D`.
2. Controlled experiment: a constant vertical wind moves the trim's alpha at a fixed altitude; the slowest mode
   follows alpha across the CL table's breakpoint at 0.09 rad (and the CD table's at 0.0873), at any altitude.
"""
import sys
import numpy as np
from tsmap import TsMap, NY, NAMES, DIAG
from trim import trim, jacobian, SCALE
import ref as refmod

DT = 1.0 / 128


def say(*a):
    print(*a); sys.stdout.flush()


def seg(keys, x):
    """Index of the table segment containing x (0: below the first key)."""
    return int(np.searchsorted(keys, x, side="right"))


def kinkfree_jac(m, h, y):
    off = np.zeros(NY); off[NAMES.index("v_rt")] = 1e-3
    return (jacobian(m, h, y + off, 1e-6) + jacobian(m, h, y - off, 1e-6)) / 2


def slow(J):
    ev, V = np.linalg.eig(np.diag(1 / SCALE) @ J @ np.diag(SCALE))
    i = np.argsort(-abs(ev))
    return ev[i], V[:, i]


def describe(m, h, y, keys):
    d = m.diag(h, y)
    J = kinkfree_jac(m, h, y)
    ev, V = slow(J)
    v0 = np.abs(V[:, 0]); v0 /= v0.max()
    dom = [NAMES[k] for k in np.argsort(-v0)[:4]]
    segs = dict(CLwbh=seg(keys["CLwbh"], d["alpha"]), CDwbh=seg(keys["CDwbh"], d["alpha"]),
                CYp=seg(keys["CYp"], d["alpha"]), cThrust=seg(keys["cThrust"], d["J"]),
                cPower=seg(keys["cPower"], d["J"]), CtMach=seg(keys["CtMach"], d["tipMach"]),
                CpMach=seg(keys["CpMach"], d["tipMach"]), mixEff=seg(keys["mixEff"], d["fuel_air"]),
                kCLge=seg(keys["kCLge"], d["h_over_b"]))
    clamps = dict(gc=not (0.05 <= d["gc_raw"] <= 0.35), n=not (0.3 <= d["n_raw"] <= 3.5),
                  amax=d["acmd_raw"] > 0.24, elev=abs(d["elev_raw"]) > 1, ail=abs(d["ail_raw"]) > 1,
                  rud=abs(d["rud_raw"]) > 1, phiT=abs(d["phiT_raw"]) > 0.15, sc=d["sc"] < 1, stall=d["stall"] != 0)
    return d, ev, dom, segs, clamps


if __name__ == "__main__":
    ref = refmod.load()
    m = TsMap(); m.smooth(True)
    keys = m.keys()
    say("== 1. sweep 300-800 m ==")
    say("   h   alpha    J      f/a    | slow rate 1/s (frame)  |ev_1s| x3          | segs CL CD J mix | clamps | slow-mode eigvec top")
    y = refmod.c_of(ref, 300.0)
    rows = []
    prev = None
    for h in np.arange(300.0, 800.1, 10.0):
        y, res = trim(m, h, y)
        d, ev, dom, segs, clamps = describe(m, h, y, keys)
        rate = -np.log(abs(ev[0])) / DT
        e1 = np.sort(abs(ev) ** 128)[::-1][:3]
        act = [k for k, v in clamps.items() if v]
        rows.append((h, d["alpha"], rate, e1, segs, act, dom))
        flips = "" if prev is None else " ".join(f"{k}:{prev[k]}->{v}" for k, v in segs.items() if prev[k] != v)
        prev = segs
        say(f"{h:5.0f} {d['alpha']:.5f} {d['J']:.4f} {d['fuel_air']:.5f} | {rate:.4f} | {np.round(e1, 4)} | "
            f"{segs['CLwbh']} {segs['CDwbh']} {segs['cThrust']} {segs['mixEff']} | {act or '-'} | {dom} {flips}")
    unchanged = [k for k in rows[0][4] if all(r[4][k] == rows[0][4][k] for r in rows)]
    say("segments constant over the sweep:", unchanged, "; clamps active anywhere:", sorted({a for r in rows for a in r[5]}) or "none")

    say("== 2. controlled experiment: vertical wind moves alpha at fixed altitude ==")
    for h in (300.0, 700.0):
        y = refmod.c_of(ref, h)
        for wd in (-6.0, -4.0, -2.0, 0.0, 2.0, 4.0, 6.0):   # ft/s, NED down (negative = updraft)
            m.wind(0.0, 0.0, wd)
            yt, res = trim(m, h, y)
            if np.max(np.abs(res) / SCALE) > 1e-8:
                say(f"  h {h:.0f} wind_down {wd:+.0f} ft/s: trim failed"); continue
            d, ev, dom, segs, clamps = describe(m, h, yt, keys)
            say(f"  h {h:4.0f} wind_down {wd:+5.1f} ft/s: alpha {d['alpha']:.5f}  CL seg {segs['CLwbh']} CD seg {segs['CDwbh']}"
                f"  slow rate {-np.log(abs(ev[0])) / DT:.4f} 1/s  |ev_1s| {abs(ev[0]) ** 128:.4f}")
        m.wind(0.0, 0.0, 0.0)
