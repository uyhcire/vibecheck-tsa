"""The reference climb c(h): the chart of the settled straight escape as it passes altitude h.

The atmosphere model is not defined below sea level (NaN) and the plant's gear touches its sea-level ground near
0 m, so the band starts at 10 m and the reference is seeded there from the frozen trim plus the steady lag measured
on a settled climb near 600 m (y*(10) + c_600 - y*(600); y*(10) by continuation down from 600 m in 50 m steps), and flown
with the real loop (smoothed quaternion) up to 1,400 m; c(h) is the linear interpolation in h of its per-frame
charts, relative to the held track (north). The seed's residual transient is reported (`seed_transient`). Also the frozen trims y*(h) (fixed points with the altitude held), for comparison: c - y* is
the steady lag of the climb behind the altitude-dependent trim.
"""
import pickle
import numpy as np

from tsmap import TsMap, NY, NAMES
from trim import trim, SCALE

H_LO, H_HI = 10.0, 1400.0


def build(path="/tmp/ts_ref.pkl"):
    m = TsMap()
    m.smooth(True)
    pre = m.run(0, 0, 300.0, 40.0, 0.0, np.pi / 2, 0, 1, 1, 128 * 60, 128 * 60)
    h600, y600 = pre[-1][4], pre[-1][5:]
    ys600, _ = trim(m, h600, y600)
    yc = ys600
    for hh in list(np.arange(550.0, 0.0, -50.0)) + [H_LO]:
        yc, _ = trim(m, hh, yc)
    seed = yc + (y600 - ys600)
    rows = m.sim(H_LO, seed, 128 * 330, 1)
    h = rows[:, 3]
    ok = (h <= H_HI + 5)
    i1 = len(ok) - np.argmax(ok[::-1])
    seg = np.column_stack([rows[:i1, 0], np.ones(i1), rows[:i1, 1:]])
    assert np.all(np.diff(seg[:, 4]) > 0), "reference climb not monotone"
    ref = dict(h=seg[:, 4], y=seg[:, 5:], east=seg[:, 2], north=seg[:, 3], frame=seg[:, 0])
    # frozen trims every 50 m
    hs = np.array([H_LO] + list(np.arange(50.0, H_HI + 1, 50.0)))
    ys = []
    yt = yc
    for hh in hs:
        yt, res = trim(m, hh, yt)
        assert np.max(np.abs(res) / SCALE) < 1e-8, ("trim failed", hh)
        ys.append(yt)
    ref["trim_h"] = hs
    ref["trim_y"] = np.array(ys)
    pickle.dump(ref, open(path, "wb"))
    return ref


def c_of(ref, h):
    """c(h) by linear interpolation of the reference charts."""
    return np.array([np.interp(h, ref["h"], ref["y"][:, j]) for j in range(NY)])


def load(path="/tmp/ts_ref.pkl"):
    return pickle.load(open(path, "rb"))


if __name__ == "__main__":
    np.set_printoptions(linewidth=220, precision=6)
    ref = build()
    print("reference samples", len(ref["h"]), "h range", ref["h"][0], ref["h"][-1])
    for hh, yt in zip(ref["trim_h"], ref["trim_y"]):
        c = c_of(ref, hh)
        v = np.hypot(np.hypot(yt[3], yt[4]), yt[5])
        gam = np.arctan2(-yt[5], np.hypot(yt[3], yt[4]))
        print(f"h {hh:6.0f}  V {v:7.3f}  climb {-yt[5]:6.3f} m/s  gamma {gam:.4f}  theta {yt[1]:.4f}  alpha~{yt[1]-gam:.4f}"
              f"  phi {yt[0]:.5f}  track-psiRef {np.arctan2(yt[4], yt[3]):.5f}  rpm {yt[27]:.1f}"
              f"  |c-y*|/SCALE max {np.max(np.abs(c-yt)/SCALE):.4f} ({NAMES[np.argmax(np.abs(c-yt)/SCALE)]})")
