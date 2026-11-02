"""Frozen-altitude trims y*(h) of the straight escape and the one-frame Jacobian there.

y*(h) is the fixed point of y -> Phi_y(h, y): place the closed loop at altitude h with local coordinates y, fly
one frame, read the local coordinates back (the altitude change is dropped). Newton on the residual
Phi_y(h, y) - y with a central-difference Jacobian.
"""
import numpy as np

from tsmap import TsMap, NY

# Finite-difference step per coordinate (absolute): about 1e-6 of each coordinate's typical size.
SCALE = np.array([1e-2, 1e-1, 1e-2, 30, 1, 5, 1e-1, 1e-1, 1e-1,
                  3e-4, 3e-4, 3e-4, 3e-4, 3e-4, 3e-4,
                  3e-2, 3e-2, 3e-2, 3e-2, 3e-2, 3e-2,
                  1e-1, 1e-1, 1e-1, 1, 1, 1, 2600, 9e4, 1e-1, 1e-1, 1e-1])


def jacobian(m, h, y, rel=1e-6, psi=0.0, north=0.0):
    """Central differences of y -> Phi_y(h, y): column j uses steps +-rel*SCALE[j]."""
    hs, ys = [], []
    steps = rel * SCALE
    for j in range(NY):
        for sgn in (1, -1):
            yy = y.copy()
            yy[j] += sgn * steps[j]
            hs.append(h)
            ys.append(yy)
    _, out = m.step_many(hs, ys, psi, north)
    J = np.empty((NY, NY))
    for j in range(NY):
        J[:, j] = (out[2 * j] - out[2 * j + 1]) / (2 * steps[j])
    return J


def trim(m, h, y0, iters=8, verbose=False):
    y = y0.copy()
    for it in range(iters):
        _, y1 = m.step(h, y)
        r = y1 - y
        if verbose:
            print(it, np.max(np.abs(r) / SCALE))
        if np.max(np.abs(r) / SCALE) < 1e-14:
            break
        J = jacobian(m, h, y)
        y = y - np.linalg.solve(J - np.eye(NY), r)
    _, y1 = m.step(h, y)
    return y, y1 - y


if __name__ == "__main__":
    np.set_printoptions(linewidth=200, precision=6, suppress=False)
    m = TsMap()
    r = m.run(0, 0, 300, 40, 0, 0, 0, 1, 1, 128 * 60, 128 * 60)
    h0, y0 = r[-1][4], r[-1][5:]
    ys, res = trim(m, h0, y0, verbose=True)
    print("h", h0)
    print("y*", ys)
    print("residual", res)
    print("settled sim minus trim (scaled)", (y0 - ys) / SCALE)
