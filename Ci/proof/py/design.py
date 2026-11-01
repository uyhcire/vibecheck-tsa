import numpy as np
from pf import *
from lin import ZI, STEP, jac
t5 = np.load("traj_5.npy"); ttop = np.load("traj_top.npy"); tab = np.load("traj_above.npy")
# manifold samples (raw rows), increasing h
segs = [t5[300:]]
segs = [t5[300:][t5[300:,1] < 2400*65536], ttop[ttop[:,1] >= 2400*65536][:6000], tab[1000:][::-1]]
M = np.concatenate(segs)
M = M[np.argsort(M[:,1], kind="stable")]
np.save("manifold.npy", M)
def xstar(h):
    """manifold state (float raw) at altitude h (m), linear interpolation"""
    hs = M[:,1] / 65536
    return np.array([np.interp(h, hs, M[:,j]) for j in range(21)])
def nearest(h):
    hs = M[:,1] / 65536; k = np.argmin(abs(hs-h)); return M[k].copy()
def realjordan(J):
    ev, V = np.linalg.eig(J)
    order = np.argsort(-abs(ev)); ev = ev[order]; V = V[:, order]
    cols = []; lam = []; done = set()
    for i, e in enumerate(ev):
        if i in done: continue
        if abs(e.imag) > 1e-9:
            j = [k for k in range(len(ev)) if k not in done and k != i and abs(ev[k] - e.conj()) < 1e-9][0]
            cols += [V[:, i].real, V[:, i].imag]; done |= {i, j}; lam += [e, e]
        else:
            cols.append(V[:, i].real); done.add(i); lam.append(e)
    return np.array(cols).T, lam
if __name__ == "__main__":
    print("manifold rows", len(M), "h range", M[0,1]/65536, M[-1,1]/65536)
    Js = {}
    for h in [100, 500, 1000, 1500, 2000, 2400, 2500, 2550, 2600, 2619, 2650, 2700]:
        J, dh = jac(nearest(h)); Js[h] = J
        ev = np.linalg.eigvals(J); ev = ev[np.argsort(-abs(ev))]
        print(f"h {h}:", " ".join(f"{abs(e):.4f}{'c%.3f' % abs(np.angle(e)) if abs(e.imag)>1e-9 else ''}" for e in ev[:8]))
    np.save("Js.npy", np.array([Js[h] for h in sorted(Js)])); np.save("Jh.npy", np.array(sorted(Js)))
