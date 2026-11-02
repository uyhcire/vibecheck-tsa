"""The alpha breakpoints as kinks: one-sided Jacobians across CL's breakpoint at alpha = 0.09 (trim at 550 m, alpha
0.09003) and CD's at 0.0873 (trim at 375 m), the rank of the jump and its small-gain value, as for the |beta| kink."""
import sys
import numpy as np
from tsmap import TsMap, NY, NAMES
from trim import trim, jacobian, SCALE
import ref as refmod

DT = 1.0 / 128
ref = refmod.load()
m = TsMap(); m.smooth(True)
ith, iv = NAMES.index("theta"), NAMES.index("v_rt")
for h, a_bp, name in ((550.0, 0.09, "CLwbh"), (375.0, 0.0873, "CDwbh")):
    y, _ = trim(m, h, refmod.c_of(ref, h))
    a0 = m.diag(h, y)["alpha"]
    J = {}
    for sgn in (1, -1):
        yy = y.copy(); yy[ith] += (a_bp - a0) + sgn * 5e-4      # alpha 5e-4 above / below the breakpoint
        offb = np.zeros(NY); offb[iv] = 1e-3
        J[sgn] = sum(np.diag(1 / SCALE) @ jacobian(m, h, yy + s * offb, 1e-6) @ np.diag(SCALE) for s in (1, -1)) / 2
        J[sgn + 0] = J[sgn]
        print(f"{name} h {h:.0f}: alpha {m.diag(h, yy)['alpha']:.5f}  slow rate {-np.log(max(abs(np.linalg.eigvals(J[sgn])))) / DT:.4f} 1/s")
    U, s, Vt = np.linalg.svd(J[1] - J[-1])
    u, v = U[:, 0] * s[0], Vt[0]
    A0 = (J[1] + J[-1]) / 2
    mu = max(abs(np.linalg.eigvals(A0))) + 3e-4
    w = np.concatenate([np.linspace(0, 0.02, 2000), np.linspace(0.02, np.pi, 2000)])
    g = max(abs(v @ np.linalg.solve(np.exp(1j * om) * np.eye(NY) - A0 / mu, u / mu)) for om in w)
    print(f"  jump singular values {np.round(s[:3], 4)}; v (cols) {[NAMES[k] for k in np.argsort(-abs(v))[:3]]}; "
          f"u (rows) {[NAMES[k] for k in np.argsort(-abs(u))[:3]]}; small gain at mu {mu:.5f}: {g / 2:.3f}")
    sys.stdout.flush()
