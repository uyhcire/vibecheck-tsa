"""The trim sits on the |beta| kink (drag term CDbeta = 0.17 |beta|; the rudder integrator drives beta to 0).
One-sided Jacobians A+ (beta > 0) and A- (beta < 0), the rank of the jump, and the small-gain test for a common
quadratic Lyapunov function over the convex hull {A0 + t u v^T : |t| <= 1/2}."""
import numpy as np, pickle
from tsmap import TsMap, NY, NAMES
from trim import SCALE, jacobian
np.set_printoptions(linewidth=200, precision=4)
d = pickle.load(open('/tmp/ts_lin.pkl', 'rb')); h0, ys = d['h0'], d['ys']
m = TsMap(); m.smooth(True)
D = np.diag(SCALE); Di = np.diag(1 / SCALE)
iv = NAMES.index("v_rt")
off = np.zeros(NY); off[iv] = 1e-3 * SCALE[iv]
Ap = Di @ jacobian(m, h0, ys + off, 1e-7) @ D
Am = Di @ jacobian(m, h0, ys - off, 1e-7) @ D
dA = Ap - Am
U, s, Vt = np.linalg.svd(dA)
print("singular values of A+ - A-:", s[:5])
u = U[:, 0] * s[0]; v = Vt[0]
print("u (rows):", {NAMES[i]: round(float(u[i]), 5) for i in np.argsort(-np.abs(u))[:8]})
print("v (cols):", {NAMES[i]: round(float(v[i]), 5) for i in np.argsort(-np.abs(v))[:8]})
A0 = (Ap + Am) / 2
print("rho(A+), rho(A-), rho(A0):", [np.max(np.abs(np.linalg.eigvals(X))) for X in (Ap, Am, A0)])
pickle.dump(dict(Ap=Ap, Am=Am, A0=A0, u=u, v=v), open('/tmp/ts_switch.pkl', 'wb'))
for mu in (0.99895, 0.9990, 0.9992, 0.9995, 0.9999):
    if mu <= np.max(np.abs(np.linalg.eigvals(A0))):
        continue
    w = np.concatenate([np.linspace(0, 0.02, 4000), np.linspace(0.02, np.pi, 4000)])
    g = []
    for om in w:
        z = np.exp(1j * om)
        g.append(abs(v @ np.linalg.solve(z * np.eye(NY) - A0 / mu, u / mu)))
    g = np.array(g)
    print(f"mu {mu}: sup |G_mu| on grid = {g.max():.4f} at omega {w[g.argmax()]:.5f} (need 0.5*sup < 1)")
