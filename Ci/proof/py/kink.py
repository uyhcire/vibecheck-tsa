"""Kink-aware fast tolerance: per node, the residual's principal direction k gets a loose bound, the rest tight."""
import numpy as np, sample as sm, os
from sample import *
sm.GsN = np.load("GsN_fit.npy")
import os; RR = float(os.environ.get("RR", "6.0"))
X = sm.sample(16000, RR, 0.0); img, *_ = ticks(X)
H = img[:,1]/65536; E = np.array([coords(xi)[2] for xi in img])     # signed residuals, STEP units
K = []; TK = []; TP = []
floor = np.array([0.05,0.1,0.5,0.1,0.5,0.05,0.1,0.5,0.02,0.02,0.02]) * 0.5
for i, hn in enumerate(HN):
    m = (H >= hn - 150) & (H <= hn + 150); Em = E[m]
    U, s, Vt = np.linalg.svd(Em - 0*Em.mean(axis=0), full_matrices=False)
    k = Vt[0]; k = k * np.sign(k[np.argmax(abs(k))])
    lam = Em @ k; perp = Em - np.outer(lam, k)
    K.append(k); TK.append(1.3 * abs(lam).max() + 0.3); TP.append(1.3 * abs(perp).max(axis=0) + floor)
    if i % 4 == 0: print(int(hn), "k", np.round(k, 2), "tau_k", round(TK[-1], 2), "perp max", np.round(abs(perp).max(axis=0), 2))
np.save("kN.npy", np.array(K)); np.save("tkN.npy", np.array(TK)); np.save("tpN.npy", np.array(TP))
