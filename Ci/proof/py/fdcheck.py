import numpy as np, lin
from design import nearest
from lin import jac
for scale in [1, 4]:
    lin.STEP = {k: v*scale for k, v in lin.STEP.items()}
    for h in [100, 110, 500, 1000, 1010, 1020]:
        J, _ = jac(nearest(h))
        ev = np.linalg.eigvals(J); ev = ev[np.argsort(-abs(ev))]
        print(scale, h, " ".join(f"{abs(e):.4f}" for e in ev[:6]))
    lin.STEP = {k: v//scale for k, v in lin.STEP.items()}
