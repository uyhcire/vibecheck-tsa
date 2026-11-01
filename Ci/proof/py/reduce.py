import numpy as np
from lin import ZI
from pf import NAMES
Js = np.load("Jys.npy")
names = [NAMES[i] for i in ZI]
Y = [names.index(k) for k in ["vx", "vz", "dz", "q", "rpm", "tmap", "eI"]]
G_ = [i for i in range(len(names)) if i not in Y]
def reduced(J):
    Jyy = J[np.ix_(Y, Y)]; Jyg = J[np.ix_(Y, G_)]; Jgy = J[np.ix_(G_, Y)]; Jgg = J[np.ix_(G_, G_)]
    G = np.zeros((len(G_), len(Y)))
    for _ in range(200):
        A = Jyy + Jyg @ G
        G = (Jgy + Jgg @ G) @ np.linalg.inv(A)
    return Jyy + Jyg @ G, G
if __name__ == "__main__":
    As = []; Gs = []
    for J in Js:
        A, G = reduced(J); As.append(A); Gs.append(G)
        ev = np.linalg.eigvals(A); ev = ev[np.argsort(-abs(ev))]
        print(" ".join(f"{abs(e):.4f}" for e in ev))
    np.save("As.npy", np.array(As)); np.save("Gs.npy", np.array(Gs))
