"""Integration-only error floor: Euler with k substeps using JSBSim's exact accelerations."""
import math, random, sys, numpy as np
sys.path.insert(0, 'sysid')
import collect as C
rng = random.Random(7)
errs = {1: [], 2: [], 4: [], 8: []}
for ep in range(40):
    fdm = C.make(rng); gen = C.pilot(rng, ep % 3 == 0); elev = 0.0; x = 0.0
    for k in range(900):
        stick, thr = next(gen)
        elev += max(-C.ELEV_STEP, min(C.ELEV_STEP, stick - elev))
        fdm['fcs/elevator-cmd-norm'] = -elev; fdm['fcs/throttle-cmd-norm'] = thr
        traj = [C.snapshot(fdm, x)]
        for i in range(16):                       # 1/128 s steps over one tick, plus one extra pair
            if i < 8 or i == 8:
                C.leveler(fdm); fdm.run(); traj.append(C.snapshot(fdm, x))
            if i == 8: break
        s0 = traj[0]
        if abs(s0['phi']) > math.radians(35) or s0['h'] < 150 or abs(s0['theta']) > 1: break
        v = np.array([[t['vx'], t['vz'], t['q']] for t in traj])      # 10 samples at 1/128 s
        acc = (v[1:] - v[:-1]) * 128                                    # forward-difference accel
        for ks in errs:
            stride = 8 // ks
            pred = v[0] + sum(acc[j * stride] for j in range(ks)) / 16 / ks
            errs[ks].append(np.abs(v[8] - pred))
        # roll back the extra step: rerunning is costly; accept the 1/128 s drift by continuing
for ks, e in errs.items():
    e = np.array(e)
    print(f'substeps {ks}: ' + ' | '.join(f'{n} p99 {np.quantile(e[:, i], .99):.4f} max {e[:, i].max():.4f}' for i, n in enumerate(['vx', 'vz', 'q'])))
