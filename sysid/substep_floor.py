"""Integration-only error floor: Euler with k substeps using JSBSim's exact accelerations."""
import math, random, sys, numpy as np
sys.path.insert(0, 'sysid')
import collect as C
rng = random.Random(7)
errs = {1: [], 2: [], 4: [], 8: []}
gentle = []
qs = []
signed4 = []
eps_id = []
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
            if ks == 4: signed4.append(v[8] - pred); eps_id.append(ep)
        gentle.append(ep % 3 != 0); qs.append(abs(s0['q']))
        # roll back the extra step: rerunning is costly; accept the 1/128 s drift by continuing
g = np.array(gentle); qa = np.array(qs)
e4 = np.array(errs[4])
for lab, m in [('aggressive episodes', ~g), ('gentle episodes', g), ('|q|<0.05 rad/s', qa < 0.05), ('|q|<0.02 rad/s', qa < 0.02)]:
    print(f'4 substeps, {lab:20s} n={m.sum():5d}: ' + ' | '.join(f'{n} max {e4[m][:, i].max():.4f} p99 {np.quantile(e4[m][:, i], .99):.4f}' for i, n in enumerate(['vx', 'vz', 'q'])))
for ks, e in errs.items():
    e = np.array(e)
    print(f'substeps {ks}: ' + ' | '.join(f'{n} p99 {np.quantile(e[:, i], .99):.4f} max {e[:, i].max():.4f}' for i, n in enumerate(['vx', 'vz', 'q'])))

r4 = np.array(signed4); eid = np.array(eps_id)
same = eid[1:] == eid[:-1]
dr = np.abs(r4[1:] - r4[:-1])[same]
print('4 substeps, tick-to-tick change of the residual: ' + ' | '.join(
    f'{n} max {dr[:, i].max():.4f} p99 {np.quantile(dr[:, i], .99):.4f}' for i, n in enumerate(['vx', 'vz', 'q'])))
