"""Replay a harness run's commands in the pip `jsbsim` 1.3.3 package and count bitwise state mismatches.

usage: replay_pip.py RUN   (RUN = path prefix written by the harness: RUN.names, RUN.bin, RUN.ic)
"""
import struct, sys
import numpy as np
import jsbsim

PROPS = [('uvw1', 'velocities/u-fps'), ('uvw2', 'velocities/v-fps'), ('uvw3', 'velocities/w-fps'),
         ('pqr1', 'velocities/p-rad_sec'), ('pqr2', 'velocities/q-rad_sec'), ('pqr3', 'velocities/r-rad_sec'),
         ('phi', 'attitude/phi-rad'), ('theta', 'attitude/theta-rad'), ('psi', 'attitude/psi-rad'),
         ('hsl', 'position/h-sl-ft'), ('rpm', 'propulsion/engine/propeller-rpm'),
         ('tank0', 'propulsion/tank[0]/contents-lbs'), ('d_alpha', 'aero/alpha-rad'),
         ('g1_wow', 'gear/unit[1]/WOW')]


def main():
    run = sys.argv[1]
    names = open(run + '.names').read().split()
    recs = np.fromfile(run + '.bin', dtype='<f8').reshape(-1, len(names))
    col = {n: i for i, n in enumerate(names)}
    ics = {}
    for l in open(run + '.ic'):
        f = l.split()
        ics[int(f[0])] = (float.fromhex(f[1]), float.fromhex(f[2]), float.fromhex(f[3]), f[4])
    bad = total = 0
    for ep, (h0, vc0, gam0, hprop) in sorted(ics.items()):
        rows = recs[recs[:, col['ep']] == ep]
        fdm = jsbsim.FGFDMExec(None)
        fdm.set_debug_level(0)
        fdm.load_model('c172p')
        fdm['ic/terrain-elevation-ft'] = 0
        fdm[hprop] = h0
        fdm['ic/vc-kts'] = vc0
        fdm['ic/gamma-deg'] = gam0
        fdm['ic/psi-true-deg'] = 90
        fdm.set_dt(1 / 128)
        fdm.run_ic()
        fdm['propulsion/set-running'] = -1
        fdm['fcs/mixture-cmd-norm'] = 0.9
        for r in rows:
            for n, p in PROPS:
                if n == 'd_alpha' and r[col['k']] == 0:
                    continue
                total += 1
                if struct.pack('<d', fdm[p]) != struct.pack('<d', r[col[n]]):
                    bad += 1
                    if bad <= 5:
                        print(f'ep {ep} k {int(r[col["k"]])} {n}: pip {fdm[p]!r} harness {r[col[n]]!r}')
            if r[col['stop']]:
                break
            fdm['fcs/elevator-cmd-norm'] = r[col['u_elev']]
            fdm['fcs/throttle-cmd-norm'] = r[col['u_thr']]
            fdm['fcs/aileron-cmd-norm'] = r[col['u_ail']]
            fdm['fcs/rudder-cmd-norm'] = r[col['u_rud']]
            fdm['fcs/left-brake-cmd-norm'] = r[col['u_brkL']]
            fdm['fcs/right-brake-cmd-norm'] = r[col['u_brkR']]
            fdm.run()
    print(f'{total} values compared, {bad} differ bitwise')


if __name__ == '__main__':
    main()
