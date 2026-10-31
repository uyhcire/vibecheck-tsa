"""Fly JSBSim's c172p with random longitudinal inputs and a wings-leveler; log 16 Hz ticks."""
import csv, math, random, sys
import jsbsim

FT = 0.3048
SUB = 8                      # JSBSim steps per 1/16 s tick (dt = 1/128 s)
ELEV_STEP = 0.125            # our elevator rate limit per tick (2/s)

COLS = ['ep', 'k', 'x', 'h', 'vx', 'vz', 'theta', 'q', 'elev', 'thr',
        'alpha', 'phi', 'beta', 'rpm', 'vt', 'ax0', 'az0', 'qd0', 'thrust']

def make(seed_rng):
    fdm = jsbsim.FGFDMExec(None)
    fdm.set_debug_level(0)
    fdm.load_model('c172p')
    fdm['ic/h-sl-ft'] = seed_rng.uniform(2000, 4000)
    fdm['ic/terrain-elevation-ft'] = 0
    fdm['ic/vc-kts'] = seed_rng.uniform(65, 110)
    fdm['ic/gamma-deg'] = 0
    fdm['ic/psi-true-deg'] = 90
    fdm.set_dt(1 / 128)
    fdm.run_ic()
    fdm['propulsion/set-running'] = -1
    fdm['fcs/mixture-cmd-norm'] = 0.9
    return fdm

def leveler(fdm):
    phi = fdm['attitude/phi-rad']
    p = fdm['velocities/p-rad_sec']
    r = fdm['velocities/r-rad_sec']
    fdm['fcs/aileron-cmd-norm'] = max(-1, min(1, -8.0 * phi - 2.0 * p))
    fdm['fcs/rudder-cmd-norm'] = max(-1, min(1, -3.0 * r + 4.0 * fdm['aero/beta-rad']))

def snapshot(fdm, x):
    vn, ve, vd = (fdm['velocities/v-north-fps'] * FT, fdm['velocities/v-east-fps'] * FT,
                  fdm['velocities/v-down-fps'] * FT)
    return dict(x=x, h=fdm['position/h-sl-meters'], vx=math.hypot(vn, ve), vz=-vd,
                theta=fdm['attitude/theta-rad'], q=fdm['velocities/q-rad_sec'],
                alpha=fdm['aero/alpha-rad'], phi=fdm['attitude/phi-rad'],
                beta=fdm['aero/beta-rad'], rpm=fdm['propulsion/engine/engine-rpm'],
                vt=fdm['velocities/vt-fps'] * FT, thrust=fdm['propulsion/engine/thrust-lbs'] * 4.44822)

def pilot(rng, aggressive):
    """Piecewise-constant random stick/throttle targets."""
    while True:
        hold = rng.randint(8, 64)
        span = 1.0 if aggressive else 0.5
        stick = rng.uniform(-span, span)
        thr = rng.choice([0.0, 1.0, rng.random(), rng.random()])
        for _ in range(hold):
            yield stick, thr

def episode(ep, rng, writer, ticks):
    fdm = make(rng)
    aggressive = ep % 3 == 0
    elev = 0.0
    x = 0.0
    gen = pilot(rng, aggressive)
    for k in range(ticks):
        stick, thr = next(gen)
        elev += max(-ELEV_STEP, min(ELEV_STEP, stick - elev))
        snap = snapshot(fdm, x)
        row = dict(ep=ep, k=k, elev=elev, thr=thr, **snap)
        if abs(snap['phi']) > math.radians(35) or snap['h'] < 150 or snap['vt'] > 80 \
                or abs(snap['theta']) > math.radians(60):
            writer.writerow(dict(row, ax0=0, az0=0, qd0=0))
            return k
        fdm['fcs/elevator-cmd-norm'] = -elev
        fdm['fcs/throttle-cmd-norm'] = thr
        for i in range(SUB):
            leveler(fdm)
            fdm.run()
            vn, ve = fdm['velocities/v-north-fps'] * FT, fdm['velocities/v-east-fps'] * FT
            x += math.hypot(vn, ve) / 128
            if i == 0:
                s1 = snapshot(fdm, x)
                row.update(ax0=(s1['vx'] - snap['vx']) * 128, az0=(s1['vz'] - snap['vz']) * 128,
                           qd0=(s1['q'] - snap['q']) * 128)
        writer.writerow(row)
    return ticks

def main():
    out, n_ep, ticks, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    with open(out, 'w', newline='') as f:
        w = csv.DictWriter(f, COLS)
        w.writeheader()
        total = 0
        for ep in range(n_ep):
            total += episode(ep, rng, w, ticks)
    print(f'{n_ep} episodes, {total} ticks -> {out}')

if __name__ == '__main__':
    main()
