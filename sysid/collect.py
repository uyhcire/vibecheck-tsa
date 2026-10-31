"""Fly JSBSim's c172p with random longitudinal inputs and a wings-leveler; log 16 Hz ticks.

Usage: collect.py OUT.csv EPISODES TICKS SEED [rud0]   (rud0: rudder held centred, which keeps sideslip near 0)
"""
import csv, math, random, sys
import jsbsim

FT = 0.3048
SUB = 8                      # JSBSim steps per 1/16 s tick (dt = 1/128 s)
ELEV_STEP = 0.125            # our elevator rate limit per tick (2/s)
RUDDER_OFF = False           # `rud0` run mode: the original rudder law drives sideslip to ~0.3 rad

LBF = 4.4482216152605    # N per lbf
SLUG = 14.593902937      # kg per slug
BASE = ['ep', 'k', 'x', 'h', 'vx', 'vz', 'theta', 'q', 'elev', 'thr',
        'alpha', 'phi', 'beta', 'rpm', 'vt', 'ax0', 'az0', 'qd0', 'thrust',
        'elevp', 'thrp']   # elevp/thrp: inputs of the previous tick, which produced the logged properties/derivatives
# Hidden state at tick start (SI; manifold pressure Pa): everything JSBSim carries between steps that the Lean state needs.
HID = ['map', 'stallh', 'udot', 'wdot', 'qdot', 'adot', 'psi', 'mix',
       'ah0', 'au0', 'ah1', 'au1',            # world-frame acceleration now / one 1/128 s step earlier
       'hvx1', 'hvz1', 'hvx2', 'hvz2',        # horizontal/vertical speed 1 and 2 steps earlier
       'pudot', 'pwdot']                      # body accelerations one step earlier (what alphadot used)
# Diagnostics: aero/prop quantities JSBSim computed for the tick-start state itself (SI; qbar kPa).
DIAG = ['mass', 'cgx', 'cgz', 'iyy', 'rho', 'grav', 'qbar_s', 'fxa', 'fza', 'ma', 'fxp', 'fzp', 'mp',
        'hp', 'vind', 'cl', 'cd', 'cmal', 'tmach', 'ct', 'jadv', 'ua', 'wa']
COLS = BASE + HID + DIAG

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
    fdm['fcs/rudder-cmd-norm'] = 0.0 if RUDDER_OFF else max(-1, min(1, -3.0 * r + 4.0 * fdm['aero/beta-rad']))

def snapshot(fdm, x):
    vn, ve, vd = (fdm['velocities/v-north-fps'] * FT, fdm['velocities/v-east-fps'] * FT,
                  fdm['velocities/v-down-fps'] * FT)
    return dict(x=x, h=fdm['position/h-sl-meters'], vx=math.hypot(vn, ve), vz=-vd,
                theta=fdm['attitude/theta-rad'], q=fdm['velocities/q-rad_sec'],
                alpha=fdm['aero/alpha-rad'], phi=fdm['attitude/phi-rad'],
                beta=fdm['aero/beta-rad'], rpm=fdm['propulsion/engine/engine-rpm'],
                vt=fdm['velocities/vt-fps'] * FT, thrust=fdm['propulsion/engine/thrust-lbs'] * LBF,
                map=fdm['propulsion/engine/map-pa'], stallh=fdm['aero/stall-hyst-norm'],
                udot=fdm['accelerations/udot-ft_sec2'] * FT, wdot=fdm['accelerations/wdot-ft_sec2'] * FT,
                qdot=fdm['accelerations/qdot-rad_sec2'], adot=fdm['aero/alphadot-rad_sec'],
                psi=fdm['attitude/psi-rad'], mix=fdm['fcs/mixture-pos-norm'],
                mass=fdm['inertia/mass-slugs'] * SLUG, cgx=fdm['inertia/cg-x-in'] * 0.0254,
                cgz=fdm['inertia/cg-z-in'] * 0.0254, iyy=fdm['inertia/iyy-slugs_ft2'] * SLUG * FT * FT,
                rho=fdm['atmosphere/rho-slugs_ft3'] * SLUG / FT ** 3, grav=fdm['accelerations/gravity-ft_sec2'] * FT,
                qbar_s=fdm['aero/qbar-psf'] * 0.04788025898,
                fxa=fdm['forces/fbx-aero-lbs'] * LBF, fza=fdm['forces/fbz-aero-lbs'] * LBF,
                ma=fdm['moments/m-aero-lbsft'] * LBF * FT, fxp=fdm['forces/fbx-prop-lbs'] * LBF,
                fzp=fdm['forces/fbz-prop-lbs'] * LBF, mp=fdm['moments/m-prop-lbsft'] * LBF * FT,
                hp=fdm['propulsion/engine/power-hp'], vind=fdm['propulsion/engine/prop-induced-velocity_fps'] * FT,
                cl=fdm['aero/coefficient/CLwbh'], cd=fdm['aero/coefficient/CDwbh'],
                cmal=fdm['aero/coefficient/Cmalpha'], tmach=fdm['propulsion/engine/helical-tip-Mach'],
                ct=fdm['propulsion/engine/thrust-coefficient'], jadv=fdm['propulsion/engine/advance-ratio'],
                ua=fdm['velocities/u-aero-fps'] * FT, wa=fdm['velocities/w-aero-fps'] * FT)

def world_accel(fdm):
    """Local-frame (horizontal, up) acceleration of the ground-relative velocity, from JSBSim's body-frame UVWdot."""
    th, q = fdm['attitude/theta-rad'], fdm['velocities/q-rad_sec']
    u, w = fdm['velocities/u-fps'] * FT, fdm['velocities/w-fps'] * FT
    bx = fdm['accelerations/udot-ft_sec2'] * FT + q * w
    bz = fdm['accelerations/wdot-ft_sec2'] * FT - q * u
    c, s = math.cos(th), math.sin(th)
    return c * bx + s * bz, s * bx - c * bz

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
    s0 = snapshot(fdm, 0.0)
    hist = [(s0['vx'], s0['vz'], *world_accel(fdm), s0['udot'], s0['wdot'])] * 3      # per-substep (vx, vz, a_h, a_up, udot, wdot), newest last
    elevp, thrp = 0.0, 0.0
    for k in range(ticks):
        stick, thr = next(gen)
        elev += max(-ELEV_STEP, min(ELEV_STEP, stick - elev))
        snap = snapshot(fdm, x)
        row = dict(ep=ep, k=k, elev=elev, thr=thr, elevp=elevp if k else elev, thrp=thrp if k else thr, **snap)
        row.update(ah0=hist[-1][2], au0=hist[-1][3], ah1=hist[-2][2], au1=hist[-2][3],
                   hvx1=hist[-2][0], hvz1=hist[-2][1], hvx2=hist[-3][0], hvz2=hist[-3][1],
                   pudot=hist[-2][4], pwdot=hist[-2][5])
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
            hist.append((math.hypot(vn, ve), -fdm['velocities/v-down-fps'] * FT, *world_accel(fdm),
                         fdm['accelerations/udot-ft_sec2'] * FT, fdm['accelerations/wdot-ft_sec2'] * FT))
            hist = hist[-3:]
            if i == 0:
                s1 = snapshot(fdm, x)
                row.update(ax0=(s1['vx'] - snap['vx']) * 128, az0=(s1['vz'] - snap['vz']) * 128,
                           qd0=(s1['q'] - snap['q']) * 128)
        writer.writerow(row)
        elevp, thrp = elev, thr
    return ticks

def main():
    global RUDDER_OFF
    out, n_ep, ticks, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    RUDDER_OFF = len(sys.argv) > 5 and sys.argv[5] == 'rud0'
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
