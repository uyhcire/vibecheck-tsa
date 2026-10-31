"""Fly c172p in banked turns (held/varied bank targets, coordinated and uncoordinated); same columns as collect.py plus p, r, pd, rd, ay."""
import csv, math, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import collect
from collect import FT, SUB, ELEV_STEP, make, pilot, snapshot as base_snapshot

EXTRA = ['p', 'r', 'pd', 'rd', 'ay', 'phit', 'rudc', 'fy', 'ail', 'rudp']
COLS = collect.COLS + EXTRA
KB, KR = -3.0, 2.0
SIGN = 1.0

def snapshot(fdm, x):
    s = base_snapshot(fdm, x)
    s.update(p=fdm['velocities/p-rad_sec'], r=fdm['velocities/r-rad_sec'],
             pd=fdm['accelerations/pdot-rad_sec2'], rd=fdm['accelerations/rdot-rad_sec2'],
             ay=fdm['accelerations/vdot-ft_sec2'] * FT,
             fy=(fdm['forces/fby-aero-lbs'] + fdm['forces/fby-prop-lbs']) * collect.LBF / 1000,
             ail=fdm['fcs/left-aileron-pos-rad'], rudp=fdm['fcs/rudder-pos-rad'])
    return s

def world_accel(fdm):
    """(d|v_horizontal|/dt, d v_up/dt): body acceleration plus omega x v, rotated to NED with the full attitude."""
    g = lambda n: fdm[n]
    u, v, w = (g('velocities/u-fps') * FT, g('velocities/v-fps') * FT, g('velocities/w-fps') * FT)
    p, q, r = g('velocities/p-rad_sec'), g('velocities/q-rad_sec'), g('velocities/r-rad_sec')
    bx = g('accelerations/udot-ft_sec2') * FT + q * w - r * v
    by = g('accelerations/vdot-ft_sec2') * FT + r * u - p * w
    bz = g('accelerations/wdot-ft_sec2') * FT + p * v - q * u
    ph, th, ps = g('attitude/phi-rad'), g('attitude/theta-rad'), g('attitude/psi-rad')
    sp, cp, st, ct, ss, cs = math.sin(ph), math.cos(ph), math.sin(th), math.cos(th), math.sin(ps), math.cos(ps)
    an = ct * cs * bx + (sp * st * cs - cp * ss) * by + (cp * st * cs + sp * ss) * bz
    ae = ct * ss * bx + (sp * st * ss + cp * cs) * by + (cp * st * ss - sp * cs) * bz
    ad = -st * bx + sp * ct * by + cp * ct * bz
    vn, ve = g('velocities/v-north-fps') * FT, g('velocities/v-east-fps') * FT
    return (vn * an + ve * ae) / math.hypot(vn, ve), -ad

def bank_schedule(rng):
    phit, cur = 0.0, 0.0
    while True:
        hold = rng.randint(24, 160)
        target = 0.0 if rng.random() < 0.1 else math.radians(rng.uniform(-45, 45))
        coord = rng.random() < 0.7
        off = 0.0 if coord else rng.uniform(-0.6, 0.6)
        rate = math.radians(rng.uniform(3, 20)) / 16
        for _ in range(hold):
            cur += max(-rate, min(rate, target - cur))
            yield cur, off, coord

def control(fdm, phit, off, coord):
    phi, p, r, beta = (fdm['attitude/phi-rad'], fdm['velocities/p-rad_sec'], fdm['velocities/r-rad_sec'],
                       fdm['aero/beta-rad'])
    fdm['fcs/aileron-cmd-norm'] = max(-1, min(1, -8.0 * (phi - phit) - 2.0 * p))
    if coord:
        v = max(fdm['velocities/vt-fps'] * FT, 20.0)
        rc = 9.81 * math.tan(phi) / v
        rud = SIGN * (KB * beta + KR * (r - rc))
    else:
        rud = off
    fdm['fcs/rudder-cmd-norm'] = max(-1, min(1, rud))

def episode(ep, rng, writer, ticks, lim_phi=math.radians(60)):
    fdm = make(rng)
    aggressive = ep % 3 == 0
    elev = 0.0
    x = 0.0
    gen = pilot(rng, aggressive)
    bank = bank_schedule(rng)
    s0 = snapshot(fdm, 0.0)
    hist = [(s0['vx'], s0['vz'], *world_accel(fdm), s0['udot'], s0['wdot'])] * 3
    for k in range(ticks):
        stick, thr = next(gen)
        phit, off, coord = next(bank)
        elev += max(-ELEV_STEP, min(ELEV_STEP, stick - elev))
        snap = snapshot(fdm, x)
        row = dict(ep=ep, k=k, elev=elev, thr=thr, phit=phit, rudc=0.0 if coord else off, **snap)
        row.update(ah0=hist[-1][2], au0=hist[-1][3], ah1=hist[-2][2], au1=hist[-2][3],
                   hvx1=hist[-2][0], hvz1=hist[-2][1], hvx2=hist[-3][0], hvz2=hist[-3][1],
                   pudot=hist[-2][4], pwdot=hist[-2][5])
        if abs(snap['phi']) > lim_phi or snap['h'] < 150 or snap['vt'] > 80 \
                or abs(snap['theta']) > math.radians(60):
            writer.writerow(dict(row, ax0=0, az0=0, qd0=0))
            return k
        fdm['fcs/elevator-cmd-norm'] = -elev
        fdm['fcs/throttle-cmd-norm'] = thr
        for i in range(SUB):
            control(fdm, phit, off, coord)
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
