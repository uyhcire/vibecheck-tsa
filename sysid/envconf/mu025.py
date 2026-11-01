"""Required escape height of the fitted mu=0.25 envelope (eric/envelope-params) under commit-referenced
(Envelope3D) semantics: total vz drop during the delay, airspeed floor from the commit airspeed."""
import math

DT = 1 / 16
P = dict(delay=35, dvz=2.19, vMin=32.0, escV=0.853, hSlack=0.017, sag=0.04,
         base=(0.187, 0.143), bands=[(33, 0.187, 0.143), (37, 0.187, 0.143), (42, 1.5, 5.129), (50, 3.75, 12.335),
                                     (60, 7.125, 13.908)])


def perf(V):
    p, c = P['base']
    for lo, pp, cc in P['bands']:
        if lo <= V:
            p, c = max(p, pp), max(c, cc)
    return p, c


def H(V0, g0, per_tick_delay=False):
    vz0 = V0 * math.sin(g0)
    VF = max(P['vMin'], V0 - P['escV'])
    pull, climb = perf(VF)
    sig, h, hmin, k = vz0 - P['dvz'], 0.0, 0.0, 0
    prev = vz0
    while True:
        if k < P['delay']:
            nxt = prev - P['dvz'] if per_tick_delay else sig
        else:
            nxt = min(climb, prev + DT * pull)
        h += DT * min(prev, nxt) - P['hSlack']
        hmin = min(hmin, h)
        prev, k = nxt, k + 1
        if k >= P['delay'] and prev >= climb:
            break
    return -hmin + P['sag']


if __name__ == '__main__':
    for V in (35, 45, 55):
        print(V, [round(H(V, g), 1) for g in (-0.3, -0.15, 0.0)], 'per-tick delay (2D semantics):',
              [round(H(V, g, True), 0) for g in (-0.3, -0.15, 0.0)])
