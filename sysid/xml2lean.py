"""Generate Jsb/C172Aero.lean from JSBSim's c172p.xml, eng_io320.xml and prop_75in2f.xml.

Usage: .venv/bin/python -I sysid/xml2lean.py [out.lean]

Lean units: m, s, rad, t (mass), kN, kPa, kW, K, kg/m^3.  Every number is emitted as an `Fx` raw integer
(value * 2^16, rounded to nearest).  Only the DRAG, LIFT and PITCH axes are generated (the longitudinal model).
Unknown function elements or properties raise: nothing is silently dropped.
"""
import math, os, sys
import xml.etree.ElementTree as ET
import jsbsim

PKG = os.path.dirname(jsbsim.__file__)
FT, IN, LBF, SLUG, LB, PSF, SQFT = 0.3048, 0.0254, 4.4482216152605, 14.593902937, 0.45359237, 47.88025898, 0.09290304
ONE = 65536

def raw(v):
    return int(round(v * ONE))

def fx(v):
    return f'⟨{raw(v)}⟩'

# ---- property leaves: JSBSim property -> (Lean field, scale such that lean = jsb * scale, typical magnitude)
FIELDS = {
    'aero/qbar-psf': ('qbar', PSF / 1000, 2.0),
    'aero/alpha-rad': ('alpha', 1.0, 0.1),
    'aero/alphadot-rad_sec': ('adot', 1.0, 0.05),
    'velocities/q-aero-rad_sec': ('qAero', 1.0, 0.1),
    'aero/ci2vel': ('ci2vel', 1.0, 0.014),
    'fcs/elevator-pos-rad': ('elevRad', 1.0, 0.2),
    'fcs/mag-elevator-pos-rad': ('magElevRad', 1.0, 0.2),
    'aero/mag-beta-rad': ('magBeta', 1.0, 0.05),
    'fcs/flap-pos-deg': ('flapDeg', 1.0, 10.0),
    'aero/stall-hyst-norm': ('stallHyst', 1.0, 1.0),
    'aero/h_b-mac-ft': ('hbMac', 1.0, 1.0),          # dimensionless height/span despite the name
    'velocities/u-aero-fps': ('uAero', FT, 50.0),
    'propulsion/engine/prop-induced-velocity_fps': ('vInd', FT, 5.0),
    'atmosphere/rho-slugs_ft3': ('rho', SLUG / FT ** 3, 1.1),
}
CONSTS = {  # metrics resolved at generation time (JSBSim units as in the file)
    'metrics/Sw-sqft': None, 'metrics/bw-ft': None, 'metrics/cbarw-ft': None,
}

class Gen:
    def __init__(self):
        self.tables = []    
        self.fields_used = set()
        self.fn_out = {}    
        self.fn_defs = []     # lean text
        self.ntab = 0
        self.metrics = {}

    def parse_table(self, el, owner):
        ivs = el.findall('independentVar')
        data = [[float(t) for t in ln.split()] for ln in el.find('tableData').text.strip().splitlines() if ln.strip()]
        self.ntab += 1
        name = f'tbl_{owner}_{self.ntab}'
        if len(ivs) <= 1:
            sc = self.field_scale(ivs[0].text.strip()) if ivs else 1.0
            xs = [raw(r[0] * sc) for r in data]
            ys = [raw(r[1]) for r in data]
            self.tables.append((name, f'def {name} : Tbl1 := {{ xs := #{xs}, ys := #{ys} }}'))
            mag = max(abs(r[1]) for r in data)
            return name, 1, [ivs[0].text.strip()] if ivs else [], mag
        assert len(ivs) == 2, 'table with >2 independent variables'
        look = {iv.get('lookup'): iv.text.strip() for iv in ivs}
        assert set(look) == {'row', 'column'}, f'unexpected lookup attributes {look}'
        rs, cs = self.field_scale(look['row']), self.field_scale(look['column'])
        cols = [raw(c * cs) for c in data[0]]
        rows = [raw(r[0] * rs) for r in data[1:]]
        body = [raw(v) for r in data[1:] for v in r[1:]]
        assert all(len(r) == len(cols) + 1 for r in data[1:]) and len(data[0]) == len(cols)
        self.tables.append((name, f'def {name} : Tbl2 := {{ rows := #{rows}, cols := #{cols}, data := #{body} }}'))
        mag = max(abs(v) for r in data[1:] for v in r[1:])
        return name, 2, [look['row'], look['column']], mag

    def field_scale(self, prop):
        if prop not in FIELDS:
            raise SystemExit(f'unhandled property {prop}')
        return FIELDS[prop][1]

    def use_field(self, prop):
        f, s, m = FIELDS[prop]
        self.fields_used.add(f)
        return f'e.{f}', s, m

    def comp(self, node, scale):
        const, factors = self.comp_prod(node, scale)
        return self.render(const, factors)

    def render(self, const, factors):
        factors = sorted(factors, key=lambda f: -f[1])
        if not factors:
            return f'({fx(const)} : Fx)'
        names = [f[0] for f in factors]
        if 0 < abs(const) < 0.05:
            prod = names[0] if len(names) == 1 else '(' + ' * '.join(names) + ')'
            q = f'({prod} / ({fx(1 / abs(const))} : Fx))'
            return q if const > 0 else f'(-{q})'
        parts = [f'({fx(const)} : Fx)'] if abs(const - 1.0) > 1e-12 else []
        parts += names
        if len(parts) == 1:
            return parts[0]
        return '(' + ' * '.join(parts) + ')'

    def comp_prod(self, node, scale):
        tag = node.tag
        if tag == 'product':
            const, factors = scale, []
            for ch in node:
                if ch.tag == 'description':
                    continue
                c, f = self.leaf(ch)
                const *= c
                factors += f
            return const, factors
        if tag == 'sum':
            terms = [self.render(*self.comp_prod(sub, scale)) for sub in node if sub.tag != 'description']
            return 1.0, [('(' + ' + '.join(terms) + ')', 10.0)]
        c, f = self.leaf(node)
        return c * scale, f

    def leaf(self, ch):
        t = ch.tag
        if t == 'value':
            return float(ch.text), []
        if t == 'property':
            p = ch.text.strip()
            if p in self.fn_out:
                nm, s = self.fn_out[p]
                return 1.0 / s, [(f'({nm} e)', 1.0)]
            if p in CONSTS:
                return self.metrics[p], []
            ref, s, m = self.use_field(p)
            return 1.0 / s, [(ref, m)]
        if t == 'table':
            name, dim, vars_, mag = self.parse_table(ch, 'x')
            args = []
            for v in vars_:
                ref, s, m = self.use_field(v)
                args.append(ref)
            call = f'(Tbl{dim}.eval {name} {" ".join(args)})'
            return 1.0, [(call, mag)]
        if t == 'sum':
            terms = []
            for sub in ch:
                if sub.tag == 'description':
                    continue
                c, f = self.leaf(sub)
                terms.append(self.render(c, f))
            return 1.0, [('(' + ' + '.join(terms) + ')', 10.0)]
        if t == 'product':
            c, f = self.comp_prod(ch, 1.0)
            return 1.0, [(self.render(c, f), 1.0)]
        raise SystemExit(f'unhandled function element <{t}>')

def lean_name(prop):
    return prop.split('/')[-1].replace('-', '_')

def main():
    out = sys.argv[1] if len(sys.argv) > 1 else 'Jsb/C172Aero.lean'
    ac = ET.parse(f'{PKG}/aircraft/c172p/c172p.xml').getroot()
    eng = ET.parse(f'{PKG}/engine/eng_io320.xml').getroot()
    prop = ET.parse(f'{PKG}/engine/prop_75in2f.xml').getroot()
    g = Gen()

    m = ac.find('metrics')
    Sw, bw, cw = (float(m.find(k).text) for k in ('wingarea', 'wingspan', 'chord'))
    g.metrics = {'metrics/Sw-sqft': Sw, 'metrics/bw-ft': bw, 'metrics/cbarw-ft': cw}
    def loc(el):  # inches -> metres, structural frame (x aft, y right, z up)
        return [float(el.find(a).text) for a in 'xyz']
    rp = [v for v in loc([e for e in m.findall('location') if e.get('name') == 'AERORP'][0])]

    mb = ac.find('mass_balance')
    base_cg = loc([e for e in mb.findall('location') if e.get('name') == 'CG'][0])
    wempty = float(mb.find('emptywt').text)
    iyy0 = float(mb.find('iyy').text)
    pms = [(float(p.find('weight').text), loc(p.find('location'))) for p in mb.findall('pointmass')]
    pr = ac.find('propulsion')
    for tk in pr.findall('tank'):
        pms.append((float(tk.find('contents').text), loc(tk.find('location'))))
    W = wempty + sum(w for w, _ in pms)
    cg = [(wempty * base_cg[i] + sum(w * r[i] for w, r in pms)) / W for i in range(3)]
    def pm_iyy(w, r):   # slug ft^2 about the CG
        return w / 32.174049 * (((r[0] - cg[0]) / 12) ** 2 + ((r[2] - cg[2]) / 12) ** 2)
    iyy = iyy0 + pm_iyy(wempty, base_cg) + sum(pm_iyy(w, r) for w, r in pms)
    mass_t = W * LB / 1000
    iyy_t = iyy * SLUG * FT * FT / 1000
    # body frame (x forward, z down) offset from CG of a structural-frame point, metres
    def body_off(r):
        return (-(r[0] - cg[0]) * IN, -(r[2] - cg[2]) * IN)
    rpx, rpz = body_off(rp)
    th = pr.find('engine').find('thruster')
    thl = loc(th.find('location'))
    thx, thz = body_off(thl)

    aero = ac.find('aerodynamics')
    fnames = {}
    for fn in aero.iter('function'):
        fnames[fn.get('name')] = fn
    helper_scale = {'aero/function/kCDge': 1.0, 'aero/function/kCLge': 1.0,
                    'aero/function/velocity-induced-fps': FT, 'aero/function/qbar-induced-psf': PSF / 1000}
    axis_scale = {'DRAG': LBF / 1000, 'LIFT': LBF / 1000, 'PITCH': LBF * FT / 1000}
    helpers = [fn for fn in aero.findall('function')]
    for fn in helpers:
        n = fn.get('name')
        if n not in helper_scale:
            raise SystemExit(f'unhandled helper function {n}')
        lname = 'fn_' + lean_name(n)
        body = g.comp(next(c for c in fn if c.tag != 'description'), helper_scale[n])
        g.fn_out[n] = (lname, helper_scale[n])
        g.fn_defs.append(f'def {lname} (e : AeroIn) : Fx :=\n  {body}')
    axis_terms = {}
    for ax in aero.findall('axis'):
        an = ax.get('name')
        if an not in axis_scale:
            continue   # lateral axes: out of scope for the longitudinal model
        names = []
        for fn in ax.findall('function'):
            n = fn.get('name')
            lname = 'f_' + lean_name(n)
            body = g.comp(next(c for c in fn if c.tag != 'description'), axis_scale[an])
            g.fn_out[n] = (lname, axis_scale[an])
            g.fn_defs.append(f'/-- {n}: {fn.find("description").text.strip()} -/\ndef {lname} (e : AeroIn) : Fx :=\n  {body}')
            names.append(lname)
        axis_terms[an] = names
    alim = aero.find('alphalimits')
    hyst = aero.find('hysteresis_limits')

    pt = {t.get('name'): t for t in prop.findall('table')}
    def prop_tab(n):
        el = pt[n]
        data = [[float(t) for t in ln.split()] for ln in el.find('tableData').text.strip().splitlines() if ln.strip()]
        return f'{{ xs := #{[raw(r[0]) for r in data]}, ys := #{[raw(r[1]) for r in data]} }}'
    D = float(prop.find('diameter').text) * IN
    ixx_prop = float(prop.find('ixx').text) * SLUG * FT * FT
    p_factor = float(th.find('p_factor').text)

    def ev(tag, default):
        e = eng.find(tag)
        return float(e.text) if e is not None else default
    INHG = 3386.389
    minmp, maxmp = ev('minmp', 6.5) * INHG, min(ev('maxmp', 28.5), 29.9) * INHG
    disp = ev('displacement', 360) * IN ** 3
    idle, maxrpm = ev('idlerpm', 600), ev('maxrpm', 2800)
    stroke = 4.375
    peak_mps, std_p = 100.0, 101320.73
    rated_mps = maxrpm * stroke / 360
    ze = peak_mps / rated_mps
    z_air = std_p * ze / maxmp - ze
    z_thr = (peak_mps / ((idle * stroke) / 360)) * (std_p / minmp - 1) - z_air
    isfc = ev('bsfc', 0.32)
    mix_eff = [(0.05, 0.0), (0.05137, 0.00862), (0.05179, 0.21552), (0.05430, 0.48276), (0.05842, 0.70690),
               (0.06312, 0.83621), (0.06942, 0.93103), (0.07786, 1.0), (0.08845, 1.0), (0.09270, 0.98276),
               (0.10120, 0.93103), (0.11455, 0.72414), (0.12158, 0.45690), (0.12435, 0.23276), (0.125, 0.0)]

    Rg = 6356766.0
    atm_rows = []
    for i in range(0, 161):
        h = 50.0 * i
        hg = Rg * h / (Rg + h)
        T = 288.15 - 0.0065 * hg
        Rair = 287.053 * (1 - 3.2e-6)
        P = 101325.0 * (1 + 5.375e-6) * (T / 288.15) ** (9.80665 / (0.0065 * 287.053))
        rho = P / (Rair * T)
        a = math.sqrt(1.4 * 287.053 * T) * (1 - 1.6e-6)
        atm_rows.append((rho, P / 1000, T, a))

    L = []
    L.append('import Jsb.Math\n')
    L.append('/-! GENERATED by sysid/xml2lean.py from JSBSim c172p.xml, eng_io320.xml, prop_75in2f.xml. DO NOT EDIT.')
    L.append('    Units: m, s, rad, t, kN, kPa, kW, K, kg/m^3. Every `Fx` literal is a raw integer (value * 2^16). -/\n')
    L.append('namespace Jsb.C172\nopen Vibecheck\n')
    L.append('/-- Inputs of the generated aerodynamic functions (JSBSim property names in comments). -/')
    L.append('structure AeroIn where')
    inv = {f: p for p, (f, _, _) in FIELDS.items()}
    for f in sorted(g.fields_used):
        L.append(f'  {f} : Fx  -- {inv[f]}')
    L.append('')
    L.append('-- Geometry and mass properties')
    def c(nm, v, doc):
        L.append(f'/-- {doc} -/\ndef {nm} : Fx := {fx(v)}')
    c('wingArea', Sw * SQFT, 'wing area, m^2')
    c('wingSpan', bw * FT, 'wing span, m')
    c('wingChord', cw * FT, 'mean aerodynamic chord, m')
    c('massT', mass_t, 'aircraft mass at the XML loadout, t')
    c('iyyT', iyy_t, 'pitch inertia about the CG, t m^2')
    c('rpBodyX', rpx, 'aero reference point relative to the CG, body x forward, m')
    c('rpBodyZ', rpz, 'aero reference point relative to the CG, body z down, m')
    c('thrusterBodyX', thx, 'propeller hub relative to the CG, body x forward, m')
    c('thrusterBodyZ', thz, 'propeller hub relative to the CG, body z down, m')
    c('alphaHystLo', float(hyst.find('min').text), 'stall hysteresis lower limit, rad')
    c('alphaHystHi', float(hyst.find('max').text), 'stall hysteresis upper limit, rad')
    c('elevGain', float(ac.find('flight_control').find('.//aerosurface_scale/gain').text), 'rad per degree (JSBSim uses 0.01745)')
    L.append('/-- elevator travel in degrees at normalised command -1 (trailing edge up) and +1 -/')
    L.append(f'def elevTravelUp : Fx := {fx(28)}\ndef elevTravelDown : Fx := {fx(23)}\n')
    L.append('-- Tables')
    for _, t in g.tables:
        L.append(t)
    L.append('')
    L.append('-- Aerodynamic functions (forces kN, moments kN m)')
    for t in g.fn_defs:
        L.append(t)
    L.append('')
    for an, nm in (('DRAG', 'dragForce'), ('LIFT', 'liftForce'), ('PITCH', 'pitchMomentRP')):
        L.append(f'/-- sum of the {an} axis functions -/')
        L.append(f'def {nm} (e : AeroIn) : Fx :=\n  ' + ' + '.join(f'{n} e' for n in axis_terms[an]) + '\n')
    L.append('-- Propeller (FGPropeller fixed pitch)')
    c('propDiameter', D, 'propeller diameter, m')
    c('propD4', D ** 4, 'D^4, m^4')
    c('propD5', D ** 5, 'D^5, m^5')
    c('propArea', math.pi / 4 * D * D, 'disk area, m^2')
    c('propIxx', ixx_prop, 'propeller moment of inertia, kg m^2')
    L.append(f'def tblCT : Tbl1 := {prop_tab("C_THRUST")}')
    L.append(f'def tblCP : Tbl1 := {prop_tab("C_POWER")}')
    L.append(f'def tblCTMach : Tbl1 := {prop_tab("CT_MACH")}')
    L.append(f'def tblCPMach : Tbl1 := {prop_tab("CP_MACH")}\n')
    L.append('-- Piston engine (FGPiston with IO-320 data; defaults from FGPiston.cpp for unspecified items)')
    c('engDispL', disp * 1000, 'displacement, litres')
    c('engIdleRpm', idle, 'idle rpm')
    c('engStrokeIn', stroke, 'stroke, in (FGPiston default)')
    c('engPeakMps', peak_mps, 'peak mean piston speed, ft/s')
    c('engZeNum', peak_mps * 360 / stroke, 'ze = engZeNum / rpm')
    c('engZAirbox', z_air, 'air box impedance')
    c('engZThrottle', z_thr, 'throttle impedance constant')
    c('engVolEff', 0.85, 'volumetric efficiency (default)')
    c('engCompRatio', 8.5, 'compression ratio (default)')
    c('engIsfc', isfc, 'lb/hp/hr')
    c('engStaticFriction', 1.5, 'hp (default)')
    c('engFmepDynamic', 18.4, 'kPa per (m/s) of mean piston speed (default 18400 Pa)')
    c('engFmepStatic', 46.5, 'kPa (default 46500 Pa)')
    L.append(f'def tblMixEff : Tbl1 := {{ xs := #{[raw(a) for a, _ in mix_eff]}, ys := #{[raw(b) for _, b in mix_eff]} }}\n')
    L.append('-- Standard atmosphere, 50 m spacing from 0 m: (rho kg/m^3, p kPa, T K, a m/s)')
    L.append('def atmRho : Array Int := #' + str([raw(r[0]) for r in atm_rows]))
    L.append('def atmP : Array Int := #' + str([raw(r[1]) for r in atm_rows]))
    L.append('def atmT : Array Int := #' + str([raw(r[2]) for r in atm_rows]))
    L.append('def atmA : Array Int := #' + str([raw(r[3]) for r in atm_rows]) + '\n')
    L.append('-- Gravity at latitude 0 (WGS84 with J2; g(h) = g0 - h / (1000 gravScaleHKm)) and Earth rotation')
    Re, Om, g0 = 6378137.0, 7.292115e-5, 9.81420
    c('gravity0', g0, 'm/s^2 at h = 0')
    c('gravScaleHKm', Re / (2 * g0) / 1000, 'km; dg/dh = 1 / (1000 * gravScaleHKm) per m')
    c('earthRadiusKm', Re / 1000, 'km')
    c('omegaInv2', 1 / (2 * Om), 's; 1 / (2 * earth rate)')
    c('omega2R0', Om * Om * Re, 'm/s^2; centrifugal acceleration at the equator')
    L.append('\nend Jsb.C172')
    open(out, 'w').write('\n'.join(L) + '\n')
    print(f'wrote {out}: mass {mass_t*1000:.3f} kg, CG {[round(v*IN,5) for v in cg]} m, Iyy {iyy_t*1000:.3f} kg m^2, '
          f'rp body ({rpx:.4f},{rpz:.4f}) thruster body ({thx:.4f},{thz:.4f}) fields {sorted(g.fields_used)}')

main()
