import jsbsim, math
def mk():
    fdm = jsbsim.FGFDMExec(None); fdm.set_debug_level(0); fdm.load_model('c172p')
    fdm['ic/h-sl-ft']=1500; fdm['ic/terrain-elevation-ft']=0; fdm['ic/vc-kts']=90; fdm['ic/psi-true-deg']=90
    fdm.set_dt(1/128); fdm.run_ic(); fdm['propulsion/set-running']=-1
    fdm['fcs/throttle-cmd-norm']=0.7; fdm['fcs/mixture-cmd-norm']=0.9
    return fdm
for cmd in [-0.3, 0.0, 0.3]:
    fdm=mk(); fdm['fcs/elevator-cmd-norm']=cmd
    for i in range(128*2): fdm.run()
    print(cmd, 'theta', round(fdm['attitude/theta-deg'],1), 'q', round(fdm['velocities/q-rad_sec'],3), 'elevpos', round(fdm['fcs/elevator-pos-norm'],3), round(fdm['fcs/elevator-pos-rad'],3))
fdm=mk()
for p in fdm.query_property_catalog('distance-from-start').split('\n')[:6]: print(p)
for p in fdm.query_property_catalog('ground').split('\n')[:8]: print(p)
