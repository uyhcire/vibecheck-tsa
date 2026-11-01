// Example host for the drift check: flies JSBSim's c172p with varied inputs and logs every frame with
// jsbx::DriftLog; `jsbdrift OUT` then steps JsbExact alongside. usage: drift_host ROOT OUT [SECONDS] [SEED]
#include "export_state.hpp"
#include <random>

int main(int argc, char** argv) {
  if (argc < 3) {
    std::fprintf(stderr, "usage: drift_host JSBSIM_ROOT OUT [SECONDS] [SEED]\n");
    return 2;
  }
  double seconds = argc > 3 ? std::atof(argv[3]) : 120.0;
  std::mt19937_64 rng(argc > 4 ? std::strtoull(argv[4], nullptr, 10) : 1);
  auto uni = [&](double a, double b) { return std::uniform_real_distribution<double>(a, b)(rng); };
  JSBSim::FGJSBBase::debug_lvl = 0;
  JSBSim::FGFDMExec fdm(nullptr, nullptr);
  fdm.SetRootDir(SGPath(argv[1]));
  fdm.SetAircraftPath(SGPath("aircraft"));
  fdm.SetEnginePath(SGPath("engine"));
  fdm.SetSystemsPath(SGPath("systems"));
  fdm.SetDebugLevel(0);
  if (!fdm.LoadModel("c172p")) return 1;
  fdm.SetPropertyValue("ic/terrain-elevation-ft", 0);
  fdm.SetPropertyValue("ic/h-sl-ft", 3000);
  fdm.SetPropertyValue("ic/vc-kts", 90);
  fdm.SetPropertyValue("ic/psi-true-deg", 90);
  fdm.Setdt(1.0 / 128);
  fdm.RunIC();
  fdm.SetPropertyValue("propulsion/set-running", -1);
  jsbx::DriftLog log(argv[2]);
  if (!log.ok()) return 1;
  double elev = 0, ail = 0, rud = 0, thr = 0.7;
  long frames = static_cast<long>(seconds * 128);
  for (long k = 0; k < frames; k++) {
    if (k % 128 == 0) { elev = uni(-0.3, 0.2); ail = uni(-0.3, 0.3); rud = uni(-0.2, 0.2); thr = uni(0.3, 1.0); }
    double phi = fdm.GetPropertyValue("attitude/phi-rad");
    double a = std::max(-1.0, std::min(1.0, ail - 1.5 * phi));
    log.record(fdm, elev, a, rud, thr, 0.9, 0, 0, 0, k + 1 == frames);
    fdm.SetPropertyValue("fcs/elevator-cmd-norm", elev);
    fdm.SetPropertyValue("fcs/aileron-cmd-norm", a);
    fdm.SetPropertyValue("fcs/rudder-cmd-norm", rud);
    fdm.SetPropertyValue("fcs/throttle-cmd-norm", thr);
    fdm.SetPropertyValue("fcs/mixture-cmd-norm", 0.9);
    fdm.Run();
  }
  return 0;
}
