// JSBSim 1.3.3 c172p state dump for JsbExact; include before any other JSBSim header (it makes private members public).
#ifndef JSBX_EXPORT_STATE_HPP
#define JSBX_EXPORT_STATE_HPP
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstring>
#include <deque>
#include <fstream>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#define private public
#define protected public
#include "FGFDMExec.h"
#include "models/FGPropagate.h"
#include "models/FGAccelerations.h"
#include "models/FGAerodynamics.h"
#include "models/FGAuxiliary.h"
#include "models/FGMassBalance.h"
#include "models/FGPropulsion.h"
#include "models/FGAircraft.h"
#include "models/FGInertial.h"
#include "models/FGFCS.h"
#include "models/FGGroundReactions.h"
#include "models/FGLGear.h"
#include "models/atmosphere/FGWinds.h"
#include "models/FGAtmosphere.h"
#include "models/atmosphere/FGStandardAtmosphere.h"
#include "models/propulsion/FGPiston.h"
#include "models/propulsion/FGPropeller.h"
#include "models/propulsion/FGTank.h"
#include "math/FGTable.h"
#include "input_output/FGGroundCallback.h"
#undef private
#undef protected

namespace jsbx {

struct Rec {
  std::vector<std::string> names;
  std::vector<double> vals;
  void add(const std::string& n, double v) { names.push_back(n); vals.push_back(v); }
  void v3(const std::string& n, const JSBSim::FGColumnVector3& v) { for (int i = 1; i <= 3; i++) add(n + std::to_string(i), v(i)); }
  void q4(const std::string& n, const JSBSim::FGQuaternion& q) { for (int i = 1; i <= 4; i++) add(n + std::to_string(i), q(i)); }
  void m9(const std::string& n, const JSBSim::FGMatrix33& m) {
    for (int r = 1; r <= 3; r++) for (int c = 1; c <= 3; c++) add(n + std::to_string(r) + std::to_string(c), m(r, c));
  }
};

// The field order is the interface: CityJsb.dumpNames mirrors it.
inline void dump_state(JSBSim::FGFDMExec& fdm, Rec& r) {
  using namespace JSBSim;
  auto P = fdm.GetPropagate(); auto A = fdm.GetAccelerations(); auto Ae = fdm.GetAerodynamics();
  auto MB = fdm.GetMassBalance(); auto Pr = fdm.GetPropulsion(); auto Ax = fdm.GetAuxiliary();
  auto& V = P->VState;
  auto eng = static_cast<FGPiston*>(Pr->GetEngine(0).get());
  auto prop = static_cast<FGPropeller*>(eng->GetThruster());
  r.add("time", fdm.GetSimTime());
  r.q4("qi", V.qAttitudeECI); r.q4("qdot", V.vQtrndot);
  r.v3("pqri", V.vPQRi); r.v3("ri", V.vInertialPosition); r.v3("vi", V.vInertialVelocity);
  r.v3("vih0_", V.dqInertialVelocity[0]); r.v3("vih1_", V.dqInertialVelocity[1]);
  r.v3("aih0_", V.dqUVWidot[0]);
  r.add("epa", P->epa);
  r.v3("pqridot", A->vPQRidot); r.v3("uvwidot", A->vUVWidot); r.v3("uvwdot", A->vUVWdot);
  r.add("stall", Ae->stall_hyst);
  r.v3("cg", MB->vXYZcg);
  r.add("tank0", Pr->GetTank(0)->Contents); r.add("tank1", Pr->GetTank(1)->Contents);
  r.add("tmap", eng->TMAP); r.add("running", eng->Running ? 1.0 : 0.0); r.add("fuelflow", eng->FuelFlowRate);
  r.add("starved", eng->Starved ? 1.0 : 0.0); r.add("rpm", prop->RPM);
  r.v3("actxyz", prop->vActingXYZn);
  r.v3("lastcg", MB->vLastXYZcg);
  auto GR = fdm.GetGroundReactions();
  for (int i = 0; i < GR->GetNumGearUnits(); i++) {
    auto g = GR->GetGearUnit(i);
    std::string p = "g" + std::to_string(i) + "_";
    r.add(p + "wow", g->WOW ? 1.0 : 0.0);
    for (int j = 0; j < 3; j++) r.add(p + "lm" + std::to_string(j), g->LMultiplier[j].value);
    r.add(p + "slip", g->WheelSlip); r.add(p + "steer", g->SteerAngle);
    r.v3(p + "act", g->vActingXYZn); r.m9(p + "mT", g->mT);
    r.add(p + "d_fz", g->vFn(3));
  }
  r.v3("d_ffric", A->vFrictionForces);
  r.v3("d_wind", fdm.GetWinds()->vTotalWindNED); r.v3("d_aerouvw", Ax->vAeroUVW);
  r.v3("uvw", V.vUVW); r.v3("pqr", V.vPQR); r.v3("ecef", V.vLocation.mECLoc);
  r.add("phi", P->GetEuler(1)); r.add("theta", P->GetEuler(2)); r.add("psi", P->GetEuler(3));
  r.add("hsl", P->GetAltitudeASL()); r.add("lat", V.vLocation.GetGeodLatitudeRad()); r.add("lon", V.vLocation.GetLongitude());
  r.v3("vned", P->vVel);
  r.v3("d_faero", Ae->vForces); r.v3("d_maero", Ae->vMoments);
  r.v3("d_fprop", Pr->vForces); r.v3("d_mprop", Pr->vMoments);
  r.v3("d_fgear", fdm.GetGroundReactions()->GetForces()); r.v3("d_mgear", fdm.GetGroundReactions()->GetMoments());
  r.v3("d_ftot", fdm.GetAircraft()->vForces); r.v3("d_mtot", fdm.GetAircraft()->vMoments);
  r.v3("d_fnat", Ae->vFnative); r.v3("d_mmrc", Ae->vMomentsMRC);
  r.add("d_alpha", Ax->alpha); r.add("d_beta", Ax->beta); r.add("d_adot", Ax->adot); r.add("d_qbar", Ax->qbar);
  r.add("d_vt", Ax->Vt); r.add("d_mach", Ax->Mach); r.add("d_pt", Ax->pt); r.add("d_hmac", Ax->hoverbmac);
  auto At = fdm.GetAtmosphere();
  r.add("d_rho", At->Density); r.add("d_p", At->Pressure); r.add("d_t", At->Temperature); r.add("d_a", At->Soundspeed);
  r.v3("d_grav", fdm.GetInertial()->vGravAccel);
  r.add("d_thrust", prop->Thrust); r.add("d_hp", eng->HP); r.add("d_ihp", eng->IndicatedHorsePower);
  r.add("d_mdotair", eng->m_dot_air); r.add("d_preq", prop->PowerRequired); r.add("d_vind", prop->Vinduced);
  r.add("d_mass", MB->Mass); r.m9("d_J", MB->mJ); r.m9("d_Jinv", MB->mJinv);
  r.add("d_agl", P->GetDistanceAGL());
  auto F = fdm.GetFCS();
  r.add("d_de", F->GetDePos(0)); r.add("d_da", F->GetDaLPos(0)); r.add("d_dr", F->GetDrPos(0)); r.add("d_df", F->GetDfPos(1));
}

inline std::vector<double> export_state(JSBSim::FGFDMExec& fdm) {
  Rec r;
  dump_state(fdm, r);
  return r.vals;
}

inline std::vector<std::string> export_state_names(JSBSim::FGFDMExec& fdm) {
  Rec r;
  dump_state(fdm, r);
  return r.names;
}

class DriftLog {
 public:
  explicit DriftLog(const std::string& prefix) : prefix_(prefix), bin_(std::fopen((prefix + ".bin").c_str(), "wb")) {}
  ~DriftLog() { if (bin_) std::fclose(bin_); }
  DriftLog(const DriftLog&) = delete;
  DriftLog& operator=(const DriftLog&) = delete;
  bool ok() const { return bin_ != nullptr; }

  // A record with a new `ep` starts a new episode (the check re-imports there); `stop` marks a final record.
  void record(JSBSim::FGFDMExec& fdm, double elev, double ail, double rud, double thr, double mix, double brkL,
              double brkR, int ep = 0, bool stop = false) {
    Rec r;
    r.add("ep", ep); r.add("k", static_cast<double>(k_++)); r.add("stop", stop ? 1.0 : 0.0);
    r.add("u_elev", elev); r.add("u_ail", ail); r.add("u_rud", rud); r.add("u_thr", thr); r.add("u_mix", mix);
    r.add("u_brkL", brkL); r.add("u_brkR", brkR);
    dump_state(fdm, r);
    if (!named_) {
      std::ofstream nf(prefix_ + ".names");
      for (auto& n : r.names) nf << n << "\n";
      named_ = true;
    }
    if (bin_) std::fwrite(r.vals.data(), sizeof(double), r.vals.size(), bin_);
  }

 private:
  std::string prefix_;
  std::FILE* bin_;
  bool named_ = false;
  long k_ = 0;
};

}  // namespace jsbx
#endif
