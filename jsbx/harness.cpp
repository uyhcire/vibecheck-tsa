// Lockstep harness: drives JSBSim 1.3.3's c172p and dumps the complete step state (incl. hidden state).
#include <cmath>
#include <cstdio>
#include <cstdint>
#include <cstring>
#include <deque>
#include <vector>
#include <string>
#include <map>
#include <memory>
#include <random>
#include <iostream>
#include <sstream>
#include <fstream>
#include <functional>
#include <algorithm>
#include <chrono>
#include "export_state.hpp"

using namespace JSBSim;

using jsbx::Rec;

static std::string hexd(double d) { uint64_t u; std::memcpy(&u, &d, 8); char b[32]; snprintf(b, 32, "\"0x%016llx\"", (unsigned long long)u); return b; }

struct Cfg {
  std::ostringstream o; bool first = true;
  void key(const std::string& k) { o << (first ? "" : ",\n") << "\"" << k << "\": "; first = false; }
  void d(const std::string& k, double v) { key(k); o << hexd(v); }
  void arr(const std::string& k, const std::vector<double>& v) {
    key(k); o << "["; for (size_t i = 0; i < v.size(); i++) o << (i ? "," : "") << hexd(v[i]); o << "]";
  }
  void v3(const std::string& k, const FGColumnVector3& v) { arr(k, {v(1), v(2), v(3)}); }
  void m9(const std::string& k, const FGMatrix33& m) {
    std::vector<double> v; for (int r = 1; r <= 3; r++) for (int c = 1; c <= 3; c++) v.push_back(m(r, c)); arr(k, v);
  }
  void table(const std::string& k, FGTable* t) {
    if (!t) { key(k); o << "null"; return; }
    key(k); o << "{\"rows\": " << t->nRows << ", \"cols\": " << t->nCols << ", \"data\": [";
    for (size_t i = 0; i < t->Data.size(); i++) o << (i ? "," : "") << hexd(t->Data[i]);
    o << "]}";
  }
};

static void dumpConfig(FGFDMExec& fdm, const std::string& path) {
  Cfg c;
  auto Ac = fdm.GetAircraft(); auto Ae = fdm.GetAerodynamics(); auto MB = fdm.GetMassBalance();
  auto Pr = fdm.GetPropulsion(); auto In = fdm.GetInertial();
  auto At = std::static_pointer_cast<FGStandardAtmosphere>(fdm.GetAtmosphere());
  auto eng = static_cast<FGPiston*>(Pr->GetEngine(0).get());
  auto prop = static_cast<FGPropeller*>(eng->GetThruster());
  c.d("dt", fdm.GetDeltaT());
  c.d("Sw", Ac->WingArea); c.d("bw", Ac->WingSpan); c.d("cbar", Ac->cbar); c.d("incidence", Ac->WingIncidence);
  c.v3("XYZrp", Ac->vXYZrp); c.v3("XYZvrp", Ac->vXYZvrp); c.v3("XYZep", Ac->vXYZep);
  c.d("alphaclmax", Ae->alphaclmax); c.d("hystmax", Ae->alphahystmax); c.d("hystmin", Ae->alphahystmin);
  c.d("emptywt", MB->EmptyWeight); c.v3("baseCG", MB->vbaseXYZcg); c.m9("baseJ", MB->baseJ);
  std::vector<double> pmw, pmloc, pmJ;
  for (auto pm : MB->PointMasses) {
    pmw.push_back(pm->Weight);
    for (int i = 1; i <= 3; i++) pmloc.push_back(pm->Location(i));
    for (int r = 1; r <= 3; r++) for (int k = 1; k <= 3; k++) pmJ.push_back(pm->mPMInertia(r, k));
  }
  c.arr("pmWeight", pmw); c.arr("pmLoc", pmloc); c.arr("pmJ", pmJ);
  std::vector<double> tk;
  for (unsigned i = 0; i < Pr->GetNumTanks(); i++) {
    auto t = Pr->GetTank(i);
    std::vector<double> v = {t->vXYZ(1), t->vXYZ(2), t->vXYZ(3), t->vXYZ_drain(1), t->vXYZ_drain(2), t->vXYZ_drain(3),
                             t->Capacity, t->GetUnusable(), t->Ixx, t->Iyy, t->Izz, t->Radius, (double)t->GetPriority(),
                             t->Selected ? 1.0 : 0.0, t->Temperature, t->ExternalFlow};
    c.arr("tank" + std::to_string(i), v);
  }
  c.d("GM", In->GM); c.d("J2", In->J2); c.d("a", In->a); c.d("b", In->b); c.v3("omega", In->vOmegaPlanet);
  c.d("terrain", static_cast<FGDefaultGroundCallback*>(In->GroundCallback.get())->mTerrainElevation);
  c.arr("pressBreak", At->PressureBreakpoints); c.arr("lapse", At->LapseRates);
  c.table("stdTemp", &At->StdAtmosTemperatureTable); c.table("maxVapor", &At->MaxVaporMassFraction);
  c.d("Reng", At->Reng); c.d("SLpressure", At->SLpressure); c.d("SLdensity", At->SLdensity);
  c.d("SLtemperature", At->SLtemperature); c.d("tbias", At->TemperatureBias); c.d("tgrad", At->TemperatureDeltaGradient);
  c.d("fadeAlt", At->GradientFadeoutAltitude); c.d("vapor", At->VaporMassFraction);
  c.d("StdDaySLsoundspeed", At->StdDaySLsoundspeed);
  c.d("R_air", eng->R_air); c.d("MPLag", eng->ManifoldPressureLag); c.d("dispSI", eng->displacement_SI);
  c.d("MaxHP", eng->MaxHP); c.d("SFHP", eng->StaticFriction_HP); c.d("SparkFailDrop", eng->SparkFailDrop);
  c.d("Cycles", eng->Cycles); c.d("IdleRPM", eng->IdleRPM); c.d("Stroke", eng->Stroke);
  c.d("CompressionRatio", eng->CompressionRatio); c.d("Z_airbox", eng->Z_airbox); c.d("Z_throttle", eng->Z_throttle);
  c.d("PeakMPS", eng->PeakMeanPistonSpeed_fps); c.d("RamAir", eng->Ram_Air_Factor); c.d("VE", eng->volumetric_efficiency);
  c.d("FMEPDynamic", eng->FMEPDynamic); c.d("FMEPStatic", eng->FMEPStatic); c.d("ISFC", eng->ISFC);
  c.d("Magnetos", eng->Magnetos); c.d("Boosted", eng->Boosted); c.d("BoostLossFactor", eng->BoostLossFactor);
  c.d("StarterTorque", eng->StarterTorque); c.d("StarterRPM", eng->StarterRPM); c.d("StarterGain", eng->StarterGain);
  c.d("FuelDensity", eng->FuelDensity); c.d("Starter", eng->Starter);
  c.table("mixEff", eng->Mixture_Efficiency_Correlation);
  c.d("Diameter", prop->Diameter); c.d("D4", prop->D4); c.d("D5", prop->D5); c.d("propIxx", prop->Ixx);
  c.d("CtFactor", prop->CtFactor); c.d("CpFactor", prop->CpFactor); c.d("PFactor", prop->P_Factor);
  c.d("Sense", prop->Sense); c.d("SenseMult", prop->Sense_multiplier); c.d("GearRatio", prop->GearRatio);
  c.d("MaxPitch", prop->MaxPitch); c.d("MinPitch", prop->MinPitch);
  c.v3("propXYZ", prop->vXYZn); c.m9("propT", prop->mT); c.d("propTtype", prop->ttype);
  c.table("cThrust", prop->cThrust); c.table("cPower", prop->cPower);
  c.table("CtMach", prop->CtMach); c.table("CpMach", prop->CpMach);
  auto GR = fdm.GetGroundReactions();
  c.d("staticFFactor", GR->staticFFactor); c.d("rollingFFactor", GR->rollingFFactor);
  c.d("maximumForce", GR->maximumForce); c.d("bumpiness", GR->bumpiness); c.d("isSolid", GR->isSolid);
  for (int i = 0; i < GR->GetNumGearUnits(); i++) {
    auto g = GR->GetGearUnit(i);
    std::vector<double> v = {(double)g->eContactType, g->vXYZn(1), g->vXYZn(2), g->vXYZn(3), g->kSpring, g->bDamp,
      g->bDampRebound, (double)g->eDampType, (double)g->eDampTypeRebound, g->staticFCoeff, g->dynamicFCoeff,
      g->rollingFCoeff, g->maxSteerAngle, g->Castered ? 1.0 : 0.0, (double)g->eBrakeGrp, g->isRetractable ? 1.0 : 0.0,
      g->Stiffness, g->Shape, g->Peak, g->Curvature, g->ForceY_Table ? 1.0 : 0.0, g->fStrutForce ? 1.0 : 0.0};
    for (int r = 1; r <= 3; r++) for (int k = 1; k <= 3; k++) v.push_back(g->mTGear(r, k));
    c.arr("gear" + std::to_string(i), v);
  }
  c.m9("Ts2b", FGLGear::Ts2b); c.m9("Tb2s", FGLGear::Tb2s);
  c.d("hasCtRPM", prop->cThrustRPM != nullptr); c.d("hasCpRPM", prop->cPowerRPM != nullptr);
  c.d("EarthRadius", FGStandardAtmosphere::EarthRadius); c.d("g0", FGAtmosphere::g0); c.d("Rdry", FGStandardAtmosphere::Rdry);
  c.d("SHRatio", FGAtmosphere::SHRatio); c.d("StdDaySLpressure", FGAtmosphere::StdDaySLpressure);
  c.d("psftopa", FGJSBBase::psftopa); c.d("hptoftlbssec", FGJSBBase::hptoftlbssec); c.d("fttom", FGJSBBase::fttom);
  c.d("inchtoft", FGJSBBase::inchtoft); c.d("lbtoslug", FGJSBBase::lbtoslug); c.d("slugtolb", FGJSBBase::slugtolb);
  c.d("radtodeg", FGJSBBase::radtodeg); c.d("inhgtopa", FGJSBBase::inhgtopa);
  std::ofstream f(path); f << "{\n" << c.o.str() << "\n}\n";
}

struct Rng {
  std::mt19937_64 g;
  explicit Rng(uint64_t s) : g(s) {}
  double uni(double a, double b) { return std::uniform_real_distribution<double>(a, b)(g); }
  int ri(int a, int b) { return std::uniform_int_distribution<int>(a, b)(g); }
};

static double clampd(double x, double lo, double hi) { return std::max(lo, std::min(hi, x)); }

static void setupPaths(FGFDMExec& fdm, const std::string& root) {
  fdm.SetRootDir(SGPath(root));
  fdm.SetOutputPath(SGPath("."));
  fdm.SetEnginePath(SGPath("engine"));
  fdm.SetAircraftPath(SGPath("aircraft"));
  fdm.SetSystemsPath(SGPath("systems"));
}

int main(int argc, char** argv) {
  if (argc < 7) {
    fprintf(stderr, "usage: harness ROOT OUT MODE(level|rud0|bank|takeoff|land|bench) EPISODES STEPS SEED [freeze]\n");
    return 2;
  }
  std::string root = argv[1], out = argv[2], mode = argv[3];
  int nep = atoi(argv[4]), nsteps = atoi(argv[5]);
  Rng rng(strtoull(argv[6], nullptr, 10));
  // "freeze": propulsion/fuel_freeze on after RunIC (tanks never drain; JsbExact.step with fuelFreeze).
  bool freeze = argc > 7 && std::string(argv[7]) == "freeze";
  FILE* fb = fopen((out + ".bin").c_str(), "wb");
  FILE* fi = fopen((out + ".ic").c_str(), "w");
  size_t nfields = 0; long total = 0;
  for (int ep = 0; ep < nep; ep++) {
    FGJSBBase::debug_lvl = 0;
    FGFDMExec fdm(nullptr, nullptr);
    setupPaths(fdm, root);
    fdm.SetDebugLevel(0);
    fdm.LoadModel("c172p");
    bool ground = mode == "takeoff" || mode == "land";
    double h0 = rng.uni(2000, 4000), vc0 = rng.uni(65, 110), gam0 = 0;
    if (mode == "takeoff") { h0 = 4.9; vc0 = 0; }
    if (mode == "land") { h0 = rng.uni(40, 120); vc0 = rng.uni(58, 72); gam0 = -3; }
    const char* hprop = ground ? "ic/h-agl-ft" : "ic/h-sl-ft";
    fdm.SetPropertyValue("ic/terrain-elevation-ft", 0);
    fdm.SetPropertyValue(hprop, h0);
    fdm.SetPropertyValue("ic/vc-kts", vc0);
    fdm.SetPropertyValue("ic/gamma-deg", gam0);
    fdm.SetPropertyValue("ic/psi-true-deg", 90);
    fdm.Setdt(1.0 / 128);
    fdm.RunIC();
    fdm.SetPropertyValue("propulsion/set-running", -1);
    if (freeze) fdm.SetPropertyValue("propulsion/fuel_freeze", 1);
    fdm.SetPropertyValue("fcs/mixture-cmd-norm", 0.9);
    fprintf(fi, "%d %a %a %a %s\n", ep, h0, vc0, gam0, hprop);
    if (ep == 0) dumpConfig(fdm, out + ".cfg.json");
    double elev = 0, stick = 0, thr = 0, phit = 0, rudoff = 0, thetat = 0.03;
    int hold = 0, bhold = 0, rhold = 0;
    bool aggressive = ep % 3 == 0;
    double brk = 0, vrot = rng.uni(50, 62), thrTO = rng.uni(0.8, 1.0), thetaTO = rng.uni(0.08, 0.16), brkLand = rng.uni(0.3, 1.0);
    double psi0 = 0.5 * M_PI, tWow = -1;
    int k;
    for (k = 0; k < nsteps; k++) {
      auto P = fdm.GetPropagate(); auto Ax = fdm.GetAuxiliary();
      double phi = P->GetEuler(1), theta = P->GetEuler(2), p = P->VState.vPQR(1), q = P->VState.vPQR(2),
             r = P->VState.vPQR(3), beta = Ax->beta, h = P->GetAltitudeASL() * 0.3048, vt = Ax->Vt * 0.3048;
      double lim = mode == "bank" ? 60 : 35;
      bool stop = std::fabs(phi) > lim * M_PI / 180 || h < 150 || vt > 80 || std::fabs(theta) > M_PI / 3 || vt < 20;
      double agl = P->GetDistanceAGL(), t = k / 128.0, psi = P->GetEuler(3);
      bool wow = fdm.GetGroundReactions()->GetWOW();
      if (ground) stop = std::fabs(phi) > M_PI / 4 || agl > 300 || vt > 80 || std::fabs(theta) > M_PI / 4
                         || (mode == "land" && tWow >= 0 && vt < 1.0);
      if (k % 8 == 0) {   // 1/16 s pilot tick
        if (hold-- <= 0) {
          hold = rng.ri(8, 64);
          double span = aggressive ? 1.0 : 0.5;
          stick = rng.uni(-span, span);
          int c = rng.ri(0, 3);
          thr = c == 0 ? 0.0 : c == 1 ? 1.0 : rng.uni(0, 1);
          thetat = rng.uni(-0.05, 0.12);
        }
        if (ground) {
          if (rhold-- <= 0) { rhold = rng.ri(16, 64); rudoff = rng.ri(0, 2) == 0 ? rng.uni(-0.3, 0.3) : 0.0; }
          double s;
          if (mode == "takeoff") {
            thr = t < 2 ? 0.0 : thrTO;
            brk = t < 4 ? 1.0 : 0.0;
            s = vt < vrot * 0.5144 ? 0.0 : clampd(2.0 * (thetaTO - theta) - 0.6 * q, -1, 1);
          } else {
            if (wow && tWow < 0) tWow = t;
            thr = agl > 20 ? 0.25 : 0.0;
            brk = tWow >= 0 && t > tWow + 1.5 ? brkLand : 0.0;
            double tht = agl > 15 ? -0.02 : 0.07;
            s = tWow >= 0 ? 0.0 : clampd(2.0 * (tht - theta) - 0.6 * q, -1, 1);
          }
          elev += clampd(s - elev, -0.125, 0.125);
        } else if (mode == "bank") {
          if (bhold-- <= 0) { bhold = rng.ri(32, 160); phit = rng.uni(-45, 45) * M_PI / 180; }
          if (rhold-- <= 0) { rhold = rng.ri(16, 96); rudoff = rng.ri(0, 2) == 0 ? rng.uni(-0.4, 0.4) : 0.0; }
          double s = clampd(2.0 * (thetat - theta) - 0.6 * q + 0.15 * std::fabs(phi), -1, 1);
          elev += clampd(s - elev, -0.125, 0.125);
        } else {
          elev += clampd(stick - elev, -0.125, 0.125);
        }
      }
      double ail, rud;
      if (ground) {
        ail = clampd(-3.0 * phi - 1.5 * p, -1, 1);
        rud = clampd(2.0 * (psi - psi0) + 1.0 * r + rudoff, -1, 1);
      } else if (mode == "bank") {
        ail = clampd(-3.0 * (phi - phit) - 1.5 * p, -1, 1);
        rud = clampd(3.0 * r - 4.0 * beta + rudoff, -1, 1);
      } else {
        ail = clampd(-8.0 * phi - 2.0 * p, -1, 1);
        rud = mode == "rud0" ? 0.0 : clampd(-3.0 * r + 4.0 * beta, -1, 1);
      }
      if (mode == "bench") {
        fdm.SetPropertyValue("fcs/throttle-cmd-norm", 0.7);
        auto t0 = std::chrono::steady_clock::now();
        for (int i = 0; i < nsteps; i++) fdm.Run();
        double us = std::chrono::duration<double, std::micro>(std::chrono::steady_clock::now() - t0).count();
        fprintf(stderr, "FGFDMExec::Run: %.3f us/step over %d steps\n", us / nsteps, nsteps);
        return 0;
      }
      Rec rec;
      rec.add("ep", ep); rec.add("k", k); rec.add("stop", stop ? 1.0 : 0.0);
      rec.add("u_elev", -elev); rec.add("u_ail", ail); rec.add("u_rud", rud); rec.add("u_thr", thr); rec.add("u_mix", 0.9);
      rec.add("u_brkL", brk); rec.add("u_brkR", brk);
      jsbx::dump_state(fdm, rec);
      if (nfields == 0) {
        nfields = rec.vals.size();
        std::ofstream nf(out + ".names");
        for (auto& n : rec.names) nf << n << "\n";
      }
      fwrite(rec.vals.data(), sizeof(double), rec.vals.size(), fb);
      total++;
      if (stop) break;
      fdm.SetPropertyValue("fcs/elevator-cmd-norm", -elev);
      fdm.SetPropertyValue("fcs/throttle-cmd-norm", thr);
      fdm.SetPropertyValue("fcs/aileron-cmd-norm", ail);
      fdm.SetPropertyValue("fcs/rudder-cmd-norm", rud);
      fdm.SetPropertyValue("fcs/left-brake-cmd-norm", brk);
      fdm.SetPropertyValue("fcs/right-brake-cmd-norm", brk);
      fdm.Run();
    }
  }
  fclose(fb); fclose(fi);
  fprintf(stderr, "%d episodes, %ld records, %zu fields -> %s.bin\n", nep, total, nfields, out.c_str());
  return 0;
}
