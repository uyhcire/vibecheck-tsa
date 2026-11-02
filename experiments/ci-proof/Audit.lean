import ExpProofs.CiProof.StaticBox
import ExpProofs.CiProof.StepLyap
import Ci.proof.BandNext

/-! Axiom audit of the theorems named in README.md. Run: `lake env lean Audit.lean`. -/

#print axioms ExpProofs.CiProof.step_identity
#print axioms ExpProofs.CiProof.step_decrease
#print axioms ExpProofs.CiProof.recentre_le
#print axioms ExpProofs.CiProof.compose_steps
#print axioms ExpProofs.CiProof.contract_step
#print axioms ExpProofs.CiProof.tInvariant_of_lyap
#print axioms ExpProofs.CiProof.inT_next_of_lyap
#print axioms ExpProofs.CiProof.Skel.P_psd
#print axioms ExpProofs.CiProof.Skel.bridge_in
#print axioms ExpProofs.CiProof.Skel.bridge_out
#print axioms ExpProofs.CiProof.Skel.static_box
#print axioms ExpProofs.CiProof.Skel.tInvariant_of_dynamics
#print axioms ExpProofs.CiProof.Skel.tInvariant_of_fast_enc
#print axioms Ci.Goals.tSafe_of_tInvariant
#print axioms Ci.Proof.SafeIv.tick_safe_climb
#print axioms Ci.Proof.SafeIv.tick_band_h
#print axioms Ci.Proof.SafeIv.band_next
#print axioms Ci.Proof.tInvariant_of_tickInT
#print axioms Ci.Proof.s1000_in
#print axioms Ci.Proof.s1000_fast_out
