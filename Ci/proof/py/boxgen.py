"""Rewrite TData.boxTab with provable cell boxes (see provbox.py) and add the slow-deviation bounds slowB (per 100 m
node interval, raw) that the static-fit proof certifies."""
import re
import provbox as pb
src = open("../TData.lean").read()
for ci in range(267):
    L, H, elo, ehi = pb.cellbox_prov(ci)
    vals = [int(v) for v in L + H] + [int(elo), int(ehi)]
    src = re.sub(rf"^def b{ci} : Array Int := #\[.*\]$", f"def b{ci} : Array Int := #[" + ", ".join(map(str, vals)) + "]", src, flags=re.M)
src = re.sub(r"/-- Bounding box of the set in each 10 m altitude cell.*?-/", "/-- Box of the set in each 10 m altitude cell from 10 m: 19 lows, 19 highs (x unused), then the integrator\nmemory eI's low and high. Built from the certified bounds `slowB` on the slow deviations, the table centre rows of the\ncell, the slaving gains and the fast tolerances, so the set's other conditions imply it (`static_box`). -/", src, flags=re.S)
if "def slowB" not in src:
    rows = ", ".join("#[" + ", ".join(map(str, b)) + "]" for b in pb.B)
    src = src.replace("end Ci.Proof.TData", f"/-- Certified bound (raw) on each slow deviation over each 100 m node interval: d_k² < slowB² whenever the slow\nquadratic check passes (LDLᵀ certificates in `Proofs/CiProof/StaticBox.lean`). -/\ndef slowB : Array (Array Int) := #[{rows}]\n\nend Ci.Proof.TData")
open("../TData.lean", "w").write(src)
print("ok")
