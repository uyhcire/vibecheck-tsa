import Proofs.TermSound.Checks
import Spec.EndSets

/-!
# A proved safe region for the simplified point-mass aircraft, against the city spec's `Crash`

About the simplified point-mass model (`Proofs.TermSound`, exact reals), **not** the JSBSim aircraft: the airframe
is only assumed to lie within `e` of a rational point within `η` of the point-mass position, read in the map frame.
-/

namespace Proofs.SafeRegion

open Proofs.TermSound CitySafety CitySafety.EndSets JsbExact

noncomputable section

/-- The horizontal position of a map point as a complex number (east = re, north = im). -/
def horiz (q : Pt) : ℂ := ⟨(q.x : ℝ), (q.y : ℝ)⟩

def rH (z0 ztop : ℝ) : ℝ := (Rstar z0 + Rstar ztop) / 2

def δH (z0 m0 ztop : ℝ) : ℝ := (Rstar z0 - Rstar ztop) / 2 + m0 + kappa * (ztop - z0)

/-- **Map clearance for the helix** (over ℝ, margin `E`): every solid point lies below `ztop - E`, and a solid point
whose horizontal distance to `c0` is within `[r - δ - 2E, r + δ + 2E]` lies below `z0 - E`. -/
def HelixClear (M : CityMap) (c0 : ℂ) (z0 m0 ztop E : ℝ) : Prop :=
  ∀ q : Pt, Solid M q → (q.z : ℝ) < ztop - E ∧
    (rH z0 ztop - δH z0 m0 ztop - 2 * E ≤ ‖horiz q - c0‖ →
      ‖horiz q - c0‖ ≤ rH z0 ztop + δH z0 m0 ztop + 2 * E → (q.z : ℝ) < z0 - E)

/-- Within `η` per map axis. -/
def Near (η : ℝ) (s : St) (c : Pt) : Prop :=
  |(c.x : ℝ) - s.x| ≤ η ∧ |(c.y : ℝ) - s.y| ≤ η ∧ |(c.z : ℝ) - s.z| ≤ η

/-- `Helix.clear` over ℝ, for a rational box around a point near the point mass. -/
theorem helix_box_clear {M : CityMap} {c0 : ℂ} {z0 m0 ztop : ℝ} {e : ℚ} {η : ℝ} (hz0 : 0 ≤ z0)
    (hzt : ztop ≤ ZT) {s : St} (hs : DynH c0 z0 m0 ztop s) (hclr : HelixClear M c0 z0 m0 ztop (e + η))
    {c : Pt} (hc : Near η s c) : ∀ q, InBox e c q → ¬ Solid M q := by
  intro q hq hsol
  obtain ⟨h1, h2⟩ := hclr q hsol
  simp only [InBox] at hq
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hq
  have b1 : (c.x : ℝ) - e ≤ q.x := by exact_mod_cast a1
  have b2 : (q.x : ℝ) ≤ c.x + e := by exact_mod_cast a2
  have b3 : (c.y : ℝ) - e ≤ q.y := by exact_mod_cast a3
  have b4 : (q.y : ℝ) ≤ c.y + e := by exact_mod_cast a4
  have b5 : (c.z : ℝ) - e ≤ q.z := by exact_mod_cast a5
  obtain ⟨hx, hy, hz⟩ := hc
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  obtain ⟨hz1, -⟩ := abs_le.mp hz
  have hqz : s.z - (e + η) ≤ q.z := by linarith
  by_cases hlt : s.z < ztop
  · have hconf := helix_conf hz0 hzt hs hlt
    simp only at hconf
    obtain ⟨lo, hi, hz0s⟩ := hconf
    have hd : ‖horiz q - pos s‖ ≤ 2 * (e + η) := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have er : (horiz q - pos s).re = (q.x : ℝ) - s.x := by simp [horiz, pos]
      have ei : (horiz q - pos s).im = (q.y : ℝ) - s.y := by simp [horiz, pos]
      rw [er, ei]
      have := abs_le.mpr (show -((e : ℝ) + η) ≤ (q.x : ℝ) - s.x ∧ (q.x : ℝ) - s.x ≤ e + η from ⟨by linarith, by linarith⟩)
      have := abs_le.mpr (show -((e : ℝ) + η) ≤ (q.y : ℝ) - s.y ∧ (q.y : ℝ) - s.y ≤ e + η from ⟨by linarith, by linarith⟩)
      linarith
    have t1 := norm_sub_le_norm_sub_add_norm_sub (horiz q) (pos s) c0
    have t2 := norm_sub_le_norm_sub_add_norm_sub (pos s) (horiz q) c0
    rw [norm_sub_rev (pos s) (horiz q)] at t2
    have := h2 (by simp only [rH, δH]; linarith) (by simp only [rH, δH]; linarith)
    linarith
  · linarith

/-- **Safe region, point-mass helix** (simplified model, not the JSBSim aircraft): start in the helix set `DynH`,
take any per-frame disturbances within the proved budget `Small`, and let the map satisfy `HelixClear` at margin
`e + η`. Then at every frame `n`, any spec state `st` whose airframe lies within `e` of a rational point `c` that is
within `η` of the point-mass position is not a `Crash`. -/
theorem helix_safe_region {c0 : ℂ} {z0 m0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT)
    {s0 : St} {d : ℕ → St} (h0 : DynH c0 z0 m0 ztop s0) (hd : ∀ n, Small (d n))
    {M : CityMap} {e : ℚ} {η : ℝ} (hclr : HelixClear M c0 z0 m0 ztop (e + η))
    (n : ℕ) {st : State Float} {c : Pt} (hnear : Near η (traj stepHelix s0 d n) c)
    (ha : AirframeWithinOf e st c) : ¬ Crash M st :=
  not_crash_of_clear ha (helix_box_clear hz0 hzt (helix_forever hz0 hz0t hzt h0 hd n) hclr hnear)

/-! ## Instance: a helix circling a spire taller than its entry altitude -/

/-- A 60 m × 60 m spire, 350 m tall, centred on the helix centre `c0H = (0, Rstar 300 ≈ 194.17)`. -/
def spire : Box := ⟨-30, 30, 165, 225, -3 / 2, 350⟩

def spireMap : CityMap := ⟨3000, 20, 301, fun _ _ => 0, [spire]⟩

theorem spireMap_terrain (x y : ℚ) : spireMap.terrain x y = 0 := by
  simp [CityMap.terrain, spireMap]

theorem trimH_mem400 : DynH c0H 300 0 400 trimH := by
  refine ⟨?_, le_refl _, by norm_num [trimH, ZCAPH], fun _ => ⟨?_, ?_⟩⟩
  · simp [q, eu, evz, trimH, r2L]
  · simp [trimH, RL]
  · simp [c0H, trimH]

theorem c0H_re : c0H.re = 0 := by simp [c0H, centre, trimH, pos, cis]
theorem c0H_im : c0H.im = Rstar 300 := by simp [c0H, centre, trimH, pos, cis]

theorem spire_clear : HelixClear spireMap c0H 300 0 400 (((5 : ℚ) : ℝ) + 1) := by
  intro p hp
  have hR1 : (194 : ℝ) ≤ Rstar 300 := by norm_num [Rstar, uStar, EH, E1, ur, g, lc]
  have hR2 : Rstar 300 ≤ 195 := by norm_num [Rstar, uStar, EH, E1, ur, g, lc]
  have hgap : (61 : ℝ) < rH 300 400 - δH 300 0 400 - 2 * (((5 : ℚ) : ℝ) + 1) := by
    norm_num [rH, δH, Rstar, uStar, EH, E1, ur, g, lc, kappa]
  rcases hp with hp | ⟨b, hb, hc⟩
  · rw [spireMap_terrain] at hp
    have : (p.z : ℝ) ≤ 0 := by exact_mod_cast hp
    exact ⟨by norm_num; linarith, fun _ _ => by norm_num; linarith⟩
  · simp only [spireMap, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp only [Box.Contains, spire] at hc
    obtain ⟨x0, x1, y0, y1, -, z1⟩ := hc
    have cx0 : (-30 : ℝ) ≤ p.x := by exact_mod_cast x0
    have cx1 : (p.x : ℝ) ≤ 30 := by exact_mod_cast x1
    have cy0 : (165 : ℝ) ≤ p.y := by exact_mod_cast y0
    have cy1 : (p.y : ℝ) ≤ 225 := by exact_mod_cast y1
    have cz1 : (p.z : ℝ) ≤ 350 := by exact_mod_cast z1
    refine ⟨by norm_num; linarith, fun hlo _ => ?_⟩
    exfalso
    have hn : ‖horiz p - c0H‖ ≤ 61 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have er : (horiz p - c0H).re = (p.x : ℝ) := by simp [horiz, c0H_re]
      have ei : (horiz p - c0H).im = (p.y : ℝ) - Rstar 300 := by simp [horiz, c0H_im]
      rw [er, ei]
      have := abs_le.mpr (show -(30 : ℝ) ≤ p.x ∧ (p.x : ℝ) ≤ 30 from ⟨cx0, cx1⟩)
      have := abs_le.mpr (show -(31 : ℝ) ≤ (p.y : ℝ) - Rstar 300 ∧ (p.y : ℝ) - Rstar 300 ≤ 31 from
        ⟨by linarith, by linarith⟩)
      linarith
    linarith

/-- Instance: `trimH` under `dMax` every frame, circling the 350 m spire, airframe within 5 m, `η` = 1 m. -/
theorem spire_safe (n : ℕ) {st : State Float} {c : Pt}
    (hnear : Near 1 (traj stepHelix trimH (fun _ => dMax) n) c) (ha : AirframeWithinOf 5 st c) :
    ¬ Crash spireMap st :=
  helix_safe_region (by norm_num) (by norm_num) (by norm_num [ZT]) trimH_mem400 (fun _ => dMax_small)
    spire_clear n hnear ha

example : ∀ n (st : State Float) (c : Pt),
    Near 1 (traj stepHelix trimH (fun _ => dMax) n) c → AirframeWithinOf 5 st c → ¬ Crash spireMap st :=
  fun n _ _ hn ha => spire_safe n hn ha

/-- The `Near` antecedent is satisfiable: at frame 0 the point mass sits at `(0, 0, 300)`. -/
example : Near 1 (traj stepHelix trimH (fun _ => dMax) 0) ⟨0, 0, 300⟩ := by
  norm_num [Near, traj, trimH]

/-! ## The ray -/

/-- The corridor half-width of `ray_conf`. -/
def wR (z0 w0 ztop : ℝ) : ℝ := w0 + kapY * ((ztop - z0) / G)

/-- **Map clearance for the ray** (over ℝ, margin `E`): every solid point lies below `ztop - E`, and a solid point
within `wR + E` of the track and at least `x0 - E` along it lies below the climb line `z0 + G (x - x0 - E) - E`. -/
def RayClear (M : CityMap) (x0 z0 w0 ztop E : ℝ) : Prop :=
  ∀ q : Pt, Solid M q → (q.z : ℝ) < ztop - E ∧
    (|(q.y : ℝ)| ≤ wR z0 w0 ztop + E → x0 - E ≤ q.x → (q.z : ℝ) < z0 + G * max 0 ((q.x : ℝ) - x0 - E) - E)

theorem ray_box_clear {M : CityMap} {x0 z0 w0 ztop : ℝ} {e : ℚ} {η : ℝ} (hz0 : 0 ≤ z0)
    (hzt : ztop ≤ ZT) {s : St} (hs : DynR x0 z0 w0 ztop s) (hclr : RayClear M x0 z0 w0 ztop (e + η))
    {c : Pt} (hc : Near η s c) : ∀ q, InBox e c q → ¬ Solid M q := by
  intro q hq hsol
  obtain ⟨h1, h2⟩ := hclr q hsol
  simp only [InBox] at hq
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hq
  have b1 : (c.x : ℝ) - e ≤ q.x := by exact_mod_cast a1
  have b2 : (q.x : ℝ) ≤ c.x + e := by exact_mod_cast a2
  have b3 : (c.y : ℝ) - e ≤ q.y := by exact_mod_cast a3
  have b4 : (q.y : ℝ) ≤ c.y + e := by exact_mod_cast a4
  have b5 : (c.z : ℝ) - e ≤ q.z := by exact_mod_cast a5
  obtain ⟨hx, hy, hz⟩ := hc
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  obtain ⟨hz1, -⟩ := abs_le.mp hz
  have hqz : s.z - (e + η) ≤ q.z := by linarith
  by_cases hlt : s.z < ztop
  · obtain ⟨hw, hal, hg⟩ := ray_conf hz0 hzt hs hlt
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    have hqy : |(q.y : ℝ)| ≤ wR z0 w0 ztop + (e + η) := by
      rw [abs_le]; simp only [wR]; constructor <;> linarith
    have hm : max 0 ((q.x : ℝ) - x0 - (e + η)) ≤ s.x - x0 := max_le hal (by linarith)
    have hG := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ G by norm_num [G])
    have := h2 hqy (by linarith)
    linarith
  · linarith

/-- **Safe region, point-mass ray** (simplified model, not the JSBSim aircraft): as `helix_safe_region`, for the
ray set `DynR` and `RayClear`. -/
theorem ray_safe_region {x0 z0 w0 ztop : ℝ} (hz0 : 0 ≤ z0) (hz0t : z0 ≤ ztop) (hzt : ztop ≤ ZT)
    {s0 : St} {d : ℕ → St} (h0 : DynR x0 z0 w0 ztop s0) (hd : ∀ n, Small (d n))
    {M : CityMap} {e : ℚ} {η : ℝ} (hclr : RayClear M x0 z0 w0 ztop (e + η))
    (n : ℕ) {st : State Float} {c : Pt} (hnear : Near η (traj stepRay s0 d n) c)
    (ha : AirframeWithinOf e st c) : ¬ Crash M st :=
  not_crash_of_clear ha (ray_box_clear hz0 hzt (ray_forever hz0 hz0t hzt h0 hd n) hclr hnear)

/-- A 100 m × 60 m block, 330 m tall, on the ray's track 500 m to 600 m ahead of `trimR` (entered at 300 m). -/
def block : Box := ⟨500, 600, -30, 30, -3 / 2, 330⟩

def blockMap : CityMap := ⟨3000, 20, 301, fun _ _ => 0, [block]⟩

theorem blockMap_terrain (x y : ℚ) : blockMap.terrain x y = 0 := by
  simp [CityMap.terrain, blockMap]

theorem block_clear : RayClear blockMap 0 300 5 1000 (((5 : ℚ) : ℝ) + 1) := by
  intro p hp
  have hG : (0 : ℝ) ≤ G := by norm_num [G]
  rcases hp with hp | ⟨b, hb, hc⟩
  · rw [blockMap_terrain] at hp
    have : (p.z : ℝ) ≤ 0 := by exact_mod_cast hp
    have := mul_nonneg hG (le_max_left 0 ((p.x : ℝ) - 0 - (((5 : ℚ) : ℝ) + 1)))
    exact ⟨by norm_num; linarith, fun _ _ => by norm_num at this ⊢; linarith⟩
  · simp only [blockMap, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp only [Box.Contains, block] at hc
    obtain ⟨x0, -, -, -, -, z1⟩ := hc
    have cx0 : (500 : ℝ) ≤ p.x := by exact_mod_cast x0
    have cz1 : (p.z : ℝ) ≤ 330 := by exact_mod_cast z1
    refine ⟨by norm_num; linarith, fun _ _ => ?_⟩
    have h6 : (((5 : ℚ) : ℝ) + 1) = 6 := by norm_num
    rw [h6, show G = 2 / 25 from rfl]
    have hm : (p.x : ℝ) - 0 - 6 ≤ max 0 ((p.x : ℝ) - 0 - 6) := le_max_right _ _
    linarith

/-- Instance: `trimR` under `dMax` every frame, climbing over the 330 m block, airframe within 5 m, `η` = 1 m. -/
theorem block_safe (n : ℕ) {st : State Float} {c : Pt}
    (hnear : Near 1 (traj stepRay trimR (fun _ => dMax) n) c) (ha : AirframeWithinOf 5 st c) :
    ¬ Crash blockMap st :=
  ray_safe_region (by norm_num) (by norm_num) (by norm_num [ZT]) trimR_mem (fun _ => dMax_small)
    block_clear n hnear ha

example : ∀ n (st : State Float) (c : Pt),
    Near 1 (traj stepRay trimR (fun _ => dMax) n) c → AirframeWithinOf 5 st c → ¬ Crash blockMap st :=
  fun n _ _ hn ha => block_safe n hn ha

end

#print axioms helix_safe_region
#print axioms spire_safe
#print axioms ray_safe_region
#print axioms block_safe

end Proofs.SafeRegion
