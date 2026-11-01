import Ci.proof.SafeSound

/-! The one-tick safety and climb obligation of `Ci.Proof.lawT`, proved: every state in the terminal set lies in
one of the 53 cell boxes of `TData.boxTab`, and on each box the interval check `SafeIv.ok` passes after at most a
few bisections (`checkRec`, evaluated by the kernel). -/

namespace Ci.Proof.SafeIv
open Vibecheck Jsb Ci.Lawfirst
open Ci.Proof.LawIv (In I)

/-- The property checked on boxes: for every memory with this integrator value and a stored α command in range,
the tick is safe and climbs. -/
def Pt (c : CLOf Fx) : Prop :=
  ∀ m : Mem, m.eI = c.elev.raw → (-900000 ≤ m.ac ∧ m.ac ≤ 900000) →
    (Ci.tickT lawT c.s m).safe = true ∧ (Ci.tickT lawT c.s m).climb = true ∧
    hLoT ≤ (Ci.tickT lawT c.s m).s.h.raw ∧ (Ci.tickT lawT c.s m).s.h.raw < hHiT

theorem clampI_idem (lo hi x : Int) (h : lo ≤ hi) : clampI lo hi (clampI lo hi x) = clampI lo hi x := by
  unfold clampI; omega

theorem thrH_anti {a b : Int} (h : a ≤ b) : thrH b ≤ thrH a := by
  have hx : max 0 (a - hThr) ≤ max 0 (b - hThr) := by omega
  have h0 : 0 ≤ max 0 (a - hThr) := by omega
  have hsq : max 0 (a - hThr) * max 0 (a - hThr) ≤ max 0 (b - hThr) * max 0 (b - hThr) :=
    Int.mul_le_mul hx hx h0 (by omega)
  have hd : max 0 (a - hThr) * max 0 (a - hThr) / thrK ≤ max 0 (b - hThr) * max 0 (b - hThr) / thrK :=
    Int.ediv_le_ediv (by decide) hsq
  unfold thrH clampI
  generalize max 0 (a - hThr) * max 0 (a - hThr) / thrK = ta at hd ⊢
  generalize max 0 (b - hThr) * max 0 (b - hThr) / thrK = tb at hd ⊢
  omega

theorem ok_sound (B : CLOf Iv) (c : CLOf Fx) (hB : B.Mem c) (hok : ok B = true) : Pt c := by
  intro m hm hac
  dsimp only [ok] at hok
  split at hok
  · cases hok
  · rename_i hbox
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hbox
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨bvx, bvz⟩, bdx⟩, bdz⟩, bq⟩, bah⟩, bau⟩, bh⟩, bpvz⟩, bpvz2⟩, bel⟩, brho⟩ := hbox
    have hS := hB.1
    have H : LawIv.Holds ⟨pr B.s.vx, pr B.s.vz, pr B.s.dx, pr B.s.dz, pr B.s.q, pr B.s.ah, pr B.s.au, rhoI B.s.h,
        pr B.elev⟩ c.s m :=
      { vx := in_pr bvx hS.2.2.1, vz := in_pr bvz hS.2.2.2.1, dx := in_pr bdx hS.2.2.2.2.1,
        dz := in_pr bdz hS.2.2.2.2.2.1, q := in_pr bq hS.2.2.2.2.2.2.1,
        ah := in_pr bah hS.2.2.2.2.2.2.2.2.2.2.2.2.1, au := in_pr bau hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        rho := in_pr brho (Jsb.Iv.atm_sound Jsb.C172.atmRho hS.2.1),
        eI := by rw [hm]; exact in_pr bel hB.2 }
    split at hok
    · cases hok
    · rename_i e he
      have hel := LawIv.elev_sound H hac he
      -- the scoreboard's clamped input lies in the interval input
      have hU : (InputOf.Mem ⟨.box e.1 e.2, .box (thrI B.s.h).1 (thrI B.s.h).2, .box 0 0, .box 0 0⟩
          (Ci.clampInput (lawT.step m c.s).1)) := by
        have hh := mem_lohi bh hS.2.1
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (Iv.box e.1 e.2).Mem (Ci.clampInput (lawT.step m c.s).1).elev
          rw [Jsb.Iv.mem_box]
          have hce : (Ci.clampInput (lawT.step m c.s).1).elev.raw =
              max (-65536) (min 65536 (stepP p1 m c.s).1.elev.raw) := rfl
          obtain ⟨E, hE⟩ : ∃ E, (stepP p1 m c.s).1.elev.raw = clampI (-65536) 65536 E := ⟨_, rfl⟩
          rw [hce, hE]
          unfold In at hel
          rw [hE] at hel
          unfold clampI at *; constructor <;> omega
        · show (thrI B.s.h).1 ≤ max 0 (min 65536 (thrH c.s.h.raw)) ∧ max 0 (min 65536 (thrH c.s.h.raw)) ≤ (thrI B.s.h).2
          have t1 := thrH_anti hh.1
          have t2 := thrH_anti hh.2
          unfold thrI
          have r : max 0 (min 65536 (thrH c.s.h.raw)) = thrH c.s.h.raw := by
            unfold thrH clampI
            generalize max 0 (c.s.h.raw - hThr) * max 0 (c.s.h.raw - hThr) / thrK = t
            omega
          rw [r]; exact ⟨t2, t1⟩
        · show (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0; omega
        · show (0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0; omega
      have key := plantOK_sound hU 8 B.s c.s _ _ _ true true hS
        (LawIv.sub_in (in_pr bvz hS.2.2.2.1) (in_pr bpvz hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
        (LawIv.sub_in (in_pr bpvz hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (in_pr bpvz2 hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2))
        (in_pr bh hS.2.1) hok
      dsimp only [Ci.tickT]
      generalize Ci.subT (Ci.clampInput (lawT.step m c.s).1) 8 c.s true true = res at key ⊢
      obtain ⟨s', ok', cl'⟩ := res
      obtain ⟨k1, k2, k3⟩ := key
      simp only [Prod.mk.injEq] at k1
      obtain ⟨h1, h2⟩ := k1
      subst h1; subst h2
      exact ⟨rfl, rfl, k2, k3⟩

end Ci.Proof.SafeIv
