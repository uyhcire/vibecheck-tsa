import ExpVibecheck.Controls

namespace ExpVibecheck

instance (s : State) : Decidable (Init s) := by unfold Init; infer_instance

example : Init initState := by decide

example : inS initState = true := init_inS initState (by decide)

/-- No certificate can declare every state safe, so `safe` has teeth. -/
theorem no_certificate_accepts_everything : ¬ ∃ C : Certificate, ∀ s, C.inS s = true := by
  rintro ⟨C, hC⟩
  let s : State := { initState with phase := .crashed .terrain }
  exact C.safe s (hC s) ⟨.terrain, rfl⟩

example : inS { initState with phase := .crashed .terrain } = false := by decide

/-- The pilot-input-ignoring filter that always parks is not a certificate: `passthrough`
forbids overriding a safe input (here: idle on the runway). -/
theorem always_park_violates_passthrough :
    ¬ (∀ s u, inS s = true → u.Admissible → inS (step s u) = true →
        (fun (_ : State) (_ : Input) => Autoland.park) s u = u) := by
  intro h
  have hu : ({ stick := 0, throttle := 0, brake := false } : Input).Admissible := by decide
  have hs : step initState { stick := 0, throttle := 0, brake := false } = initState := by decide
  have := h initState _ (init_inS initState (by decide)) hu (by rw [hs]; exact init_inS _ (by decide))
  simp [Autoland.park] at this

end ExpVibecheck
