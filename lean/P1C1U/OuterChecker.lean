import P1Wrap.OuterProgram

namespace P1C1U.AstraC1U.Outer

open C1Challenge P1Int P1Wrap.W3 P1Wrap.W3.AstraOuter
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Hier (MCode Entry)

open private P1Wrap.W3.AstraOuter.Words P1Wrap.W3.AstraOuter.ready
  P1Wrap.W3.AstraOuter.stageAnswer P1Wrap.W3.AstraOuter.easy_stage
  P1Wrap.W3.AstraOuter.stage_true_iff P1Wrap.W3.AstraOuter.padded_ready
  P1Wrap.W3.AstraOuter.pieces_ready from P1Wrap.OuterTask

noncomputable section

open Classical in
def verdict (code : MCode) (j a b : ℕ) (w x : List Bool) : Bool :=
  decide (lpM2 (sOf j) a b x.length ≤ w.length ∧
    ∃ (τ : List Entry) (r : ℕ), (∀ e ∈ τ, e ∈ code.table) ∧
      w.drop (lpM2 (sOf j) a b x.length) = encT code.table τ ++ List.replicate r false ∧
      P1Hier.Check code (padIn j a b x (w.take (lpM2 (sOf j) a b x.length))) w.length τ)

private theorem ready_verdict (code : MCode) (j a b : ℕ) (w x : List Bool) :
    P1Wrap.W3.AstraOuter.stageAnswer code (P1Wrap.W3.AstraOuter.ready j a b (w, x)) = verdict code j a b w x := by
  classical
  rw [Bool.eq_iff_iff, P1Wrap.W3.AstraOuter.stage_true_iff, verdict, decide_eq_true_iff, P1Wrap.W3.AstraOuter.padded_ready, P1Wrap.W3.AstraOuter.pieces_ready]
  simp only [P1Wrap.W3.AstraOuter.ready, tally_length]

/-- The outer wrapper's task accepts a table with several rows for a state and scanned symbols. -/
theorem task (code : MCode) (j a b : ℕ) :
    Task (fun p : List Bool × List Bool => p.1.length + nuOf j a b p.2.length)
      (fun p => send (withGuess p.1 p.2)) (fun p => send (verdict code j a b p.1 p.2)) := by
  have hu := P1Hier.UM.easy_unGuess
  have hP := PT.paramPad j a b
  have hW1 : Task P1Hier.checkBudget send (fun i => send (P1Hier.UM.chk i)) := P1Hier.check_task_of_phases
  have splitInput : Easy (fun z : List Bool => (ruler (P1Hier.UM.unGuess z).2, P1Hier.UM.unGuess z)) :=
    (Easy.ruler (Easy.sndCompose hu)).pair hu
  have t₁ : Task (fun p : P1Wrap.W3.AstraOuter.Words => size (withGuess p.1 p.2))
      (fun p => send (withGuess p.1 p.2)) (fun p => send (ruler p.2, p)) :=
    (Task.on splitInput (fun p : P1Wrap.W3.AstraOuter.Words => withGuess p.1 p.2)).conform
      (fun _ => rfl) (fun _ => rfl) (fun p => by
        change send (ruler (P1Hier.UM.unGuess (withGuess p.1 p.2)).2,
          P1Hier.UM.unGuess (withGuess p.1 p.2)) = send (ruler p.2, p)
        rw [P1Hier.UM.unGuess_withGuess])
  have t₂ : Task (fun p : P1Wrap.W3.AstraOuter.Words => nuOf j a b p.2.length)
      (fun p => send (ruler p.2, p)) (fun p => send (P1Wrap.W3.AstraOuter.ready j a b p)) := by
    have h := (Task.on hP (fun p : P1Wrap.W3.AstraOuter.Words => ruler p.2)).left (fun p : P1Wrap.W3.AstraOuter.Words => send p)
    refine h.conform (fun p => ?_) (fun _ => rfl) (fun p => ?_)
    · simp only [ruler_length]
    · simp only [P1Wrap.W3.AstraOuter.ready, send_prod, ruler_length]
  have t₃ := Task.on (P1Wrap.W3.AstraOuter.easy_stage code hW1) (P1Wrap.W3.AstraOuter.ready j a b)
  have combined := (t₁.compose t₂).compose t₃
  refine (combined.bound (b' := fun p => p.1.length + nuOf j a b p.2.length) 12
    (fun p => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun p => ?_)
  · change size (withGuess p.1 p.2) + nuOf j a b p.2.length + size (P1Wrap.W3.AstraOuter.ready j a b p) + 1 ≤ _
    simp only [P1Wrap.W3.AstraOuter.ready, size_prod, size_tally, tally_length, P1Hier.UM.size_bits', length_withGuess', nuOf]
    omega
  · exact congrArg send (ready_verdict code j a b p.1 p.2)

/-- One machine checks the table transcript at every guess and input with the wrapper's linear bound. -/
theorem verifier (code : MCode) (j a b : ℕ) :
    ∃ (V : C1Challenge.Machine) (K : ℕ), ∀ w x : List Bool,
      HaltsWithin V (withGuess w x) (verdict code j a b w x)
        (K * (w.length + nuOf j a b x.length + 1)) := by
  obtain ⟨D, K, hD⟩ := P1Hier.compile_task
    (fun p : List Bool × List Bool => p.1.length + nuOf j a b p.2.length)
    (fun p => withGuess p.1 p.2) (fun p => verdict code j a b p.1 p.2) (task code j a b)
  refine ⟨P1Wrap.Bridge.fromOAI D, 3 * K, fun w x => ?_⟩
  have hd := (P1Wrap.Bridge.haltsWithin_fromOAI D).mpr (hD (w, x))
  apply P1Wrap.Bridge.haltsWithin_mono hd
  have hl := length_withGuess' w x
  have hx : x.length ≤ nuOf j a b x.length := by unfold nuOf; omega
  change K * ((withGuess w x).length + (w.length + nuOf j a b x.length) + 1) ≤
    3 * K * (w.length + nuOf j a b x.length + 1)
  calc
    _ ≤ K * (3 * (w.length + nuOf j a b x.length + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end
end P1C1U.AstraC1U.Outer

#print axioms P1C1U.AstraC1U.Outer.verifier
