import C1Challenge.UTime
import P1Final.C1UClosed
import P1C1U.Resolve

/-! # P1Final.UTimeClosed: both sentences of Theorem "Uplus" (P1-lean-integ, 2026-11-25) -/

theorem P1Final.utime_sub {L : List Bool → Bool} {f : ℕ → ℝ} (h : C1Challenge.UTIMEIn L f) :
    C1Challenge.NTIMEIn L f ∧ C1Challenge.ParTIMEIn L f := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨⟨M, C, fun x => ?_⟩, ⟨M, C, fun x => ?_⟩⟩
  · obtain ⟨T, hT, hbound, hle, hiff⟩ := hM x
    refine ⟨T, hT, hbound, hiff.trans ?_⟩
    haveI := P1C1U.AstraC1U.finite_accComp hbound
    have hdef : M.acc x = Nat.card (M.AccComp x) := rfl
    constructor
    · intro h1
      have hpos : 0 < Nat.card (M.AccComp x) := by omega
      obtain ⟨a⟩ := (Nat.card_pos_iff.1 hpos).1
      exact ⟨a.1.length, M.after (M.init x) a.1, C1Challenge.C1UGuards.run_reach M a.1 _ a.2.1, a.2.2.1, a.2.2.2⟩
    · rintro ⟨t, c, hr, hh, ha⟩
      obtain ⟨os, hos, -, hc⟩ := C1Challenge.C1UGuards.reach_run M t _ c hr
      have hne : Nonempty (M.AccComp x) :=
        ⟨⟨os, hos, by rw [hc]; exact hh, by rw [hc]; exact ha⟩⟩
      have hpos : 0 < Nat.card (M.AccComp x) := Nat.card_pos_iff.2 ⟨hne, inferInstance⟩
      omega
  · obtain ⟨T, hT, hbound, hle, hiff⟩ := hM x
    refine ⟨T, hT, hbound, hiff.trans ?_⟩
    constructor
    · intro h1
      rw [h1]
      exact ⟨0, rfl⟩
    · rintro ⟨k, hk⟩
      omega

theorem P1Final.c1u_utime_closed : ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
    ¬ (C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) ∧
      C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ)) ∧
    ¬ C1Challenge.UTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  obtain ⟨σ, hσ, L, hL, hnot⟩ := P1Final.c1u_closed
  exact ⟨σ, hσ, L, hL, hnot, fun hu => hnot (P1Final.utime_sub hu)⟩

open Lean in
run_meta do
  let env ← getEnv
  let some x := env.find? ``C1Challenge.c1u_utime | throwError "C1Challenge.c1u_utime not found"
  let some y := env.find? ``P1Final.c1u_utime_closed | throwError "P1Final.c1u_utime_closed not found"
  unless x.type == y.type do throwError "TYPES DIFFER"
  logInfo "P1Final.c1u_utime_closed has exactly the type of C1Challenge.c1u_utime (as terms)"

#print axioms P1Final.c1u_utime_closed
