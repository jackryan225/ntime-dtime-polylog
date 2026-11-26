import C1Challenge.UTime
import C1Challenge.C1UGuards

/-! Guards for `UTIMEIn`: DTIME(f) ⊆ UTIME(f); the branching machine (two accepting computations) is not unambiguous. -/

namespace C1Challenge
namespace UTimeGuards

open NTimeGuards C1UGuards

theorem utime_of_dtime {L : List Bool → Bool} {f : ℕ → ℝ} (h : DTIMEIn L f) : UTIMEIn L f := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨toN M, C, fun x => ?_⟩
  obtain ⟨T, hT, hH⟩ := hM x
  refine ⟨T, hT, fun c' hr => ?_, ?_, ?_⟩
  · obtain ⟨t, htT, c, hc, hstop, -⟩ := hH
    have hr' := (reach_toN M (T + 1) (M.init x) c').1 hr
    obtain ⟨k, hk⟩ : ∃ k, T + 1 = t + 1 + k := ⟨T - t, by omega⟩
    rw [hk, run_after_halt M hc hstop k] at hr'
    cases hr'
  · rw [acc_toN hH]
    split <;> omega
  · rw [acc_toN hH]
    cases L x <;> simp

theorem utime_firstBit : UTIMEIn firstBit (fun n => (n : ℝ)) :=
  utime_of_dtime (dtime_firstBit _ (fun n => Nat.cast_nonneg n))

theorem fork_ambiguous (x : List Bool) : ¬ forkMachine.acc x ≤ 1 := by
  rw [acc_fork]
  omega

end UTimeGuards
end C1Challenge

#print axioms C1Challenge.UTimeGuards.utime_of_dtime
#print axioms C1Challenge.UTimeGuards.utime_firstBit
#print axioms C1Challenge.UTimeGuards.fork_ambiguous
