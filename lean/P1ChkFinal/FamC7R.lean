import P1ChkFinal.C7RTarget
import P1SolFmt.C7RProg
import P1ChkFinal.FamGreedyAg

/-!
# P1ChkFinal.FamC7R: the program of family 6, refresh part, at the genuine dims (lane P1-lean-greedy, D15)

Sol P1-sol-c7rprog DONE in round 1 (runner LEAN CHECK passed); file ChkFinal/P1SolFmt/C7RProg.lean copied UNCHANGED
(sha256 4894f2db..fbbac, 643 lines; read: format rows, two batch reads (term slot + in-endpoints, then the tie widths),
integer admission test, `evaluate_correct` = the decision equals `decide (C7Rfam ..)`, Task, `famProg_of_task`).
-/

namespace P1ChkFinal.C7R

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- **The refresh part of family 6 has a program at the genuine dims** (exact owner target). -/
theorem c7rProg {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)
    (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    C7RProgTarget A Kc V aM a b d bigBias termBias :=
  P1SolC7R.c7rProg_genuine A Kc V aM a b d bigBias termBias hs hb

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1Int P1ChkFinal.FmtAgTarget P1ChkFinal.FamGreedy

open Classical in
/-- **Use test of `FamProgAndTarget`** (shape check before its prover starts): with it, family 6 = `C7all` has a program
at the genuine dims, from `famC7_genuine` (shrinking part) and `c7rProg` (refresh part). -/
theorem famC7all_of_and (hand : FamProgAndTarget) {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)
    {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : FixedBlock 𝕜 demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C7all S.graph (Nat.two_pow_pos S.expanderExponent)
        (S.port_bound.connected_and_pos S.port_order).1 A.refresh B (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ := by
  obtain ⟨R₁, c₁, n₁, h₁⟩ := famC7_genuine A Kc V aM a b d bigBias termBias B hs hb
  obtain ⟨R₂, c₂, n₂, h₂⟩ := c7rProg A Kc V aM a b d bigBias termBias hs hb
  obtain ⟨R, c, n, h⟩ := hand R₁ R₂ _ _ _ _ _ c₁ c₂ n₁ n₂ h₁ h₂
  refine ⟨R, c, n, ?_⟩
  have e : (fun x u i => decide (C7all S.graph (Nat.two_pow_pos S.expanderExponent)
        (S.port_bound.connected_and_pos S.port_order).1 A.refresh B (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) =
      (fun x u i => decide (P1SolGreedy.C7fam B (gDims A Kc V aM a b d bigBias termBias)
          (agG (gDims A Kc V aM a b d bigBias termBias)) x u i) &&
        decide (C7Rfam S.graph (Nat.two_pow_pos S.expanderExponent)
          (S.port_bound.connected_and_pos S.port_order).1 A.refresh
          (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias) x u i)) := by
    funext x u i
    rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact Iff.rfl
  rw [e]
  exact h

end P1ChkFinal.C7R

#print axioms P1ChkFinal.C7R.c7rProg
#print axioms P1ChkFinal.C7R.famC7all_of_and
