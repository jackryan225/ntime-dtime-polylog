import P1ChkFinal.C7RTests
import P1ChkFinal.FamGreedyAg

/-!
# P1ChkFinal.C7RTarget: the target of the program of family 6, refresh part (lane P1-lean-greedy, D15)

The refresh data of the genuine schedule (as in integ's TrueRecords.lean): `S.graph`, `Nat.two_pow_pos S.expanderExponent`,
`(S.port_bound.connected_and_pos S.port_order).1`, `A.refresh`. The target `C7RProgTarget A Kc V aM a b d bigBias termBias`
says: the family `C7Rfam` at the genuine dims has a program in the form `P1Int.P11.FamProg`, as `famC7_genuine` for the
shrinking part. Then `C7all` (= family 6) gets its program from the two (conjunction of two families with the same index).
-/

namespace P1ChkFinal.C7R

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1Int

open Classical

/-- **Target of the Sol prover of the C7Rfam program** (statement only). -/
def C7RProgTarget {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) : Prop :=
  ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (C7Rfam S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 A.refresh
      (fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias) x u i))
    ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂

/-- **Target: the conjunction of two family programs** (needed for family 6 = `C7all` = `C7fam ∧ C7Rfam`: the programs
`famC7_genuine` and `c7rProg_genuine` give one program of the conjunction). Statement only. -/
def FamProgAndTarget : Prop :=
  ∀ (Rc₁ Rc₂ : Prog Ltr) (ck₁ ck₂ : List Bool → List Bool → ℕ → Bool) (s : ℝ) (a b cc₁ cc₂ n₁ n₂ : ℕ),
    P11.FamProg Ltr.bit P1Dispatch.answer Rc₁ ck₁ s a b cc₁ n₁ →
    P11.FamProg Ltr.bit P1Dispatch.answer Rc₂ ck₂ s a b cc₂ n₂ →
    ∃ (Rc : Prog Ltr) (cc n₃ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc (fun x u i => ck₁ x u i && ck₂ x u i) s a b cc n₃

end P1ChkFinal.C7R
