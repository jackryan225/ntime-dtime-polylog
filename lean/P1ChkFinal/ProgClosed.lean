import P1ChkFinal.ProgSolFmt
import P1ChkFinal.BatchLink
import P1SolFmt.Length
import P1SolFmt.Genuine

/-!
# P1ChkFinal.ProgClosed: the programs of C11, C12, C13ends at the GENUINE dims, with no open input

Lane P1-lean-checks (2026-11-25). `progC11_fmt`, `progC12`, `progC13ends_fmt` need only `BatchHyp`, `LenHyp` and
`FmtHyp dims`. Here they are closed at the genuine dims of Lemma P (P1-sol-space: `P1Wit.SolSpace.genuineDims` at
`t = lpTime a b n`, guess length `g = a (n^2 + 1)`) by
* `P1ChkFinal.batchHyp` (BatchLink.lean, from `P1Batch.batch_lookup`),
* `P1SolFmt.SolLength.lenHyp` and `P1SolFmt.SolFormat.fmtHyp_genuine` (Sol P1-sol-fmt, files P1SolFmt/, unchanged).
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

open scoped Classical

variable {k : Type*} [Field k] {S : BlockSchedule k}

/-- **Family 11 (C12), program, genuine dims, no open input.** -/
theorem progC12_genuine (A : S.Templates) (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine)
    (aM a b d bigBias termBias : ℕ) (M K : ℕ → ℕ) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C12w (fun n => SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n)
        (a * (n ^ 2 + 1)) d bigBias termBias) p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  progC12 _ M K batchHyp P1SolFmt.SolLength.lenHyp
    (P1SolFmt.SolFormat.fmtHyp_genuine A Kc V aM a b d bigBias termBias)

/-- **Family 10 (C11), program, genuine dims, no open input.** -/
theorem progC11_genuine (A : S.Templates) (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine)
    (aM a b d bigBias termBias : ℕ) (M K : ℕ → ℕ) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C11w (fun n => SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n)
        (a * (n ^ 2 + 1)) d bigBias termBias) p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  progC11_fmt _ M K batchHyp P1SolFmt.SolLength.lenHyp
    (P1SolFmt.SolFormat.fmtHyp_genuine A Kc V aM a b d bigBias termBias)

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- **Family 13 (C13ends), program, genuine dims, no open input.** -/
theorem progC13ends_genuine (bs : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) (M K : ℕ → ℕ) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw bs l (fun n => SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n)
        (a * (n ^ 2 + 1)) d bigBias termBias) p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  progC13ends_fmt bs l _ M K batchHyp P1SolFmt.SolLength.lenHyp
    (P1SolFmt.SolFormat.fmtHyp_genuine A Kc V aM a b d bigBias termBias)

end P1ChkFinal

#print axioms P1ChkFinal.progC12_genuine
#print axioms P1ChkFinal.progC11_genuine
#print axioms P1ChkFinal.progC13ends_genuine
