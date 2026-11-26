import P1Int.D5AsmDefs

/-! # The size facts that `D5StepsAsmTarget` takes, for all long inputs (P1-lean-integ, statement only) -/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)

/-- **Target: the size facts at the fixed dims for all long inputs.** -/
def SizeFactsTarget (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) : Prop :=
  1 ≤ b → ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length →
    (fixedDims Bt V a b x d bigBias termBias).I ≠ 0 ∧
    (fixedDims Bt V a b x d bigBias termBias).I * (fixedDims Bt V a b x d bigBias termBias).N ≠ 0 ∧
    P1Wrap.Params.B (lpTime a b x.length) ≠ 0 ∧
    2 ≤ P1Wrap.Params.B (lpTime a b x.length) * (fixedDims Bt V a b x d bigBias termBias).N ∧
    (fixedDims Bt V a b x d bigBias termBias).nGB = P1ChkDir.nGuessBlocks (a * (x.length ^ 2 + 1))
      (P1Wrap.Params.B (lpTime a b x.length) * (fixedDims Bt V a b x d bigBias termBias).N) ∧
    (c4dims Bt V a b d bigBias termBias x.length).D.N = 2 ^ (c4dims Bt V a b d bigBias termBias x.length).h

end

end P11

end P1Int
