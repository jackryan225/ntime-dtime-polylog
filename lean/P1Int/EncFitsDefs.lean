import P1Int.FormDefs
import P1Int.TrueH
import P1Int.WitnessFit

/-!
# `EncFits` for the true records (P1-lean-integ, statement only)

`EncFits H` (FormDefs.lean): the fixed part and the payload of every tuple fit into the `m` witness bits. For the true
records `trueH` the payload of a tuple is the list of the wire words of the final state of its branch, so its length is
the total width of that final state; `witness_fits` (WitnessFit.lean, PROVED) bounds `fixedLen + totalWidth` by `m`
for all long inputs.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- **Target: `EncFits` for the true records, for all long inputs.** -/
def EncFitsTrueTarget (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) : Prop :=
  1 ≤ b → ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length →
    ∀ hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias,
      EncFits Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH)

end

end P11

end P1Int
