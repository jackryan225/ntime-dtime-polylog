import P1Int.TrueRecords
import P1Int.RecordsFitProof

/-!
# The true record package `H` at the fixed parameters (P1-lean-integ)

`trueH`: witfill's record package built from the fit facts (`recordsFit`, Sol recfit), the true panel values
(`trueSupply`) and the true injective term tables (`trueTables`, `trueTables_injective`, Sol truerec).
`trueH_facts`: one threshold for both facts (the larger of the two `n₂`).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- The two facts that `trueH` needs at one input. -/
def TrueHFacts (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) : Prop :=
  RecordsFitStmt Bt κ hκ V a b x d bigBias termBias ∧
    ∀ σ, TablesInjective (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0
      (trueTables Bt κ hκ V a b x d bigBias termBias σ)

/-- **The true record package** at one input. -/
def trueH (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias) : FixedRecords Bt κ hκ V a b x d bigBias termBias :=
  mkRecordsT Bt κ hκ V a b x d bigBias termBias hH.1 (trueSupply Bt κ hκ V a b x d bigBias termBias)
    (trueTables Bt κ hκ V a b x d bigBias termBias) hH.2

/-- **One threshold for the facts of `trueH`.** -/
theorem trueH_facts (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) (hb : 1 ≤ b) :
    ∃ n₂ : ℕ, ∀ x : List Bool, n₂ ≤ x.length → TrueHFacts Bt κ hκ V a b x d bigBias termBias := by
  obtain ⟨n₁, h₁⟩ := recordsFit Bt κ hκ V a b d bigBias termBias hb
  obtain ⟨n₂, h₂⟩ := trueTables_injective Bt κ hκ V a b d bigBias termBias hb
  exact ⟨max n₁ n₂, fun x hx => ⟨h₁ x (le_of_max_le_left hx), h₂ x (le_of_max_le_right hx)⟩⟩

end

end P11

end P1Int

#print axioms P1Int.P11.trueH
#print axioms P1Int.P11.trueH_facts
