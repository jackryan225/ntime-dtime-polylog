import P1Int.FinalWiring
import P1P5.ConeClose

/-!
# Closing two inputs of `FinalInputs` with the eval lane's proofs (P1-lean-integ)

* `factor0In_proved`: `Factor0In` from `P1P5.Cone.factor0Hyp_cone` (Sol f0read, PROVED by eval).
* `coneIn_of_target`: `ConeIn` from the cone program's owner target `P1P5.Cone.ConeTarget` at `ρ = Fintype.equivFin`
  (kernel writers `shrinkWriters_all`, PROVED by eval).
* `FinalInputs2` = `ConeTarget` (for every machine) ∧ `GreedyIn` ∧ `DispIn`; `openChecksRec_of_inputs2`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

theorem factor0In_proved {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (d : ℕ) :
    Factor0In Bt κ hκ d :=
  fun V a b bigBias termBias _ => P1P5.Cone.factor0Hyp_cone Bt κ hκ V a b d bigBias termBias _

/-- The cone program's owner target for every machine and parameters, at `ρ = Fintype.equivFin`. -/
def ConeTargetIn {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (d : ℕ)
    (bs : Module.Basis (Fin d) (ZMod 2) F) : Prop :=
  ∀ (V : C1Challenge.Machine) (a b bigBias termBias : ℕ), 1 ≤ b →
    P1P5.Cone.ConeTarget Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) bs

theorem coneIn_of_target {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (d : ℕ)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (h : ConeTargetIn Bt κ hκ d bs) : ConeIn Bt κ hκ d bs :=
  fun V a b bigBias termBias hb hf => h V a b bigBias termBias hb (P1P5.Cone.shrinkWriters_all Bt) hf

/-- `EnergyFitIn` at every port from greedy's `EnergyFitLong` (Astra target, decision D16). -/
theorem energyFitIn_of_long (h : P1ChkFinal.EnergyFit.EnergyFitLong) {k : Type} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (d : ℕ) : EnergyFitIn Bt κ hκ d :=
  fun V a b bigBias termBias hb => h Bt κ hκ V a b d bigBias termBias hb

/-- **The inputs still owed after eval's proofs**: cone program target, greedy bridges, dispatcher, energy fit. -/
def FinalInputs2 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Module.Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant →
    haveI : Fintype F := Fintype.ofFinite F
    ConeTargetIn Bt κ hκ D bs ∧ GreedyIn Bt κ hκ D ∧ DispIn Bt κ hκ D bs l ∧ EnergyFitIn Bt κ hκ D

theorem finalInputs_of_2 (h : FinalInputs2) : FinalInputs := by
  intro S Bt F _ _ _ _ κ hκ D bs l hl1 hlane hgrow
  letI : Fintype F := Fintype.ofFinite F
  have h3 := h S Bt F κ hκ D bs l hl1 hlane hgrow
  exact ⟨coneIn_of_target Bt κ hκ D bs h3.1, factor0In_proved Bt κ hκ D, h3.2.1, h3.2.2.1, h3.2.2.2⟩

theorem openChecksRec_of_inputs2 (h : FinalInputs2) : OpenChecksRec :=
  openChecksRec_of_inputs (finalInputs_of_2 h)

end P11

end P1Int

#print axioms P1Int.P11.openChecksRec_of_inputs2
