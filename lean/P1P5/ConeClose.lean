import P1P5.ConeTarget
import P1P5.ScheduleValues
import P1SolF0R.Factor0Hyp

/-!
# P1, the cone program: both hypotheses of `ConeTarget` discharged (owner P1-lean-eval, 14:40Z)

* `factor0Hyp_cone`: the level-0 header reader in the cone's FROZEN form `P1SolCone.Factor0Hyp .. P1Benes.NetBridge.bset`,
  from Sol f0read's `P1SolF0R.factor0Hyp : P1P5.F0.Factor0Hyp ..` (owner check F0ReadCheck.lean; the two Props have the same
  text up to the namespace of `Factor0In`, `SwitchSettings`, `factor0Agreement`, all `abbrev`/`def`, so they are equal by
  unfolding).
* `cone_of_target`: from `ConeTarget` ALONE (the cone program, open: Sol P1-sol-cone and Astra P1-astra-cone), kernel
  evaluators with `ScheduleKernelsOK` and a constant `c` with `WHyp` for the ONE `Wof` term
  `coneWof .. values (factor0Hyp_cone ..).choose`, for all `M K`.
-/

namespace P1P5.Cone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int Module

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

/-- The header reader in the cone's frozen form (PROVED: Sol f0read). -/
theorem factor0Hyp_cone (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) :
    P1SolCone.Factor0Hyp Bt κ hκ V a b d bigBias termBias ρ P1Benes.NetBridge.bset :=
  P1SolF0R.factor0Hyp Bt κ hκ V a b d bigBias termBias ρ

/-- From the cone program's owner target alone: values with `ScheduleKernelsOK` and `WHyp` for THE `Wof` term. -/
theorem cone_of_target (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) {Dd : ℕ} (bs : Basis (Fin Dd) (ZMod 2) F)
    (hT : ConeTarget Bt κ hκ V a b d bigBias termBias ρ bs) :
    ∃ (values : P1SolCone.SolCone.KernelValues F) (c : ℕ),
      P1SolCone.SolCone.ScheduleKernelsOK Bt κ hκ values ∧
      ∀ M K : ℕ → ℕ, P1ChkFinal.WHyp bs
        (coneWof Bt V a b d bigBias termBias values (factor0Hyp_cone Bt κ hκ V a b d bigBias termBias ρ).choose) M K
        (P1SolCone.βW Bt V a b c) :=
  hT (shrinkWriters_all Bt) (factor0Hyp_cone Bt κ hκ V a b d bigBias termBias ρ)

end P1P5.Cone

#print axioms P1P5.Cone.factor0Hyp_cone
#print axioms P1P5.Cone.cone_of_target
