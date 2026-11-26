import P1Int.WLinkProof
import P1Int.D5AsmDefs

/-!
# The W link for the true records with the cone's `Wof` (P1-lean-integ, statement only)

`WLinkTrueTarget`: with eval's ONE `Wof` term (board 2240: `Wof gdims Bt.recordLimit Bt.growthConstant (Mbar Bt V a b)
(2 ^ S.expanderExponent) values hf.choose`, `values` under `ScheduleKernelsOK`, `hf : Factor0Hyp .. ρ bset` with
`ρ = Fintype.equivFin`), the evaluation from the code of every tuple of `trueH` is `C.W`. Proof route:
`P1SolCone.wof_def_ok` (tape order of trueH = `fixedTapeOrder` = `Fintype.equivFin`), `branchExtras_true`, EncFits.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Target: the W link for `trueH` with the cone's `Wof`.** -/
def WLinkTrueTarget : Prop :=
  ∀ (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias) (values : KernelValues F)
    (_hv : ScheduleKernelsOK Bt κ hκ values)
    (hf : Factor0Hyp Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) P1Benes.NetBridge.bset),
    EncFits Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) →
    ∀ (t : (fixedCD Bt κ hκ V a b x).Tup d) (i : Fin ((fixedCD Bt κ hκ V a b x).P t.1 t.2.1)),
      Wof (gdims Bt V a b d bigBias termBias) Bt.recordLimit Bt.growthConstant (Mbar Bt V a b)
          (2 ^ S.expanderExponent) values hf.choose x
          (List.ofFn (fixedEnc Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) t)) i =
        (fixedCD Bt κ hκ V a b x).W t.1 t.2.1 t.2.2.1 i

end

end P11

end P1Int
