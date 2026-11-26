import P1Int.WLinkTrue
import P1Int.FormSoundAsm
import P1Int.FormCloseAsm
import P1Int.FormFixAsm
import P1Int.FormC14

/-! # The field `form` of `D5Steps` for the true records (P1-lean-integ): `form_of_cut` of the three proved pieces,
with the cone's `Wof` (board 2240), the W link `wlink_true`, `fixed_finP`, and `EncFits` (from `encFits_true`). -/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone

theorem form_true {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias) (values : KernelValues F)
    (hv : ScheduleKernelsOK Bt κ hκ values)
    (hf : Factor0Hyp Bt κ hκ V a b d bigBias termBias (Fintype.equivFin (toOAI V).K) P1Benes.NetBridge.bset)
    (hfit : EncFits Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH))
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (cnt : ℕ → ℕ) :
    FormStmt Bt κ hκ V a b x bigBias termBias bs l (trueH Bt κ hκ V a b x d bigBias termBias hH)
      (fixedIndex Bt V a b x d bigBias termBias cnt)
      (fixedGroups Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) bs l
        (Wof (gdims Bt V a b d bigBias termBias) Bt.recordLimit Bt.growthConstant (Mbar Bt V a b)
          (2 ^ S.expanderExponent) values hf.choose)) :=
  form_of_cut Bt κ hκ V a b x bigBias termBias bs l _ _ _
    (formSound_asm Bt κ hκ V a b x d bigBias termBias _ hfit bs l _
      (wlink_true Bt κ hκ V a b x d bigBias termBias hH values hv hf hfit)
      (fun σ ι => fixed_finP Bt κ hκ V a b x d bigBias termBias σ ι) cnt)
    (formFix_asm Bt κ hκ V a b x d bigBias termBias _ (c14_fix Bt κ hκ V a b x d bigBias termBias _) bs l _ cnt)
    (formClose_asm Bt κ hκ V a b x d bigBias termBias _ hfit (c14_close Bt κ hκ V a b x d bigBias termBias _) bs l _
      (wlink_true Bt κ hκ V a b x d bigBias termBias hH values hv hf hfit)
      (fun σ ι => fixed_finP Bt κ hκ V a b x d bigBias termBias σ ι) cnt)

end P11

end P1Int

#print axioms P1Int.P11.form_true
