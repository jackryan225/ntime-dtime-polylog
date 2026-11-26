import P1SolCone.ConeFinish
import P1SolCone.KernelDispatch

namespace P1SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int Module

theorem whyp_cone {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
    (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) {Dd : ℕ} (bs : Basis (Fin Dd) (ZMod 2) F) :
    P1P5.Cone.ConeTarget Bt κ hκ V a b d bigBias termBias ρ bs := by
  intro hs hf
  obtain ⟨shr,ref,hshr,href,hvalues⟩ := SolCone.scheduleKernels_poly Bt κ hκ hs
  obtain ⟨e,hfactor,_⟩ := hf.choose_spec
  obtain ⟨c,hc⟩ :=
    SolCone.coneExecution_interface Bt V a b d bigBias termBias bs shr ref hshr href hf.choose e hfactor
  exact ⟨SolCone.numericKernelValues shr ref,c,hvalues,hc⟩

end P1SolCone

#print axioms P1SolCone.whyp_cone

#print axioms P1SolCone.wof_def_ok
