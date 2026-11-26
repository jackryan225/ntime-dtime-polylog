import P1Int.WLinkTrueDefs

/-! # The W link for `trueH` (P1-lean-integ): `wof_def_ok` + `branchExtras_true`. -/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone

theorem wlink_true {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) :
    WLinkTrueTarget Bt κ hκ V a b x d bigBias termBias := by
  intro hH values hv hf hfit t i
  exact wof_def_ok Bt κ hκ V a b d bigBias termBias x (Fintype.equivFin _) values hv hf
    (trueH Bt κ hκ V a b x d bigBias termBias hH) (fun _ => rfl) t (fixedM Bt a b x) (hfit t) i
    (branchExtras_true Bt κ hκ V a b x d bigBias termBias hH hfit t)

end P11

end P1Int

#print axioms P1Int.P11.wlink_true
