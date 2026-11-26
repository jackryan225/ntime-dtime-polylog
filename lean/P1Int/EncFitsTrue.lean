import P1Int.EncFitsDefs

noncomputable section

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.encFits_true {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) :
    P1Int.P11.EncFitsTrueTarget Bt κ hκ V a b d bigBias termBias := by
  intro _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    (witness_fits Bt κ hκ (portConsts Bt) V 1 le_rfl (portConsts_b0 Bt)
      (portConsts_C2 Bt) d bigBias termBias a b)
  refine ⟨n₀, ?_⟩
  intro x hx hH t
  rw [P1Wit.p11Tuple_payload_length]
  exact @hn₀ x.length hx inferInstance inferInstance t.1 t.2.1

example : ∀ {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ),
    P1Int.P11.EncFitsTrueTarget Bt κ hκ V a b d bigBias termBias := @P1Int.P11.encFits_true

end

#print axioms P1Int.P11.encFits_true
