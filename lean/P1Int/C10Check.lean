import P1Int.D5AsmDefs
import P1C10.FieldClosed

/-! # Check (P1-lean-integ): `P1C10.c10_field_closed` is exactly the hypothesis `hc10Step` of `D5StepsAsmTarget`
at `H = trueH hH`, with `dims := gdims` (`gdims .. |x| = fixedDims ..` by `rfl`). No bridge is needed. -/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

example {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
    (cnt : ℕ → ℕ) (hcnt : cnt 9 = P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias))
    (ni : ℕ) (hni : P1ChkGreedy.cntBase (fixedDims Bt V a b x d bigBias termBias) ≤ ni)
    (ck : ℕ → (Fin (fixedM Bt a b x) → Bool) → ℕ → Bool)
    (hck : ∀ u i, ck 9 u i = true ↔
      P1C10.C10w (P1C10.fx10 Bt) (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) :
    ∀ lv < (fixedIndex Bt V a b x d bigBias termBias cnt).top, ∀ u,
      (∀ j < 5 + 2 * lv, (fixedGroups Bt κ hκ V a b x d bigBias termBias
          (trueH Bt κ hκ V a b x d bigBias termBias hH) bs l Wof).P
        (fixedIndex Bt V a b x d bigBias termBias cnt).top j u) →
      ((∀ i < ni, i < (fixedIndex Bt V a b x d bigBias termBias cnt).cnt 9 →
          (fixedIndex Bt V a b x d bigBias termBias cnt).lev 9 i = lv → ck 9 u i = true) ↔
        (fixedGroups Bt κ hκ V a b x d bigBias termBias
          (trueH Bt κ hκ V a b x d bigBias termBias hH) bs l Wof).c10 lv u) :=
  P1C10.c10_field_closed Bt κ hκ V a b x d bigBias termBias hH (gdims Bt V a b d bigBias termBias) rfl
    bs l Wof cnt hcnt ni hni ck hck

end P11

end P1Int
