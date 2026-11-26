import P1C10.Field
import P1C10.Fix
import P1Int.FormGroups

/-!
# P1C10.FieldFixed: the field `c10` of `D5Steps` at the integration's fixed groups and index (lane P1-lean-c10wire)

For `G = fixedGroups .. H bs l Wof` and `X = fixedIndex .. cnt` (Interfaces/P1Int/FormGroups.lean, p1intB-92) with
`cnt 9 = cntBase (fixedDims ..)` and family 9 = `C10w fx dims` (`dims |x| = fixedDims ..`), the core gives the field.
`d5_c10_field_true`: the same for `H = trueH ..` and `fx = fx10 Bt`, from `C10CoreTarget`.
-/

namespace P1C10

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Wit

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **The field `c10` at the fixed groups and index**, from the core. -/
theorem d5_c10_field_fixed (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) (fx : C10Fix)
    (hcore : C10CoreStmt Bt κ hκ V a b x d bigBias termBias H fx)
    (dims : ℕ → Dims) (hD : dims x.length = P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
    (cnt : ℕ → ℕ) (hcnt : cnt 9 = P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias))
    (ni : ℕ) (hni : P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias) ≤ ni)
    (ck : ℕ → (Fin (P1Int.P11.fixedM Bt a b x) → Bool) → ℕ → Bool)
    (hck : ∀ u i, ck 9 u i = true ↔ C10w fx dims x (List.ofFn u) i) :
    let X := P1Int.P11.fixedIndex Bt V a b x d bigBias termBias cnt
    let G := P1Int.P11.fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof
    ∀ lv < X.top, ∀ u, (∀ j < 5 + 2 * lv, G.P X.top j u) →
      ((∀ i < ni, i < X.cnt 9 → X.lev 9 i = lv → ck 9 u i = true) ↔ G.c10 lv u) :=
  d5_c10_field Bt κ hκ V a b x d bigBias termBias H fx hcore dims hD _ _ ni ck rfl hcnt (fun _ => rfl) hni hck
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)

/-- **The field `c10` for the true records and `fx10`**, from the target of the core. -/
theorem d5_c10_field_true (hcoreT : C10CoreTarget)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (dims : ℕ → Dims) (hD : dims x.length = P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
    (cnt : ℕ → ℕ) (hcnt : cnt 9 = P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias))
    (ni : ℕ) (hni : P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias) ≤ ni)
    (ck : ℕ → (Fin (P1Int.P11.fixedM Bt a b x) → Bool) → ℕ → Bool)
    (hck : ∀ u i, ck 9 u i = true ↔ C10w (fx10 Bt) dims x (List.ofFn u) i) :
    let X := P1Int.P11.fixedIndex Bt V a b x d bigBias termBias cnt
    let G := P1Int.P11.fixedGroups Bt κ hκ V a b x d bigBias termBias
      (P1Int.P11.trueH Bt κ hκ V a b x d bigBias termBias hH) bs l Wof
    ∀ lv < X.top, ∀ u, (∀ j < 5 + 2 * lv, G.P X.top j u) →
      ((∀ i < ni, i < X.cnt 9 → X.lev 9 i = lv → ck 9 u i = true) ↔ G.c10 lv u) :=
  d5_c10_field_fixed Bt κ hκ V a b x d bigBias termBias _ (fx10 Bt)
    (hcoreT Bt κ hκ V a b x d bigBias termBias hH (fx10 Bt) (fx10_shrink_ok Bt) (fx10_refresh_ok Bt) rfl)
    dims hD bs l Wof cnt hcnt ni hni ck hck

end

end P1C10

#print axioms P1C10.d5_c10_field_fixed
#print axioms P1C10.d5_c10_field_true
