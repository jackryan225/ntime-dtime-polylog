import P1ChkFinal.GreedyBridge
import P1ChkFinal.GreedyStepAll
import P1Int.D5AsmDefs

/-!
# P1ChkFinal.GreedyFieldTarget: the field `greedy` of `D5Steps` at integ's fixed index and groups (statement; P1-lean-greedy)

The exact field type of `P1Int.P11.D5StepsAsmTarget` (Interfaces/P1Int/D5AsmDefs.lean:87-92) at `H = trueH hH`, from:
the two bridges (`BridgeShrinkTarget`, `BridgeRefreshTarget`; Astra P1-astra-grbridge), the decisions `ck 4 .. ck 8` of the
families C5fam, C6fam, C7all (D15), C8fam, C9fam at `gdims` and `genuineAg gdims`, the counts and their fit in `ni`.
Pieces (PROVED): `GreedyIndex.greedy_shrink_step` (grd-33), `C7R.greedy_refresh_step` (grd-15), the `_out` lemmas, `C7all_out`;
premise: `P 3 = c4G` (level 0), `P (3 + 2 lv) = c10G (lv - 1)` (level `lv ≥ 1`).
-/

namespace P1ChkFinal.GreedyField

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry OAI.Computability.VPVNP.Compression.Refresh
open P1Wit P1ChkGreedy P1SolGreedy P1Int P1Int.P11 P1ChkFinal.C7R P1ChkFinal.GreedyBridge

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
  (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)

/-- **Target: the field `greedy`** (statement). -/
def GreedyFieldTarget : Prop :=
  BridgeShrinkTarget Bt κ hκ V a b x d bigBias termBias hH →
  BridgeRefreshTarget Bt κ hκ V a b x d bigBias termBias hH →
  ∀ (bs : Module.Basis (Fin d) (ZMod 2) F) (lmap : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
    (ck : ℕ → (Fin (fixedM Bt a b x) → Bool) → ℕ → Bool) (ni : ℕ) (cnt : ℕ → ℕ),
  (∀ u i, ck 4 u i = true ↔ C5fam (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  (∀ u i, ck 5 u i = true ↔
    C6fam (gdims Bt V a b d bigBias termBias) (genuineAg (gdims Bt V a b d bigBias termBias)) x (List.ofFn u) i) →
  (∀ u i, ck 6 u i = true ↔
    C7all S.graph (Nat.two_pow_pos S.expanderExponent) (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh
      Bt.shrink (gdims Bt V a b d bigBias termBias) (genuineAg (gdims Bt V a b d bigBias termBias)) x (List.ofFn u) i) →
  (∀ u i, ck 7 u i = true ↔
    C8fam Bt.shrink (gdims Bt V a b d bigBias termBias) (genuineAg (gdims Bt V a b d bigBias termBias)) x
      (List.ofFn u) i) →
  (∀ u i, ck 8 u i = true ↔ C9fam (gdims Bt V a b d bigBias termBias) x (List.ofFn u) i) →
  cnt 4 = cntBase (fixedDims Bt V a b x d bigBias termBias) →
  cnt 5 = cntBase (fixedDims Bt V a b x d bigBias termBias) →
  cnt 6 = cnt7all (fixedDims Bt V a b x d bigBias termBias) (genuineAg (gdims Bt V a b d bigBias termBias) x.length) →
  cnt 7 = cntBase (fixedDims Bt V a b x d bigBias termBias) →
  cnt 8 = cntLev (fixedDims Bt V a b x d bigBias termBias) →
  (∀ c, 4 ≤ c → c ≤ 8 → cnt c ≤ ni) →
  ∀ lv < (fixedIndex Bt V a b x d bigBias termBias cnt).top, ∀ u,
    (∀ j < 4 + 2 * lv, (fixedGroups Bt κ hκ V a b x d bigBias termBias
      (trueH Bt κ hκ V a b x d bigBias termBias hH) bs lmap Wof).P (fixedIndex Bt V a b x d bigBias termBias cnt).top j u) →
    ((∀ c, 4 ≤ c → c ≤ 8 → ∀ i < ni, i < (fixedIndex Bt V a b x d bigBias termBias cnt).cnt c →
        (fixedIndex Bt V a b x d bigBias termBias cnt).lev c i = lv → ck c u i = true) ↔
      (fixedGroups Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) bs lmap Wof).greedy
        lv u)

end P1ChkFinal.GreedyField
