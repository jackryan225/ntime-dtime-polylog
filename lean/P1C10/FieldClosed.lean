import P1C10.FieldFixed
import P1SolC10K.Core

/-!
# P1C10.FieldClosed: the field `c10` of `D5Steps` for the true records, closed (lane P1-lean-c10wire)

Astra P1-astra-c10core (DONE 14:22Z, runner check round 4) proved `P1SolC10K.c10Core : P1C10.C10CoreTarget`; its seven
files are compiled UNCHANGED (research/p1/lean/C10/accepted/P1SolC10K.sha256). With `d5_c10_field_true` the field `c10`
of `P1Int.P11.D5Steps` holds at integ's `fixedIndex cnt` / `fixedGroups (trueH ..) bs l Wof` for family 9 =
`C10w (fx10 Bt) dims`, with no open input beyond the index data (`dims |x| = fixedDims`, `cnt 9 = cntBase`,
`cntBase ≤ ni`, the decider `ck 9`).
-/

namespace P1C10

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Wit

/-- Statement check: the delivered theorem has exactly the target type. -/
example : C10CoreTarget := P1SolC10K.c10Core

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **The field `c10` of `D5Steps`, closed** (true records `trueH`, recomputations `fx10`). -/
theorem c10_field_closed (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias)
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
  d5_c10_field_true Bt κ hκ V a b x d bigBias termBias P1SolC10K.c10Core hH dims hD bs l Wof cnt hcnt ni hni ck hck

end

end P1C10

#print axioms P1C10.c10_field_closed
