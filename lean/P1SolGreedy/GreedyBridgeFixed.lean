import P1SolGreedy.GreedyBridgeLocate
import P1ChkFinal.GreedyBridgeE

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Wit.SolSpace P1Int P1Int.P11 P1Int.SolTrueRecords
open P1ChkFinal.EnergyFit
open private runPhases runPhases_length follows_execute from P1Wit.SpaceFacts
open private live_execute from P1Int.RecordsFitProof
open private levelFrom from P1Int.WLinkProof

set_option maxHeartbeats 800000 in
theorem fixed_located {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)
    (hE : EnergyFitTarget Bt κ hκ V a b x d bigBias termBias)
    {ℓ : ℕ} (hℓ : ℓ < (fixedDims Bt V a b x d bigBias termBias).top)
    (u : Fin (fixedM Bt a b x) → Bool) (q : (fixedCD Bt κ hκ V a b x).Tup d)
    (ht : SecEq Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u q secTrit)
    (hbelow : LevUpTo Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u q ℓ)
    (hpanel : ∀ m, panelKind m = true → SecEq Bt κ hκ V a b x d bigBias termBias
      (trueH Bt κ hκ V a b x d bigBias termBias hH) u q (secLev ℓ m)) :
    LocatedRow Bt κ hκ (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) ℓ
      (greedyG Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) ℓ u) := by
  let t := lpTime a b x.length
  let T := P1Wrap.Params.T (portConsts Bt) t
  let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  let X := routedState (S := S) V (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t) q.1
  let E := Bt.execute κ hκ T hn X
  let o := executeOrigins Bt κ hκ T hn X
  let D := fixedDims Bt V a b x d bigBias termBias
  let H := trueH Bt κ hκ V a b x d bigBias termBias hH
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let w := List.ofFn u
  have f : ExecFits D E 0 := hH.1.choose_spec.choose_spec.2.1 q.1
  have hinj : TablesInjective D E 0 (tableTree Bt κ hκ D E o 0) := hH.2 q.1
  let P := panelsFromOrigin Bt κ hκ D E o 0 f
  let Tm := termsFromOrigin Bt κ hκ D E o 0 f hinj
  have hlevel (z : E.Choices) (j : Fin (D.top + 1)) :
      R.level q.1 z j = levelFrom E P Tm z j (Nat.zero_le _) := rfl
  have hprev : readsBefore w E P Tm q.2.1 ℓ := by
    intro j _ hj m
    rw [← hlevel]
    exact (section_iff_reads R w q j m).mp (hbelow j.val hj m)
  let j : Fin (D.top + 1) := ⟨ℓ, Nat.lt_succ_of_lt hℓ⟩
  have hp : ∀ m, panelKind m = true →
      ReadsKind D w ℓ (levelFrom E P Tm q.2.1 j (Nat.zero_le _)) m := by
    intro m hm
    rw [← hlevel]
    exact (section_iff_reads R w q j m).mp (hpanel m hm)
  let G := greedyG Bt κ hκ V a b x d bigBias termBias H ℓ u
  have hg : G ↔ ∃ z : E.Choices, readsBefore w E P Tm z (ℓ + 1) := by
    refine (greedy_iff_branch Bt κ hκ V a b x d bigBias termBias H u q hℓ.le ht).trans ?_
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      intro i _ hi m
      rw [← hlevel]
      exact hz i hi m
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      intro i hi m
      change ReadsKind D w i.val (R.level q.1 z i) m
      rw [hlevel]
      exact hz i (Nat.zero_le _) hi m
  have hr : E.Bounded Bt.recordLimit (Bt.records κ hκ T hn X) :=
    (Procedure.repeat_recordBounds (Bt.recordBounds κ hκ) _ T (P1Wrap.Params.h t)
      (Nat.add_sub_of_le hn).symm X).1
  refine locate Bt κ hκ D w ℓ hℓ G E o q.2.1 0 f hinj (Bt.records κ hκ T hn X) hr
    (runPhases S T) (follows_execute Bt κ hκ T hn X) (run_laneLoss (S := S) T) ?_ ?_
    (live_execute Bt κ hκ T hn X) (hE q.1) (Nat.zero_le _) hprev hp hg
  · intro i
    have hpos : X.positions = initialPositions (toOAI V) 1 t :=
      P1Net.rn_positions (toOAI V) (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t) q.1 (four_le_baseDegree S)
    rw [Nat.zero_add, hpos]
    rfl
  · rw [runPhases_length]
    let W := P1Net.tupWidth (toOAI V) (P1Wrap.Params.B t)
    let M := Bt.growthConstant ^ T * (W + 1)
    have hw : X.maxWireWidth ≤ W := initial_width_le (toOAI V) 1 (four_le_baseDegree S) q.1
    have hpow : Bt.recordLimit ^ ((S.steps + 1) * T) ≤ Bt.growthConstant ^ T := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (le_max_right _ _) _
    have hM := Nat.mul_le_mul hpow (Nat.succ_le_succ hw)
    have hclog : M + 1 ≤ 2 ^ Nat.clog 2 (M + 1) := Nat.le_pow_clog (by decide) _
    have hD : 2 ^ Nat.clog 2 (M + 1) ≤ 2 ^ D.wW :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
    exact hM.trans_lt ((Nat.lt_succ_self _).trans_le (hclog.trans hD))

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.fixed_located
