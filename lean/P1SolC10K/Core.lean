import P1C10.Field
import P1SolC10K.Branch

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Wit P1Wit.SolWitfill P1Wit.SolSpace P1Wrap
open P1Int P1Int.P11 P1Int.SolTrueRecords P1C10 P1SolC10K.Sol
open private follows_execute layoutRows levelDims runPhases runPhases_length from P1Wit.SpaceFacts

theorem P1SolC10K.c10Core : P1C10.C10CoreTarget := by
  intro k _ S Bt F _ _ κ hκ V a b x d bigBias termBias hH fx hS hR hd ℓ hℓ u q hsrc
  let t := lpTime a b x.length
  let T := Params.T (portConsts Bt) t
  let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  let X := routedState (S := S) V (Params.B t) (Params.I 1 t) q.1
  let E := Bt.execute κ hκ T hn X
  let o := executeOrigins Bt κ hκ T hn X
  let D := fixedDims Bt V a b x d bigBias termBias
  let H := trueH Bt κ hκ V a b x d bigBias termBias hH
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  have f : ExecFits D E 0 := hH.1.choose_spec.choose_spec.2.1 q.1
  have hinj : TablesInjective D E 0 (tableTree Bt κ hκ D E o 0) := hH.2 q.1
  have hrec : E.Bounded Bt.recordLimit (Bt.records κ hκ T hn X) :=
    (Procedure.repeat_recordBounds (Bt.recordBounds κ hκ) _ T (Params.h t) (Nat.add_sub_of_le hn).symm X).1
  let L (j : Fin (D.top + 1)) := branchRecord Bt κ hκ D E o q.2.1 0 f hinj j (Nat.zero_le _)
  have sec (j : Fin (D.top + 1)) (m : Mem) :
      SecEq Bt κ hκ V a b x d bigBias termBias H u q (secLev j.val m) ↔
        ReadsSection D (List.ofFn u) j.val (L j) m := by
    have hrecord : R.level q.1 q.2.1 j = L j := rfl
    rw [← hrecord]
    exact tupleSection_iff (List.ofFn u) R q j m
  let j : Fin (D.top + 1) := ⟨ℓ, Nat.lt_succ_of_lt hℓ⟩
  let j' : Fin (D.top + 1) := ⟨ℓ + 1, Nat.succ_lt_succ hℓ⟩
  have hread : ∀ m, ReadsSection D (List.ofFn u) ℓ (L j) m := fun m => (sec j m).1 (hsrc m)
  have lanes (l a' g : ℕ) (Z : State a' g) (fit : PanelFits D (D.lv l) Z) : (D.lv l).laneW = g :=
    fixedLaneWidth Bt V a b x d bigBias termBias l fit
  have hstep :
      (∀ Y < (D.lv (ℓ + 1)).bases, C10at fx D (List.ofFn u) ℓ Y) ↔
        ∀ m, panelKind m = true → ReadsSection D (List.ofFn u) (ℓ + 1) (L j') m := by
    refine branchStep Bt κ hκ (fx := fx) ⟨hS, hR, hd⟩ D (List.ofFn u) lanes E o q.2.1 0 f hinj _ hrec
      (runPhases S T) (follows_execute Bt κ hκ T hn X) (run_laneLoss (S := S) T) ?_ ?_
      ℓ (Nat.zero_le _) hℓ hread
    · intro i
      have hpos : X.positions = initialPositions (toOAI V) 1 t :=
        P1Net.rn_positions (toOAI V) (Params.B t) (Params.I 1 t) q.1 (four_le_baseDegree S)
      rw [Nat.zero_add, hpos]
      rfl
    · rw [runPhases_length]
      let W := P1Net.tupWidth (toOAI V) (Params.B t)
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
  apply hstep.trans
  apply forall_congr'
  intro m
  apply forall_congr'
  intro _
  exact (sec j' m).symm

#print axioms P1SolC10K.c10Core
