import P1SolCone.PhaseKernelCode

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open private levelConstant from P1Wit.SpaceFacts

theorem cachedBall_eq {T : Type}
    (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool) (l : ℕ) (clock : Tally)
    (root : ℕ) (rs : List ℕ) (hr : root ∈ rs) (r : ℕ) (hr3 : r ≤ 3)
    (hs : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length)
    (data data' : ℕ → Option T)
    (hd : ∀ z ∈ rawWalk extra u (actualPhaseHeader D u l 0 clock) rs 3, data z = data' z) :
    let h := actualPhaseHeader D u l 0 clock
    let walk := rawWalk extra u h rs 3
    ballList (cachedValidNeighbors h (rawRoundCache extra u h walk)) data root r =
      ballList (validRawNeighbors D u l) data' root r := by
  intro h walk
  have cover (j : ℕ) (hj : j ≤ 3) : bfs (validRawNeighbors D u l) root j ⊆ walk := by
    dsimp only [walk,h]
    rw [rawWalk_eq extra D u l 0 clock rs 3 hs hw]
    exact bfs_subset_walkAddresses hr (validRawNeighbors_subset D u l) hj
  apply ballList_congr_on
  · intro j hj z hz
    exact cachedValidNeighbors_eq extra D u l 0 clock walk z (cover j (hj.le.trans hr3) hz) hs hw
  · intro z hz
    exact hd z (cover r hr3 hz)

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (V : C1Challenge.Machine)
  (a b d bigBias termBias : ℕ)

local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w

theorem cachedPhaseKernel_eq {F : Type} (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (dH : ℕ) (u : List Bool) (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top)
    (keys : List KeyCode) (q : KeyCode) (hq : q ∈ keys) (pad : Tally) (cap : ℕ) (ps : List KeyCode) :
    let h := actualPhaseHeader (Dobs w) u l 0 (Clock w)
    let ctx := phaseLocalOf (levelConstant S) (kernelFieldKeys dH) u h pad cap keys
    (cachedPhaseKernel shr ref dH (ctx,q,ps)).val =
      phaseKernel ⟨fun i _ z => (shr (i,z)).val, fun z => (ref z).val⟩ pad dH (Dobs w) u l q ps := by
  let D := Dobs w
  let clock := Clock w
  intro h ctx
  let extra := kernelFieldKeys dH
  let roots := phaseRoots (levelConstant S) h keys
  let ys := rawWalk extra u h roots 3
  let c := rawRoundCache extra u h ys
  let p : PhaseKernelInput := (ctx,q,ps)
  let α := (D.lv l).slotW
  let γ := (D.lv (l+1)).laneW
  let factor := P1SolC10P.SolC10prog.childFactor h
  let root := kernelForebear p
  let shape := phaseShape D l
  have shapeEq := conePhaseShape_eq B V a b d bigBias termBias (P1Batch.bval w) l hl
  have old : P1C10.slotBits D l = α := congrArg PhaseShape.inDegree shapeEq
  have hg : shape.outLanes = γ := congrArg PhaseShape.outLanes shapeEq
  have hs : shape.isShrink = (D.lv l).shrink := conePhaseShape_kind B V a b d bigBias termBias (P1Batch.bval w) l hl
  have horig : h = P1SolC10P.SolC10prog.actualHead D u l 0 clock := phaseHeader_eq_C10 D u l 0 clock
  have hfit := coneClock_fits_C10 B V a b d bigBias termBias w l hl
  have hfactor : factor = (if (D.lv l).shrink then 2 ^ J α else 2 ^ α) := by
    unfold factor
    rw [horig, P1SolC10P.SolC10prog.childFactor_actual hfit, old]
  have hroot : root ∈ roots := by
    have hr := phaseRoots_mem (levelConstant S) h keys q hq
    have r := coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le
    rw [rawPhaseRoot_eq (levelConstant S) D u l 0 α q.1.1 clock r.slotW_le r.slots_eq] at hr
    change q.1.1 / factor ∈ roots
    rw [hfactor]
    exact hr
  have hwidth := coneClock_field B V a b d bigBias termBias w l hl.le
  have hslots := coneClock_slots B V a b d bigBias termBias w l hl.le
  have havail (z : ℕ) (hz : z ∈ ys) :
      ∀ k ∈ P1SolC10P.SolC10prog.oldKeyList dH (P1SolC10P.SolC10prog.actualHead D u l 0 clock) z,
        P1SolC10P.SolC10prog.tableRead c k = P1SolC10P.SolC10prog.fieldAt u k := by
    rw [← horig]
    exact kernelFieldKeys_read dH u h ys z hz
  have hold : P1SolC10P.SolC10prog.oldBits h = α := by
    rw [horig, P1SolC10P.SolC10prog.oldBits_actual, old]
  have bit : phaseShrinkBit h = (D.lv l).shrink := phaseShrinkBit_eq D u l 0 clock
  have parent : root = q.1.1 / factor := rfl
  change (cachedPhaseKernel shr ref dH p).val = _
  unfold cachedPhaseKernel phaseKernel
  change (bif phaseShrinkBit h then
      shr (P1SolC10P.SolC10prog.oldBits h,cachedShrinkKIn dH p) else ref (cachedRefreshKIn dH p)).val =
    (bif shape.isShrink then
      (shr (shape.inDegree,readShrinkKIn pad D u l shape.inDegree shape.outLanes q.1 ps q.2)).val
      else (ref (readRefreshKIn D u l shape.inDegree shape.outLanes dH q.1 ps q.2)).val)
  rw [bit, hs, hold, hg, show shape.inDegree = α from old]
  cases hkind : (D.lv l).shrink
  · simp only [Bool.cond_false]
    apply congrArg (fun z => (ref z).val)
    have ball : cachedRefreshBall dH h c root =
        ballList (nbOf refreshNbrs (decR α γ dH D u l))
          (fun z => (decR α γ dH D u l z).map codeRefreshDatum) root 1 := by
      rw [← validRawNeighbors_refresh D u l α γ dH
        (coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le).slots_eq]
      exact cachedBall_eq extra D u l clock root roots hroot 1 (by decide) hslots hwidth _ _
        (fun z hz => by
          rw [horig, P1SolC10P.SolC10prog.readRefresh_actual hfit hkind dH z c (havail z hz), old])
    unfold cachedRefreshKIn readRefreshKIn
    change (((root,cachedRefreshBall dH h c root),(q.1.1 % factor,q.1.2)), (ps,q.2)) = _
    rw [ball, parent, hfactor]
    simp only [hkind, ↓reduceIte]
    rfl
  · simp only [Bool.cond_true]
    apply congrArg (fun z => (shr (α,z)).val)
    have ball : cachedShrinkBall dH h c root =
        ballList (nbOf shrinkNbrs (decS α γ D u l))
          (fun z => (decS α γ D u l z).map codeShrinkDatum) root 3 := by
      rw [← validRawNeighbors_shrink D u l α γ
        (coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le).slots_eq]
      exact cachedBall_eq extra D u l clock root roots hroot 3 le_rfl hslots hwidth _ _
        (fun z hz => by
          rw [horig, P1SolC10P.SolC10prog.readShrink_actual hfit hkind dH z c (havail z hz), old])
    have lay : rawRead h c .layout 0 = rdLayout D u l := rawRoundCache_layout extra D u l 0 clock ys (hwidth .layout)
    unfold cachedShrinkKIn readShrinkKIn
    change packShrinkKIn ((((root,cachedShrinkBall dH h c root),decide (rawRead h c .layout 0 = 1)),
      (q.1.1 % factor,q.1.2)),(ps,q.2)) pad = _
    rw [ball, lay, parent, hfactor]
    simp only [hkind, ↓reduceIte]
    rfl

end

end P1SolCone.SolCone
