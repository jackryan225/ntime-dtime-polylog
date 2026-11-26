import P1SolCone.PhasePreimages
import P1SolCone.PhaseCoverage
import P1SolCone.PhaseGeometry

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1Wrap
open scoped P1ChkFinal.AstraC10
open private levelConstant from P1Wit.SpaceFacts

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def phaseSlotCount (h : PhaseHeader) : ℕ := packetNat h.2.2.2.2 4
def phaseShrinkBit (h : PhaseHeader) : Bool := decide (packetNat h.2.2.2.2 7 = 1)

@[fun_prop] theorem phaseSlotCount_poly : Poly phaseSlotCount := by unfold phaseSlotCount; fun_prop
@[fun_prop] theorem phaseShrinkBit_poly : Poly phaseShrinkBit := by unfold phaseShrinkBit; fun_prop

theorem phaseSlotCount_eq (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) :
    phaseSlotCount (actualPhaseHeader D u l y clock) = (D.lv l).slots := by
  change packetNat (phaseFormat D l) 4 = _
  rw [packetNat_phaseFormat]
  rfl

theorem phaseShrinkBit_eq (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) :
    phaseShrinkBit (actualPhaseHeader D u l y clock) = (D.lv l).shrink := by
  have h : packetNat (phaseFormat D l) 7 = (D.lv l).shrink.toNat := by rw [packetNat_phaseFormat]; rfl
  unfold phaseShrinkBit
  simp only [actualPhaseHeader, h]
  cases (D.lv l).shrink <;> rfl

private def degreeTable {A B : Type} (aMax : ℕ) (f : ℕ → A → B) : List (ℕ × (A → B)) :=
  (List.range (aMax+1)).map (fun a => (2 ^ a,f a))

theorem dispatchDegree_poly {A B : Type} [Codec A] [Codec B]
    (fallback : B) (aMax : ℕ) (f : ℕ → A → B) (h : ∀ a ≤ aMax, Poly (f a)) :
    Poly (dispatchKernel fallback (degreeTable aMax f)) := by
  apply dispatchKernel_poly
  intro p hp
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
  exact h a (Nat.lt_succ_iff.mp (List.mem_range.mp ha))

theorem dispatchDegree_eq {A B : Type} (fallback : B) (aMax : ℕ) (f : ℕ → A → B)
    (a : ℕ) (ha : a ≤ aMax) (x : A) :
    dispatchKernel fallback (degreeTable aMax f) (2 ^ a,x) = f a x := by
  apply dispatchKernel_on
  · simp only [degreeTable,List.map_map,Function.comp_def]
    exact (List.nodup_range).map (fun i j hij => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) h)) hij
      · exact (Nat.ne_of_gt (Nat.pow_lt_pow_right (by decide) h)) hij)
  · exact List.mem_map.mpr ⟨a,List.mem_range.mpr (Nat.lt_succ_of_le ha),rfl⟩

def rawPhaseRoot (aMax : ℕ) (h : PhaseHeader) (y : ℕ) : ℕ :=
  bif phaseShrinkBit h then
    dispatchKernel 0 (degreeTable aMax (fun a z => z / 2 ^ J a)) (phaseSlotCount h,y)
  else y / phaseSlotCount h

theorem rawPhaseRoot_poly (aMax : ℕ) : Poly (fun p : PhaseHeader × ℕ => rawPhaseRoot aMax p.1 p.2) := by
  unfold rawPhaseRoot
  have f := dispatchDegree_poly 0 aMax (fun a z => z / 2 ^ J a)
    (fun a _ => poly_divNat Code.Poly.identity (Code.Poly.const (2 ^ J a)))
  exact Poly.choose (Easy.fst.poly.compose phaseShrinkBit_poly)
    (((Easy.fst.poly.compose phaseSlotCount_poly).pair Easy.snd.poly).compose f)
    (poly_divNat Easy.snd.poly (Easy.fst.poly.compose phaseSlotCount_poly))

theorem rawPhaseRoot_eq (aMax : ℕ) (D : Dims) (u : List Bool) (l y a z : ℕ) (clock : Tally)
    (ha : a ≤ aMax) (hs : (D.lv l).slots = 2 ^ a) :
    rawPhaseRoot aMax (actualPhaseHeader D u l y clock) z =
      z / (if (D.lv l).shrink then 2 ^ J a else 2 ^ a) := by
  unfold rawPhaseRoot
  rw [phaseShrinkBit_eq,phaseSlotCount_eq,hs]
  cases hk : (D.lv l).shrink
  · rfl
  · exact dispatchDegree_eq 0 aMax _ a ha z

def rawPhasePreimages (aMax : ℕ) (p : PhaseHeader × FieldCache × PositionCode) : List PositionCode :=
  bif phaseShrinkBit p.1 then
    dispatchKernel [] (degreeTable aMax (fun a q => rawShrinkPreimages a q.1 q.2.1 q.2.2)) (phaseSlotCount p.1,p)
  else [rawRefreshPreimage p.1 p.2.2]

theorem rawPhasePreimages_poly (aMax : ℕ) : Poly (rawPhasePreimages aMax) := by
  unfold rawPhasePreimages
  let A := PhaseHeader × FieldCache × PositionCode
  have shrink := dispatchDegree_poly ([] : List PositionCode) aMax
    (fun a (q : A) => rawShrinkPreimages a q.1 q.2.1 q.2.2) (fun a _ => rawShrinkPreimages_poly a)
  have h : Poly (fun p : A => (p.1, p.2.2)) := by unfold A; fun_prop
  have refresh := ((h.compose rawRefreshPreimage_poly).pair (Code.Poly.const ([] : List PositionCode))).compose Poly.cons
  exact Poly.choose (Easy.fst.poly.compose phaseShrinkBit_poly)
    (((Easy.fst.poly.compose phaseSlotCount_poly).pair Code.Poly.identity).compose shrink) refresh

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ)

theorem rawPhasePreimages_eq (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (w : Bits.Word) (l y : ℕ) (p : PositionCode) (roots : List ℕ)
    (hl : l < (coneDims Bt V a b d bigBias termBias (P1Batch.bval w)).top) :
    let n := P1Batch.bval w
    let D := coneDims Bt V a b d bigBias termBias n
    let clock := coneReadClock Bt V a b bigBias termBias w
    let h := actualPhaseHeader D u l y clock
    let visited := rawWalk extra u h roots 3
    rawPhaseRoot (levelConstant S) h p.1 ∈ roots →
    rawPhasePreimages (levelConstant S) (h,rawRoundCache extra u h visited,p) = phasePreimages D u l p := by
  intro n D clock h visited hroot
  let X := D.lv l
  let Y := D.lv (l+1)
  have geom := coneDims_rowBounds Bt V a b d bigBias termBias n l hl.le
  have geom' := coneDims_rowBounds Bt V a b d bigBias termBias n (l+1) hl
  have haxis : X.lanes * X.slots ≤ clock.length :=
    (coneAxisClock_fits Bt V a b d bigBias termBias w l hl.le).trans (coneReadClock_axes Bt V a b bigBias termBias w)
  have hs : X.slots ≤ clock.length :=
    (Nat.le_mul_of_pos_left _ (by rw [geom.lanes_eq]; exact Nat.two_pow_pos _)).trans haxis
  have hlanes : X.lanes ≤ clock.length :=
    (Nat.le_mul_of_pos_right _ (by rw [geom.slots_eq]; exact Nat.two_pow_pos _)).trans haxis
  have hw (m : Mem) : D.width (secLev l m) ≤ clock.length :=
    (coneLevelWidth_le Bt V a b d bigBias termBias n l hl.le m).trans
      (coneReadClock_width Bt V a b bigBias termBias w)
  have hkind := conePhaseShape_kind Bt V a b d bigBias termBias n l hl
  have hshape := conePhaseShape_eq Bt V a b d bigBias termBias n l hl
  have hα : (phaseShape D l).inDegree = X.slotW := congrArg PhaseShape.inDegree hshape
  have hγ : (phaseShape D l).outLanes = Y.laneW := congrArg PhaseShape.outLanes hshape
  have hbits : phaseShrinkBit h = X.shrink := phaseShrinkBit_eq D u l y clock
  have hd : phaseSlotCount h = 2 ^ X.slotW := (phaseSlotCount_eq D u l y clock).trans geom.slots_eq
  have e : rawPhaseRoot (levelConstant S) h p.1 =
      p.1 / (if X.shrink then 2 ^ J X.slotW else 2 ^ X.slotW) :=
    rawPhaseRoot_eq _ D u l y X.slotW p.1 clock geom.slotW_le geom.slots_eq
  unfold rawPhasePreimages phasePreimages
  dsimp only
  rw [hbits,hkind,hα,hγ]
  cases hsh : X.shrink
  · simp only [Bool.cond_false]
    rw [rawRefreshPreimage_eq D u l y X.slotW Y.laneW clock p geom.slots_eq geom'.lanes_eq]
  · simp only [Bool.cond_true]
    rw [hd,dispatchDegree_eq _ _ _ X.slotW geom.slotW_le]
    have hroot' : p.1 / 2 ^ J X.slotW ∈ roots := by simpa only [e,hsh,↓reduceIte] using hroot
    have cy (z : ℕ) (hz : z ∈ p.1 / 2 ^ J X.slotW :: actualRawNeighbors D u l (p.1 / 2 ^ J X.slotW)) :
        z ∈ visited := by
      dsimp only [visited]
      rw [rawWalk_eq extra D u l y clock roots 3 hs hw]
      exact rawWalk_covers_neighbor _ roots hroot' (by decide : 0 < 3) z hz
    have hg := (coneDims_step Bt V a b d bigBias termBias n l hl).loss
    have hg' : X.laneW = packingLaneBits X.slotW Y.laneW := by
      change X.laneW = (if X.shrink then _ else _) + Y.laneW at hg
      simp only [hsh, ↓reduceIte] at hg
      have hzero : X.laneW = packingLaneBits X.slotW 0 + Y.laneW := hg
      exact hzero.trans (by unfold packingLaneBits; omega)
    have hfull : X.lanes = 2 ^ packingLaneBits X.slotW Y.laneW := geom.lanes_eq.trans (congrArg (2 ^ ·) hg')
    exact rawShrinkPreimages_eq extra D u l y _ _ clock visited p cy geom.slots_eq hs hfull hlanes geom'.lanes_eq hw

end P1SolCone.SolCone
