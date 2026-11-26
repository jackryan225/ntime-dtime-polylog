import P1SolCone.PhaseStage
import P1SolCone.PhaseWalkTask

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10
open private levelConstant slotCap from P1Wit.SpaceFacts

def phaseVisited (lim : ℕ) (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (h : PhaseHeader) (keys : List KeyCode) : List ℕ :=
  rawWalk extra u h (phaseRoots lim h keys) 3

def phaseIncidence (lim : ℕ) (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (h : PhaseHeader) (keys : List KeyCode) : FieldCache :=
  rawRoundCache extra u h (phaseVisited lim extra u h keys)

def phaseLocalOf (lim : ℕ) (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (h : PhaseHeader) (pad : Tally) (w : ℕ) (keys : List KeyCode) : PhaseLocal :=
  let c := phaseIncidence lim extra u h keys
  let width := fetchPhaseFields u (phaseWidthRequests h c (phaseParents lim h c keys))
  (h,c,width,pad,w)

theorem phaseVisited_covers {z : ℕ} (lim : ℕ) (extra : PhaseHeader × ℕ → List FieldKey)
    (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) (keys : List KeyCode) (q : KeyCode)
    (hq : q ∈ keys) (a : ℕ) (ha : a ≤ lim) (hslots : (D.lv l).slots = 2 ^ a)
    (hs : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length)
    (hz : z ∈ (q.1.1 / (if (D.lv l).shrink then 2 ^ J a else 2 ^ a)) ::
      actualRawNeighbors D u l (q.1.1 / (if (D.lv l).shrink then 2 ^ J a else 2 ^ a))) :
    z ∈ phaseVisited lim extra u (actualPhaseHeader D u l y clock) keys := by
  unfold phaseVisited
  rw [rawWalk_eq extra D u l y clock _ 3 hs hw]
  apply rawWalk_covers_neighbor _ _ _ (by decide : 0 < 3) z hz
  have e := phaseRoots_mem lim (actualPhaseHeader D u l y clock) keys q hq
  rwa [rawPhaseRoot_eq lim D u l y a q.1.1 clock ha hslots] at e

section Concrete

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w

theorem coneClock_slots (w : Bits.Word) (l : ℕ) (hl : l ≤ (Dobs w).top) :
    ((Dobs w).lv l).slots ≤ (Clock w).length := by
  let e := coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl
  exact (Nat.le_mul_of_pos_left _ (by rw [e.lanes_eq]; exact Nat.two_pow_pos _)).trans
    ((coneAxisClock_fits B V a b d bigBias termBias w l hl).trans
      (coneReadClock_axes B V a b bigBias termBias w))

theorem coneClock_field (w : Bits.Word) (l : ℕ) (hl : l ≤ (Dobs w).top) (m : Mem) :
    (Dobs w).width (secLev l m) ≤ (Clock w).length :=
  (coneLevelWidth_le B V a b d bigBias termBias (P1Batch.bval w) l hl m).trans
    (coneReadClock_width B V a b bigBias termBias w)

theorem phaseParent_covered (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top) (keys : List KeyCode)
    (q : KeyCode) (hq : q ∈ keys) (p : PositionCode) (hp : p ∈ phasePreimages (Dobs w) u l q.1) :
    p.1 ∈ phaseVisited (levelConstant S) extra u (actualPhaseHeader (Dobs w) u l 0 (Clock w)) keys := by
  let D := Dobs w
  let c := Clock w
  let α := (D.lv l).slotW
  let γ := (D.lv (l+1)).laneW
  have shape := conePhaseShape_eq B V a b d bigBias termBias (P1Batch.bval w) l hl
  have kind := conePhaseShape_kind B V a b d bigBias termBias (P1Batch.bval w) l hl
  have row := coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le
  apply phaseVisited_covers (levelConstant S) extra D u l 0 c keys q hq α row.slotW_le row.slots_eq
    (coneClock_slots B V a b d bigBias termBias w l hl.le) (coneClock_field B V a b d bigBias termBias w l hl.le)
  unfold phasePreimages at hp
  dsimp only at hp
  rw [kind, show (phaseShape D l).inDegree = α from congrArg PhaseShape.inDegree shape,
    show (phaseShape D l).outLanes = γ from congrArg PhaseShape.outLanes shape] at hp
  change p ∈ (bif (D.lv l).shrink then shrinkPreimages D u l α γ q.1 else [refreshPreimage α γ q.1]) at hp
  cases hb : (D.lv l).shrink
  · have hq : p = refreshPreimage α γ q.1 := by
      simpa only [hb, Bool.cond_false, List.mem_singleton] using hp
    rw [hq]
    simpa only [hb, ite_false, Bool.false_eq_true, refreshPreimage] using
      (List.mem_cons_self : q.1.1 / 2 ^ α ∈ q.1.1 / 2 ^ α :: actualRawNeighbors D u l (q.1.1 / 2 ^ α))
  · have e : p ∈ shrinkPreimages D u l α γ q.1 := by simpa only [hb, Bool.cond_true] using hp
    have hmem := List.mem_dedup.mp (List.mem_filter.mp e).1
    obtain ⟨z,hz,hz'⟩ := List.mem_flatMap.mp hmem
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp hz'
    have hr : (D.lv l).slots = 2 ^ α := row.slots_eq
    simpa only [hb, ite_true, actualRawNeighbors, hr] using hz

theorem phaseLocalOf_parents (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top) (keys : List KeyCode)
    (q : KeyCode) (hq : q ∈ keys) (pad : Tally) (cap : ℕ) :
    let h := actualPhaseHeader (Dobs w) u l 0 (Clock w)
    localParents (levelConstant S) (phaseLocalOf (levelConstant S) extra u h pad cap keys, q.1) =
      phasePreimages (Dobs w) u l q.1 := by
  intro h
  exact rawPhasePreimages_eq B V a b d bigBias termBias extra u w l 0 q.1 (phaseRoots (levelConstant S) h keys)
    hl (phaseRoots_mem (levelConstant S) h keys q hq)

theorem phaseLocalOf_widths (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top) (keys : List KeyCode)
    (q : KeyCode) (hq : q ∈ keys) (p : PositionCode) (hp : p ∈ phasePreimages (Dobs w) u l q.1)
    (pad : Tally) (cap : ℕ) :
    let h := actualPhaseHeader (Dobs w) u l 0 (Clock w)
    localWidths (phaseLocalOf (levelConstant S) extra u h pad cap keys,p) = readHalfWidths (Dobs w) u l p := by
  intro h
  have he := phaseLocalOf_parents B V a b d bigBias termBias extra u w l hl keys q hq pad cap
  dsimp only at he
  have hm : p ∈ phaseParents (levelConstant S) h (phaseIncidence (levelConstant S) extra u h keys) keys := by
    apply phaseParents_mem (levelConstant S) h _ keys q hq
    change rawPhasePreimages (levelConstant S) (h,phaseIncidence (levelConstant S) extra u h keys,q.1) = _ at he
    rw [he]
    exact hp
  exact phaseWidthRequests_read extra (Dobs w) u l 0 (Clock w) (phaseVisited (levelConstant S) extra u h keys) _ p hm
    (phaseParent_covered B V a b d bigBias termBias extra u w l hl keys q hq p hp)
    (coneClock_slots B V a b d bigBias termBias w l hl.le) (coneClock_field B V a b d bigBias termBias w l hl.le)

set_option maxHeartbeats 1300000 in
theorem phaseLocalOf_allowed (extra : PhaseHeader × ℕ → List FieldKey) (u : List Bool)
    (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top) (keys : List KeyCode)
    (q : KeyCode) (hq : q ∈ keys) (pad : Tally) (cap : ℕ) :
    let h := actualPhaseHeader (Dobs w) u l 0 (Clock w)
    localAllowed (levelConstant S) B.recordLimit (phaseLocalOf (levelConstant S) extra u h pad cap keys,q) =
      phaseAllowed (Dobs w) u B.recordLimit cap l q := by
  intro h
  let ctx := phaseLocalOf (levelConstant S) extra u h pad cap keys
  let ps := phasePreimages (Dobs w) u l q.1
  have hp : localParents (levelConstant S) (ctx,q.1) = ps :=
    phaseLocalOf_parents B V a b d bigBias termBias extra u w l hl keys q hq pad cap
  have hall : ps.all (fun p => widthsWithin cap (localWidths (ctx,p))) =
      ps.all (fun p => widthsWithin cap (readHalfWidths (Dobs w) u l p)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro hgood p hm
    · have he : localWidths (ctx,p) = readHalfWidths (Dobs w) u l p :=
        phaseLocalOf_widths B V a b d bigBias termBias extra u w l hl keys q hq p hm pad cap
      rw [← he]
      exact hgood p hm
    · have he : localWidths (ctx,p) = readHalfWidths (Dobs w) u l p :=
        phaseLocalOf_widths B V a b d bigBias termBias extra u w l hl keys q hq p hm pad cap
      rw [he]
      exact hgood p hm
  change (decide ((localParents (levelConstant S) (ctx,q.1)).length ≤ B.recordLimit) &&
    (localParents (levelConstant S) (ctx,q.1)).all (fun p => widthsWithin cap (localWidths (ctx,p)))) =
    (decide (ps.length ≤ B.recordLimit) && ps.all (fun p => widthsWithin cap (readHalfWidths (Dobs w) u l p)))
  rw [hp, hall]

end Concrete

end P1SolCone.SolCone
