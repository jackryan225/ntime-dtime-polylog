import P1SolCone.ConeStateSize
import P1SolCone.PhaseMatch

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10
open private slotCap from P1Wit.SpaceFacts

theorem phaseAllowed_limits (D : Dims) (u : List Bool) (parent width l : ℕ) (q : KeyCode)
    (h : phaseAllowed D u parent width l q = true) :
    (phasePreimages D u l q.1).length ≤ parent ∧
      ∀ v ∈ phasePreimages D u l q.1, widthsWithin width (readHalfWidths D u l v) = true := by
  simpa only [phaseAllowed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using h

theorem widthsWithin_fields (width : ℕ) (ws : List ℕ × List ℕ) (h : widthsWithin width ws = true) :
    (∀ w ∈ ws.1, w ≤ width) ∧ (∀ w ∈ ws.2, w ≤ width) := by
  simpa only [widthsWithin, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem readHalfWidths_lengths (D : Dims) (u : List Bool) (l : ℕ) (x : PositionCode) :
    (readHalfWidths D u l x).1.length = (D.lv l).slots ∧
      (readHalfWidths D u l x).2.length = (D.lv l).slots := by
  simp only [readHalfWidths, List.length_map, List.length_range, and_self]

theorem halfCode_limits (ws : List ℕ × List ℕ) (w : ℕ) (hw : widthsWithin w ws = true)
    (z : HalfCode) (hz : z ∈ halfCodes ws) :
    z.1.length = ws.1.length ∧ z.2.length = ws.2.length ∧ ∀ bitword ∈ z.1 ++ z.2, bitword.length ≤ w := by
  obtain ⟨ho,hi⟩ := (mem_halfCodes ws z).mp hz
  obtain ⟨bo,bi⟩ := widthsWithin_fields w ws hw
  constructor
  · simpa only [List.length_map] using congrArg List.length ho
  constructor
  · simpa only [List.length_map] using congrArg List.length hi
  intro word hword
  rcases List.mem_append.mp hword with h | h
  · exact bo _ (ho ▸ List.mem_map_of_mem h)
  · exact bi _ (hi ▸ List.mem_map_of_mem h)

def keyFits (addr lanes slots width : ℕ) (q : KeyCode) : Prop :=
  q.1.1 < 2 ^ addr ∧ q.1.2 < lanes ∧ q.2.1.length ≤ slots ∧ q.2.2.length ≤ slots ∧
    ∀ word ∈ q.2.1 ++ q.2.2, word.length ≤ width

theorem keyFits_size (addr lanes slots width bits : ℕ) (q : KeyCode)
    (ha : addr ≤ bits) (hl : lanes ≤ 2 ^ bits) (hq : keyFits addr lanes slots width q) :
    size q ≤ 4 * bits + 2 * slots * (2*width+2) + 7 :=
  keyCode_size q slots width bits (hq.1.trans_le (Nat.pow_le_pow_right (by decide) ha))
    (hq.2.1.trans_le hl) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2

theorem preimages_addresses (D : Dims) (u : List Bool) (l a g : ℕ) (q p : PositionCode)
    (addr : ℕ) (hAddr : q.1 < 2 ^ addr)
    (hOut : ∀ y j, rdOutAddr D u l y j < 2 ^ addr) (hIn : ∀ y j, rdInAddr D u l y j < 2 ^ addr)
    (hu : p ∈ shrinkPreimages D u l a g q) :
    p.1 < 2 ^ addr ∧ p.2 < 2 ^ packingLaneBits a g := by
  have hp := List.mem_dedup.mp (List.mem_filter.mp hu).1
  obtain ⟨y,hy, hr⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  refine ⟨?_,List.mem_range.mp hi⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact (Nat.div_le_self _ _).trans_lt hAddr
  · rcases List.mem_append.mp hy with h | h
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      exact hOut _ _
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      exact hIn _ _

section Concrete
variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w

theorem phasePreimages_address_bounds (u : List Bool) (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top)
    (addr lanes : ℕ) (haddr : (Dobs w).bigW ≤ addr) (q p : PositionCode)
    (hq : q.1 < 2 ^ addr ∧ q.2 < lanes) (hp : p ∈ phasePreimages (Dobs w) u l q) :
    p.1 < 2 ^ addr ∧ p.2 < lanes + (Clock w).length := by
  let D := Dobs w
  let c := Clock w
  let α := (D.lv l).slotW
  let γ := (D.lv (l+1)).laneW
  have geom := conePhaseShape_eq B V a b d bigBias termBias (P1Batch.bval w) l hl
  have kind := conePhaseShape_kind B V a b d bigBias termBias (P1Batch.bval w) l hl
  have cap : 2 ^ packingLaneBits α γ ≤ c.length :=
    coneReadClock_shrinkLanes B V a b d bigBias termBias w l hl
  have hOut (y j : ℕ) : rdOutAddr D u l y j < 2 ^ addr := by
    unfold rdOutAddr readField
    have h : D.width (secLev l .outAddr) = D.bigW := by rw [D.width_secLev _ hl.le]; rfl
    rw [h]
    exact (readNat_lt _ _ _).trans_le (Nat.pow_le_pow_right (by decide) haddr)
  have hIn (y j : ℕ) : rdInAddr D u l y j < 2 ^ addr := by
    unfold rdInAddr readField
    have h : D.width (secLev l .inAddr) = D.bigW := by rw [D.width_secLev _ hl.le]; rfl
    rw [h]
    exact (readNat_lt _ _ _).trans_le (Nat.pow_le_pow_right (by decide) haddr)
  unfold phasePreimages at hp
  dsimp only at hp
  rw [kind, show (phaseShape D l).inDegree = α from congrArg PhaseShape.inDegree geom,
    show (phaseShape D l).outLanes = γ from congrArg PhaseShape.outLanes geom] at hp
  change p ∈ (bif (D.lv l).shrink then shrinkPreimages D u l α γ q else [refreshPreimage α γ q]) at hp
  cases hb : (D.lv l).shrink
  · simp only [hb,Bool.cond_false,List.mem_singleton] at hp
    subst p
    refine ⟨(Nat.div_le_self _ _).trans_lt hq.1, ?_⟩
    have m := Nat.mod_lt q.1 (Nat.two_pow_pos α)
    have hbound : 2 ^ α * 2 ^ γ ≤ c.length := by
      rw [← pow_add]
      apply le_trans _ cap
      apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      unfold packingLaneBits
      omega
    have hmod := Nat.mul_lt_mul_of_pos_right m (Nat.two_pow_pos γ)
    change q.1 % 2 ^ α * 2 ^ γ + q.2 < lanes + c.length
    omega
  · simp only [hb,Bool.cond_true] at hp
    obtain ⟨h₁,h₂⟩ := preimages_addresses D u l α γ q p addr hq.1 hOut hIn hp
    exact ⟨h₁,h₂.trans_le (cap.trans (Nat.le_add_left _ _))⟩

end Concrete

end P1SolCone.SolCone
