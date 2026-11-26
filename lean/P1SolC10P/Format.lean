import P1SolC10P.Primitives

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.Compression
open P1Wit P1C10 P1ChkFinal P1ChkGreedy P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

abbrev Words := List (List Bool)

/-- Enumeration clock, witness length, level, child address, and the format row. -/
abbrev C10Head := Tally × ℕ × ℕ × ℕ × Words

def formatNat (f : Words) (i : ℕ) : ℕ := P1Batch.bval (readAt [] f i)

@[fun_prop] theorem poly_formatNat {X : Type} [Codec X] {f : X → Words} {i : X → ℕ}
    (hf : Poly f) (hi : Poly i) : Poly (fun x => formatNat (f x) (i x)) :=
  poly_bval (poly_readAt [] hf hi)

def nget (h : C10Head) (i : ℕ) : ℕ := formatNat h.2.2.2.2 i

@[fun_prop] theorem poly_nget {X : Type} [Codec X] {h : X → C10Head} {i : X → ℕ}
    (hh : Poly h) (hi : Poly i) : Poly (fun x => nget (h x) (i x)) := by
  unfold nget
  exact poly_formatNat hh.sndCompose.sndCompose.sndCompose.sndCompose hi

def toTally {T : Type} (w : List T) : Tally := w.map fun _ => ()
@[simp] theorem length_toTally {T : Type} (w : List T) : (toTally w).length = w.length :=
  List.length_map _

@[fun_prop] theorem poly_toTally {X T : Type} [Codec X] [Codec T] {f : X → List T}
    (hf : Poly f) : Poly (fun x => toTally (f x)) :=
  hf.compose (Code.Poly.maps _ (poly_const ()))

def levelPow (dims : ℕ → Dims) (n : List Bool) : ℕ :=
  let row := fmt10 (dims (P1Batch.bval n)) 0
  pow2In (toTally (readAt [] row 0)) (formatNat row 1)

theorem poly_levelPow (dims : ℕ → Dims) (hf : FmtHyp10 dims) : Poly (levelPow dims) := by
  have hr : Poly (fun n : List Bool => fmt10 (dims (P1Batch.bval n)) 0) := by
    have h := (Code.Poly.identity.pair (poly_const ([] : List Bool))).compose hf
    exact h
  unfold levelPow
  exact poly_pow2In (poly_toTally (poly_readAt [] hr (poly_const 0)))
    (poly_formatNat hr (poly_const 1))

theorem bval_bits (n : ℕ) : P1Batch.bval (Nat.bits n) = n := by
  rw [← bin_eq_bits, bval_bin]

theorem levelPow_eq (dims : ℕ → Dims) (n : List Bool) :
    levelPow dims n = 2 ^ levBits (dims (P1Batch.bval n)) := by
  let D := dims (P1Batch.bval n)
  have h0 : readAt [] (fmt10 D 0) 0 = Nat.bits D.top := rfl
  have h1 : readAt [] (fmt10 D 0) 1 = Nat.bits (levBits D) := rfl
  have ht : (Nat.bits D.top).length = levBits D := by
    rw [← bin_eq_bits, ← binary_eq_bin, binary, Bits.short_length]
    rfl
  change 2 ^ min (P1Batch.bval (readAt [] (fmt10 D 0) 1))
    (toTally (readAt [] (fmt10 D 0) 0)).length = 2 ^ levBits D
  rw [h0, h1, bval_bits, length_toTally, ht, min_self]

def makeClock (C k : ℕ) (n : List Bool) : Tally := tally (C * (n.length + 1) ^ k)

theorem poly_makeClock (C k : ℕ) : Poly (makeClock C k) := by
  have h : ∀ j : ℕ, Poly (fun n : List Bool => (n.length + 1) ^ j) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero] using (poly_const (X := List Bool) (1 : ℕ))
    | succ j ih => simpa only [pow_succ] using
        (poly_mulNat ih (poly_addNat (poly_lengthNat Code.Poly.identity) (poly_const 1)))
  apply poly_tally (poly_mulNat (poly_const C) (h k))
  exact ⟨k, C, fun n => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.succ_le_succ (duration n).le) _)⟩

def makeHead (dims : ℕ → Dims) (C k : ℕ) (q : P1ChkFinal.Qry) : C10Head :=
  let pw := levelPow dims q.1
  let i := P1Batch.bval q.2.2
  let l := i % pw
  (makeClock C k q.1, P1Batch.bval q.2.1, l, i / pw,
    fmt10 (dims (P1Batch.bval q.1)) l)

theorem poly_makeHead (dims : ℕ → Dims) (C k : ℕ) (hf : FmtHyp10 dims) :
    Poly (makeHead dims C k) := by
  have n : Poly (fun q : P1ChkFinal.Qry => q.1) := Easy.fst.poly
  have u : Poly (fun q : P1ChkFinal.Qry => q.2.1) := Easy.snd.poly.fstCompose
  have i : Poly (fun q : P1ChkFinal.Qry => P1Batch.bval q.2.2) :=
    poly_bval Easy.snd.poly.sndCompose
  have pw := n.compose (poly_levelPow dims hf)
  have l := poly_modNat i pw
  have lf : Poly (fun q : P1ChkFinal.Qry => fmt10 (dims (P1Batch.bval q.1))
      (P1Batch.bval q.2.2 % levelPow dims q.1)) := by
    simpa only [bval_binary] using (n.pair (poly_binary l)).compose hf
  exact (n.compose (poly_makeClock C k)).pair ((poly_bval u).pair
    (l.pair ((poly_divNat i pw).pair lf)))

def actualHead (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) : C10Head :=
  (t, u.length, l, Y, fmt10 D l)

theorem makeHead_eq (dims : ℕ → Dims) (C k n : ℕ) (u : List Bool) (rho : List Bool) :
    makeHead dims C k (bin n, bin u.length, rho) =
      actualHead (dims n) u (P1Batch.bval rho % 2 ^ levBits (dims n))
        (P1Batch.bval rho / 2 ^ levBits (dims n)) (makeClock C k (bin n)) := by
  simp only [makeHead, levelPow_eq, bval_bin, actualHead]

theorem log_le_bin_length (n : ℕ) : Nat.log 2 (n + 1) ≤ (bin n).length := by
  have h := Bits.value_lt (bin n)
  rw [← bval_eq_value, bval_bin] at h
  exact (Nat.log_mono_right (show n + 1 ≤ 2 ^ (bin n).length by omega)).trans
    (le_of_eq (Nat.log_pow (b := 2) (by decide) _))

theorem size_le_clock (dims : ℕ → Dims) {C k n : ℕ}
    (hb : ∀ n, c10Size (dims n) ≤ C * (Nat.log 2 (n + 1) + 1) ^ k) :
    c10Size (dims n) ≤ (makeClock C k (bin n)).length := by
  rw [makeClock, tally_length]
  exact (hb n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.succ_le_succ (log_le_bin_length n)) _))

def enabled (h : C10Head) : Bool := decide (h.2.2.1 < nget h 0) &&
  decide (h.2.2.2.1 < nget h 10)

def shrinking (h : C10Head) : Bool := decide (nget h 7 = 1)
def oldBits (h : C10Head) : ℕ := Nat.log 2 (nget h 4)
def childBits (h : C10Head) : ℕ := Nat.log 2 (nget h 11)
def resBits (h : C10Head) : ℕ := nget h 13
def oldSlots (h : C10Head) : ℕ := pow2In h.1 (oldBits h)
def childSlots (h : C10Head) : ℕ := pow2In h.1 (childBits h)
def resLanes (h : C10Head) : ℕ := pow2In h.1 (resBits h)
def tagBits (h : C10Head) : ℕ := packingTagBits (oldSlots h)
def tagLanes (h : C10Head) : ℕ := pow2In h.1 (tagBits h)
def oldLanes (h : C10Head) : ℕ :=
  pow2In h.1 (if shrinking h then (2 * oldSlots h + 1) + (oldBits h + (tagBits h + resBits h))
    else oldBits h + resBits h)
def childFactor (h : C10Head) : ℕ := if shrinking h then tagLanes h else oldSlots h
def parent (h : C10Head) : ℕ := h.2.2.2.1 / childFactor h
def childIndex (h : C10Head) : ℕ := h.2.2.2.1 % childFactor h

@[fun_prop] theorem poly_enabled : Poly enabled := by unfold enabled; fun_prop
@[fun_prop] theorem poly_shrinking : Poly shrinking := by unfold shrinking; fun_prop
@[fun_prop] theorem poly_oldBits : Poly oldBits := by unfold oldBits; fun_prop
@[fun_prop] theorem poly_childBits : Poly childBits := by unfold childBits; fun_prop
@[fun_prop] theorem poly_resBits : Poly resBits := by unfold resBits; fun_prop
@[fun_prop] theorem poly_oldSlots : Poly oldSlots := by unfold oldSlots; fun_prop
@[fun_prop] theorem poly_childSlots : Poly childSlots := by unfold childSlots; fun_prop
@[fun_prop] theorem poly_resLanes : Poly resLanes := by unfold resLanes; fun_prop
@[fun_prop] theorem poly_tagBits : Poly tagBits := by
  unfold tagBits packingTagBits
  simp only [pow_two]
  fun_prop
@[fun_prop] theorem poly_tagLanes : Poly tagLanes := by unfold tagLanes; fun_prop
@[fun_prop] theorem poly_oldLanes : Poly oldLanes := by unfold oldLanes; fun_prop
@[fun_prop] theorem poly_childFactor : Poly childFactor := by unfold childFactor; fun_prop
@[fun_prop] theorem poly_parent : Poly parent := by unfold parent; fun_prop
@[fun_prop] theorem poly_childIndex : Poly childIndex := by unfold childIndex; fun_prop

theorem enabled_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    enabled (actualHead D u l Y t) = (decide (l < D.top) && decide (Y < (D.lv (l + 1)).bases)) := by
  have a : readAt [] (fmt10 D l) 0 = Nat.bits D.top := rfl
  have b : readAt [] (fmt10 D l) 10 = Nat.bits (D.lv (l + 1)).bases := rfl
  simp only [enabled, nget, actualHead, formatNat, a, b, bval_bits]

theorem shrinking_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    shrinking (actualHead D u l Y t) = (D.lv l).shrink := by
  have a : readAt [] (fmt10 D l) 7 = Nat.bits (if (D.lv l).shrink then 1 else 0) := rfl
  simp only [shrinking, nget, actualHead, formatNat, a, bval_bits]
  cases (D.lv l).shrink <;> rfl

@[simp] theorem oldBits_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    oldBits (actualHead D u l Y t) = slotBits D l := by
  have a : readAt [] (fmt10 D l) 4 = Nat.bits (D.lv l).slots := rfl
  simp only [oldBits, nget, actualHead, formatNat, a, bval_bits, slotBits]

@[simp] theorem childBits_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    childBits (actualHead D u l Y t) = slotBits D (l + 1) := by
  have a : readAt [] (fmt10 D l) 11 = Nat.bits (D.lv (l + 1)).slots := rfl
  simp only [childBits, nget, actualHead, formatNat, a, bval_bits, slotBits]

@[simp] theorem resBits_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) :
    resBits (actualHead D u l Y t) = (D.lv (l + 1)).laneW := by
  have a : readAt [] (fmt10 D l) 13 = Nat.bits (D.lv (l + 1)).laneW := rfl
  simp only [resBits, nget, actualHead, formatNat, a, bval_bits]

theorem foldr_max_ge {v : ℕ} {xs : List ℕ} (h : v ∈ xs) : v ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem activeSize_le (D : Dims) {l : ℕ} (hl : l < D.top) :
    lanesUsed D l + fieldW D l + fieldW D (l + 1) ≤ c10Size D := by
  unfold c10Size
  have hm : lanesUsed D l + fieldW D l + fieldW D (l + 1) ∈
      (List.range D.top).map (fun l => lanesUsed D l + fieldW D l + fieldW D (l + 1)) :=
    List.mem_map_of_mem (f := fun l => lanesUsed D l + fieldW D l + fieldW D (l + 1))
      (List.mem_range.mpr hl)
  exact (foldr_max_ge hm).trans (Nat.le_add_left _ _)

theorem width_le_fieldW (D : Dims) (l : ℕ) (k : Mem) :
    D.width (secLev l k) ≤ fieldW D l := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  apply List.mem_map_of_mem
  cases k <;> simp [memAll]

theorem pow_cap {e : ℕ} {t : Tally} (he : 2 ^ e ≤ t.length) :
    pow2In t e = 2 ^ e := by
  unfold pow2In
  have h : e ≤ 2 ^ e := Nat.le_of_lt (Nat.lt_two_pow_self)
  rw [min_eq_left (h.trans he)]

theorem range_cap {n : ℕ} {t : Tally} (h : n ≤ t.length) : rangeIn t n = List.range n := by
  simp only [rangeIn, min_eq_left h]

structure Fits (D : Dims) (l : ℕ) (t : Tally) : Prop where
  slotsOld : 2 ^ slotBits D l ≤ t.length
  slotsChild : 2 ^ slotBits D (l + 1) ≤ t.length
  lanesRes : 2 ^ (D.lv (l + 1)).laneW ≤ t.length
  lanesShrink : 2 ^ packingLaneBits (slotBits D l) (D.lv (l + 1)).laneW ≤ t.length
  lanesRefresh : 2 ^ (slotBits D l + (D.lv (l + 1)).laneW) ≤ t.length
  tags : 2 ^ packingTagBits (2 ^ slotBits D l) ≤ t.length
  width : ∀ (next : Bool) (k : Mem), D.width (secLev (if next then l + 1 else l) k) ≤ t.length

theorem fits_of_size (D : Dims) {l : ℕ} (hl : l < D.top) {t : Tally} (ht : c10Size D ≤ t.length) :
    Fits D l t := by
  have h := (activeSize_le D hl).trans ht
  unfold lanesUsed at h
  have pieces {a b c d e f B : ℕ} (le : a + b + c + d + e + f ≤ B) :
      a ≤ B ∧ b ≤ B ∧ c ≤ B ∧ d ≤ B ∧ e ≤ B ∧ f ≤ B := by omega
  obtain ⟨shr, ref, res, child, wold, wnew⟩ := pieces h
  refine ⟨?_, child, res, shr, ref, ?_, ?_⟩
  · exact (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)).trans ref
  · apply le_trans _ shr
    apply Nat.pow_le_pow_right (by decide)
    unfold packingLaneBits
    omega
  · intro next k
    cases next
    · exact (width_le_fieldW D l k).trans wold
    · exact (width_le_fieldW D (l + 1) k).trans wnew

theorem oldSlots_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    oldSlots (actualHead D u l Y t) = 2 ^ slotBits D l := by
  rw [oldSlots, oldBits_actual]
  exact pow_cap h.slotsOld

theorem childSlots_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    childSlots (actualHead D u l Y t) = 2 ^ slotBits D (l + 1) := by
  rw [childSlots, childBits_actual]
  exact pow_cap h.slotsChild

theorem resLanes_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    resLanes (actualHead D u l Y t) = 2 ^ (D.lv (l + 1)).laneW := by
  rw [resLanes, resBits_actual]
  exact pow_cap h.lanesRes

theorem tagLanes_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    tagLanes (actualHead D u l Y t) = shrinkJ (slotBits D l) := by
  rw [tagLanes, tagBits, oldSlots_actual h]
  exact pow_cap h.tags

theorem oldLanes_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    oldLanes (actualHead D u l Y t) =
      if (D.lv l).shrink then 2 ^ packingLaneBits (slotBits D l) (D.lv (l + 1)).laneW
      else 2 ^ (slotBits D l + (D.lv (l + 1)).laneW) := by
  simp only [oldLanes, tagBits, shrinking_actual, oldSlots_actual h, oldBits_actual, resBits_actual]
  split
  · exact pow_cap h.lanesShrink
  · exact pow_cap h.lanesRefresh

theorem childFactor_actual {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ) :
    childFactor (actualHead D u l Y t) =
      if (D.lv l).shrink then shrinkJ (slotBits D l) else 2 ^ slotBits D l := by
  simp only [childFactor, shrinking_actual, tagLanes_actual h, oldSlots_actual h]

def oldValid (h : C10Head) (y : ℕ) : Bool := decide (y < nget h 3)

@[fun_prop] theorem poly_oldValid {X : Type} [Codec X] {h : X → C10Head} {y : X → ℕ}
    (hh : Poly h) (hy : Poly y) : Poly (fun x => oldValid (h x) (y x)) := by
  unfold oldValid
  fun_prop

theorem oldValid_actual (D : Dims) (u : List Bool) (l Y : ℕ) (t : Tally) (y : ℕ) :
    oldValid (actualHead D u l Y t) y = decide (y < (D.lv l).bases) := by
  have a : readAt [] (fmt10 D l) 3 = Nat.bits (D.lv l).bases := rfl
  simp only [oldValid, nget, actualHead, formatNat, a, bval_bits]

def memIndex : Mem → ℕ
  | .layout => 0
  | .outAddr => 1
  | .outDisp => 2
  | .outFar => 3
  | .inAddr => 4
  | .inDisp => 5
  | .inFar => 6
  | .width => 7
  | .colour => 8
  | .offset => 9
  | .energy => 10
  | .terms => 11

def fieldPos (next : Bool) (m : Mem) : ℕ := (if next then 38 else 14) + 2 * memIndex m

abbrev FieldKey := ℕ × ℕ

def fieldKey (next : Bool) (m : Mem) (h : C10Head) (i : ℕ) : FieldKey :=
  let f := fieldPos next m
  let w := nget h (f + 1)
  (min h.2.1 (nget h f + i * w), min h.1.length w)

@[fun_prop] theorem poly_fieldKey (next : Bool) (m : Mem) {X : Type} [Codec X]
    {h : X → C10Head} {i : X → ℕ} (hh : Poly h) (hi : Poly i) :
    Poly (fun x => fieldKey next m (h x) (i x)) := by
  unfold fieldKey
  fun_prop

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000 in
theorem fieldPos_actual (D : Dims) (l : ℕ) (next : Bool) (m : Mem) :
    (readAt [] (fmt10 D l) (fieldPos next m),
      readAt [] (fmt10 D l) (fieldPos next m + 1)) =
    (Nat.bits (D.off (secLev (if next then l + 1 else l) m)),
      Nat.bits (D.width (secLev (if next then l + 1 else l) m))) := by
  cases next <;> cases m <;> rfl

def fieldAt (u : List Bool) (q : FieldKey) : ℕ := P1Batch.bval ((u.drop q.1).take q.2)

theorem fieldAt_fieldKey {D : Dims} {l : ℕ} {t : Tally} (h : Fits D l t) (u : List Bool) (Y : ℕ)
    (next : Bool) (m : Mem) (i : ℕ) :
    fieldAt u (fieldKey next m (actualHead D u l Y t) i) =
      readField D u (secLev (if next then l + 1 else l) m) i := by
  have ho := congrArg Prod.fst (fieldPos_actual D l next m)
  have hw := congrArg Prod.snd (fieldPos_actual D l next m)
  dsimp only at ho hw
  simp only [fieldAt, fieldKey, actualHead, nget, formatNat, ho, hw, bval_bits,
    min_eq_right (h.width next m), readField, readNat, bitsVal_eq_bval]
  generalize D.off (secLev (if next then l + 1 else l) m) +
    i * D.width (secLev (if next then l + 1 else l) m) = n
  by_cases hn : n ≤ u.length
  · rw [min_eq_right hn]
  · rw [min_eq_left (Nat.le_of_not_le hn), List.drop_length,
      List.drop_eq_nil_of_le (Nat.le_of_not_le hn)]

end P1SolC10P.SolC10prog
