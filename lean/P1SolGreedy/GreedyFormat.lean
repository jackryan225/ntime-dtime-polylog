import P1SolGreedy.BinaryGreedy
import P1ChkGreedy.Local
import P1ChkFinal.Progs
import OAI.Computability.IntegerMultiplication.Carry.Remainder
import OAI.Computability.IntegerMultiplication.Carry.Shrink

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

/-- A row contains only public dimensions, unary loop limits, and section offsets and widths. -/
abbrev BaseRow := Bool × NumberWord × NumberWord × Tally × Tally × List (P1Batch.Req × Tally)

abbrev PublicFmt := NumberWord × NumberWord × List (NumberWord × BaseRow)

def levelRow (D : Dims) (ℓ : ℕ) : BaseRow :=
  let L := D.lv ℓ
  (L.shrink, bin L.bases, bin L.slots, tally L.slots, tally (2 * L.slots + 1),
    (List.range 12).map fun j =>
      let s := secLev ℓ (Mem.ofCode j)
      ((bin (D.off s), bin (D.width s)), tally (D.width s)))

def defaultRow : BaseRow := (false, [], [], [], [], [])

/-- Public witness format for checks indexed by level and base. -/
def fmtGreedy (D : Dims) (M : ℕ) : PublicFmt :=
  (bin (2 ^ levBits D), bin M, (List.range (D.top + 1)).map fun ℓ => (bin ℓ, levelRow D ℓ))

def FmtHypGreedy (dims : ℕ → Dims) (M : ℕ → ℕ) : Prop :=
  Poly (fun n : NumberWord => fmtGreedy (dims (P1Batch.bval n)) (M (P1Batch.bval n)))

abbrev IndexWord := NumberWord × NumberWord

def formatIndex (dims : ℕ → Dims) (M : ℕ → ℕ) (z : IndexWord) : PublicFmt × NumberWord :=
  (fmtGreedy (dims (P1Batch.bval z.1)) (M (P1Batch.bval z.1)), z.2)

theorem formatIndex_poly (dims : ℕ → Dims) (M : ℕ → ℕ) (hf : FmtHypGreedy dims M) :
    Poly (formatIndex dims M) := Poly.onleft hf

@[fun_prop] theorem pickPoly {T : Type} [Codec T] (d : T) : Poly (Code.Iter.pick d) :=
  (Code.Iter.facile d).poly

def rowSection (c : Mem) (r : BaseRow) : P1Batch.Req :=
  (Code.Iter.pick (([], []), []) (r.2.2.2.2.2, tally c.toNat)).1

@[fun_prop] theorem rowSection_poly (c : Mem) : Poly (rowSection c) := by
  unfold rowSection
  fun_prop

theorem width_le_size_levelRow (D : Dims) (ℓ : ℕ) (c : Mem) :
    D.width (secLev ℓ c) ≤ size (levelRow D ℓ) := by
  let q := fun j => ((bin (D.off (secLev ℓ (Mem.ofCode j))), bin (D.width (secLev ℓ (Mem.ofCode j)))),
    tally (D.width (secLev ℓ (Mem.ofCode j))))
  have hm : q c.toNat ∈ (List.range 12).map q :=
    List.mem_map_of_mem (List.mem_range.mpr c.toNat_lt)
  have hs := size_bel hm
  simp only [q, Mem.ofCode_toNat, size_prod, size_tally, tally_length] at hs
  simp only [levelRow, size_prod]
  change D.width (secLev ℓ c) ≤
    size (D.lv ℓ).shrink + (size (bin (D.lv ℓ).bases) + (size (bin (D.lv ℓ).slots) +
      (size (tally (D.lv ℓ).slots) + (size (tally (2 * (D.lv ℓ).slots + 1)) +
        size ((List.range 12).map q) + 1) + 1) + 1) + 1) + 1
  dsimp only [q]
  omega

theorem rowSection_levelRow (D : Dims) (ℓ : ℕ) (c : Mem) :
    rowSection c (levelRow D ℓ) =
      (bin (D.off (secLev ℓ c)), bin (D.width (secLev ℓ c))) := by
  cases c <;> rfl

/-- Select rows by equality of binary level numbers, including noncanonical input words. -/
def matchRow {R : Type} (p : NumberWord × (NumberWord × R)) : List R :=
  bif numberEq (p.1, p.2.1) then [p.2.2] else []

@[fun_prop] theorem matchRow_poly {R : Type} [Codec R] : Poly (matchRow (R := R)) := by
  unfold matchRow
  fun_prop

def matchingRows {R : Type} (p : NumberWord × List (NumberWord × R)) : List R :=
  (Code.polyPush matchRow p).flatten

theorem matchingRows_poly {R : Type} [Codec R] (default : R) :
    Poly (matchingRows (R := R)) :=
  (Poly.push ([] : NumberWord) (([] : NumberWord), default) matchRow_poly).compose Easy.flatten.poly

theorem mem_matchingRows {R : Type} (i : NumberWord) (rows : List (NumberWord × R)) (r : R) :
    r ∈ matchingRows (i, rows) ↔ ∃ j, (j, r) ∈ rows ∧ P1Batch.bval i = P1Batch.bval j := by
  simp only [matchingRows, Code.polyPush, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨s, ⟨⟨j, t⟩, hj, rfl⟩, hr⟩
    unfold matchRow at hr
    dsimp only at hr
    cases e : numberEq (i, j)
    · simp only [e, Bool.cond_false, List.not_mem_nil] at hr
    · simp only [e, Bool.cond_true, List.mem_singleton] at hr
      subst t
      exact ⟨j, hj, (numberEq_spec (i, j)).mp e⟩
  · rintro ⟨j, hj, he⟩
    refine ⟨matchRow (i, j, r), ⟨(j, r), hj, rfl⟩, ?_⟩
    have h := (numberEq_spec (i, j)).mpr he
    simp only [matchRow, h, Bool.cond_true, List.mem_singleton]

def selectRow {R : Type} (default : R) (p : NumberWord × List (NumberWord × R)) : R :=
  (matchingRows p).headD default

theorem selectRow_poly {R : Type} [Codec R] (default : R) : Poly (selectRow default) :=
  (matchingRows_poly default).compose (Code.Iter.leader default).poly

theorem selectRow_table {R : Type} (default : R) (count : ℕ) (row : ℕ → R) (i : NumberWord) :
    selectRow default (i, (List.range count).map (fun j => (bin j, row j))) =
      if P1Batch.bval i < count then row (P1Batch.bval i) else default := by
  let rs := (List.range count).map (fun j => (bin j, row j))
  have hmem (r : R) : r ∈ matchingRows (i, rs) ↔
      P1Batch.bval i < count ∧ r = row (P1Batch.bval i) := by
    rw [mem_matchingRows]
    constructor
    · rintro ⟨j, hj, he⟩
      obtain ⟨k, hk, hkr⟩ := List.mem_map.mp hj
      have hj' := congrArg Prod.fst hkr
      have hr' := congrArg Prod.snd hkr
      change bin k = j at hj'
      change row k = r at hr'
      rw [← hj', bval_bin] at he
      subst k
      exact ⟨List.mem_range.mp hk, hr'.symm⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨bin (P1Batch.bval i), List.mem_map.mpr ⟨_, List.mem_range.mpr hi, rfl⟩, by rw [bval_bin]⟩
  change (matchingRows (i, rs)).headD default = _
  cases hs : matchingRows (i, rs) with
  | nil =>
    have hnot : ¬ P1Batch.bval i < count := fun h => by
      have hh := (hmem (row (P1Batch.bval i))).mpr ⟨h, rfl⟩
      rw [hs] at hh
      exact List.not_mem_nil hh
    rw [ite_eq_right hnot]
    rfl
  | cons r rs' =>
    have hm : r ∈ matchingRows (i, rs) := by rw [hs]; exact List.mem_cons_self
    obtain ⟨h, hr⟩ := (hmem r).mp hm
    rw [ite_eq_left h, ← hr]
    rfl

theorem selectRow_level (D : Dims) (M : ℕ) (i : NumberWord) :
    selectRow defaultRow (i, (fmtGreedy D M).2.2) =
      if P1Batch.bval i ≤ D.top then levelRow D (P1Batch.bval i) else defaultRow := by
  unfold fmtGreedy
  rw [selectRow_table]
  simp only [Nat.lt_succ_iff]

/-- Boolean guard, base address word, and public level row for a base-indexed check. -/
abbrev BaseQuery := Bool × NumberWord × BaseRow

def setupBase (p : PublicFmt × NumberWord) : BaseQuery :=
  let parts := Carry.nat_div (p.2, p.1.1)
  let r := selectRow defaultRow (parts.2, p.1.2.2)
  (bif r.1 then Carry.lt_ (parts.1, r.2.1) else false, parts.1, r)

theorem setupBase_poly : Poly setupBase := by
  have hsel : Poly (selectRow defaultRow) := selectRow_poly _
  unfold setupBase
  dsimp only
  fun_prop

theorem bval_divide (x y : NumberWord) :
    P1Batch.bval (Carry.nat_div (x, y)).1 = P1Batch.bval x / P1Batch.bval y ∧
      P1Batch.bval (Carry.nat_div (x, y)).2 = P1Batch.bval x % P1Batch.bval y := by
  rw [← value_bval x, ← value_bval y, ← value_bval, ← value_bval]
  exact Carry.division_rules x y

theorem setupBase_spec (D : Dims) (M : ℕ) (i : NumberWord) :
    let p := setupBase (fmtGreedy D M, i)
    let ℓ := P1Batch.bval i % 2 ^ levBits D
    (p.1 = true ↔ ShrinkIdx D (P1Batch.bval i)) ∧
      P1Batch.bval p.2.1 = P1Batch.bval i / 2 ^ levBits D ∧
      p.2.2 = if ℓ ≤ D.top then levelRow D ℓ else defaultRow := by
  have hd := bval_divide i ((fmtGreedy D M).1)
  change P1Batch.bval (Carry.nat_div (i, bin (2 ^ levBits D))).1 = _ ∧
    P1Batch.bval (Carry.nat_div (i, bin (2 ^ levBits D))).2 = _ at hd
  rw [show (fmtGreedy D M).1 = bin (2 ^ levBits D) from rfl, bval_bin] at hd
  unfold setupBase
  dsimp only
  rw [selectRow_level, show (fmtGreedy D M).1 = bin (2 ^ levBits D) from rfl, hd.2]
  refine ⟨?_, hd.1, rfl⟩
  unfold ShrinkIdx
  split_ifs with h
  · simp only [levelRow, less_spec, hd.1, bval_bin, h, true_and]
    cases (D.lv (P1Batch.bval i % 2 ^ levBits D)).shrink <;> simp
  · simp [defaultRow, h]

/-- Enumerate a format-sized range as binary numbers. -/
def wordRange (t : Tally) : List NumberWord :=
  (Code.Iter.lineup t).map (fun s => Carry.born s.length)

@[fun_prop] theorem wordRange_poly : Poly wordRange :=
  Code.Iter.poly_line.compose (Poly.maps _ Carry.easy_chart.poly)

theorem wordRange_tally (n : ℕ) :
    wordRange (tally n) = (List.range n).map Carry.born := by
  simp only [wordRange, Code.Iter.lined, List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_range]
  · intro j hj hk
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_def, tally_length]

theorem bval_born (n : ℕ) : P1Batch.bval (Carry.born n) = n := by
  rw [← value_bval, Carry.birthValue]

end P1SolGreedy.SolDemand
