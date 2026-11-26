import P1SolGreedy.GreedyFamilies
import P1SolGreedy.WireNumbers

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev MotifShiftTable := List (NumberWord × NumberWord)
abbrev MotifStride := NumberWord × NumberWord × NumberWord
abbrev MotifRow := WireRadices × NumberWord × Tally × Tally × Tally × NumberWord × MotifShiftTable × MotifStride
abbrev MotifFormat := PublicFmt × List (NumberWord × MotifRow)
abbrev MotifContext := C5Context × MotifRow × NumberWord

def colourShiftTable (c : ℕ) : MotifShiftTable :=
  (List.range c).map fun j => (bin j, bin (2 ^ (c - 1 - j)))

/-- The single-term check needs only its selected wire, whereas the energy check scans all root wires. -/
def motifRow (all : Bool) (D : Dims) (ℓ a g : ℕ) : MotifRow :=
  let c := 2 * 2 ^ a + 1
  (wireRadices a g, bin c, tally (2 ^ a), tally (2 ^ c),
    if all then tally (2 ^ packingLaneBits a g) else [],
    bin (PackingData.pieceCount (2 ^ a) c), colourShiftTable c,
    (bin (D.lv ℓ).lanes, bin (D.lv ℓ).termKeys, bin ((D.lv ℓ).termArity + 1)))

def emptyMotifRow : MotifRow :=
  (([], [], [], [], []), [], [], [], [], [], [], ([], [], []))

def motifFormat (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) : MotifFormat :=
  (fmtGreedy D M, (List.range (D.top + 1)).map fun ℓ => (bin ℓ, motifRow all D ℓ (ag ℓ).1 (ag ℓ).2))

def FmtHypMotif (all : Bool) (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ) : Prop :=
  Poly (fun n : NumberWord =>
    motifFormat all (dims (P1Batch.bval n)) (M (P1Batch.bval n)) (ag (P1Batch.bval n)))

/-- Split a C7 index into level, base and key or a C8 index into level and base. -/
def setupMotif (all : Bool) (p : MotifFormat × NumberWord) : MotifContext :=
  let j := Carry.nat_div (p.2, p.1.1.1)
  let row := selectRow defaultRow (j.2, p.1.1.2.2)
  let m := selectRow emptyMotifRow (j.2, p.1.2)
  let keys := Carry.times0 (m.1.2.2.2.2, m.1.1)
  let s := bif all then (j.1, []) else Carry.nat_div (j.1, keys)
  ((p.1.1.2.1, bif row.1 then Carry.lt_ (s.1, row.2.1) else false, s.1, row), m, s.2)

theorem setupMotif_poly (all : Bool) : Poly (setupMotif all) := by
  have h₁ := selectRow_poly defaultRow
  have h₂ := selectRow_poly emptyMotifRow
  cases all <;> unfold setupMotif <;> dsimp only <;> fun_prop

def setupC78 (all : Bool) (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ) (z : IndexWord) :
    MotifContext :=
  setupMotif all
    (motifFormat all (dims (P1Batch.bval z.1)) (M (P1Batch.bval z.1)) (ag (P1Batch.bval z.1)), z.2)

theorem setupC78_poly (all : Bool) (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ)
    (hf : FmtHypMotif all dims M ag) : Poly (setupC78 all dims M ag) :=
  (Poly.onleft hf).compose (setupMotif_poly all)

theorem setupMotif_length (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    P1Batch.bval (setupMotif all (motifFormat all D M ag, i)).1.1 = M := bval_bin _

def activeMotif (all : Bool) (D : Dims) (ℓ a g : ℕ) (len Y key : NumberWord) : MotifContext :=
  ((len, true, Y, levelRow D ℓ), motifRow all D ℓ a g, key)

theorem selectRow_motif (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    selectRow emptyMotifRow (i, (motifFormat all D M ag).2) =
      if P1Batch.bval i ≤ D.top then motifRow all D (P1Batch.bval i) (ag (P1Batch.bval i)).1 (ag (P1Batch.bval i)).2
      else emptyMotifRow := by
  unfold motifFormat
  rw [selectRow_table]
  simp only [Nat.lt_succ_iff]

set_option maxHeartbeats 600000 in
theorem setupMotif_spec (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    let p := setupMotif all (motifFormat all D M ag, i)
    let ℓ := P1Batch.bval i % 2 ^ levBits D
    let j := P1Batch.bval i / 2 ^ levBits D
    (p.1.2.1 = true ↔ ShrinkIdx (if all then D else termDims D ag) (P1Batch.bval i)) ∧
    (ℓ ≤ D.top →
      p.1.2.2.2 = levelRow D ℓ ∧ p.2.1 = motifRow all D ℓ (ag ℓ).1 (ag ℓ).2 ∧
      P1Batch.bval p.1.2.2.1 = (if all then j else j / termStride ag ℓ) ∧
      P1Batch.bval p.2.2 = (if all then 0 else j % termStride ag ℓ)) := by
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let j := P1Batch.bval i / 2 ^ levBits D
  let word₀ := (Carry.nat_div (i, bin (2 ^ levBits D))).1
  let word₁ := (Carry.nat_div (i, bin (2 ^ levBits D))).2
  let r := selectRow defaultRow (word₁, (fmtGreedy D M).2.2)
  let m := selectRow emptyMotifRow (word₁, (motifFormat all D M ag).2)
  let keys := Carry.times0 (m.1.2.2.2.2, m.1.1)
  let s := bif all then (word₀, []) else Carry.nat_div (word₀, keys)
  have hj : P1Batch.bval word₀ = j := by simp only [word₀, j, (bval_divide _ _).1, bval_bin]
  have hl : P1Batch.bval word₁ = ℓ := by simp only [word₁, ℓ, (bval_divide _ _).2, bval_bin]
  have hr : r = if ℓ ≤ D.top then levelRow D ℓ else defaultRow := by
    unfold r
    rw [selectRow_level, hl]
  have hm : m = if ℓ ≤ D.top then motifRow all D ℓ (ag ℓ).1 (ag ℓ).2 else emptyMotifRow := by
    unfold m
    rw [selectRow_motif, hl]
  change ((bif r.1 then Carry.lt_ (s.1, r.2.1) else false) = true ↔
    ShrinkIdx (if all then D else termDims D ag) (P1Batch.bval i)) ∧
    (ℓ ≤ D.top → r = levelRow D ℓ ∧ m = motifRow all D ℓ (ag ℓ).1 (ag ℓ).2 ∧
      P1Batch.bval s.1 = (if all then j else j / termStride ag ℓ) ∧
      P1Batch.bval s.2 = (if all then 0 else j % termStride ag ℓ))
  by_cases h : ℓ ≤ D.top
  · have hR : r = levelRow D ℓ := hr.trans (ite_eq_left h)
    have hM : m = motifRow all D ℓ (ag ℓ).1 (ag ℓ).2 := hm.trans (ite_eq_left h)
    have hd : P1Batch.bval keys = termStride ag ℓ := by
      unfold keys
      rw [bval_mul, hM]
      simp only [motifRow, wireRadices, bval_bin, termStride]
    have hS₁ : P1Batch.bval s.1 = if all then j else j / termStride ag ℓ := by
      cases all
      · change P1Batch.bval (Carry.nat_div (word₀, keys)).1 = j / termStride ag ℓ
        rw [(bval_divide _ _).1, hj, hd]
      · exact hj
    have hS₂ : P1Batch.bval s.2 = if all then 0 else j % termStride ag ℓ := by
      cases all
      · change P1Batch.bval (Carry.nat_div (word₀, keys)).2 = j % termStride ag ℓ
        rw [(bval_divide _ _).2, hj, hd]
      · rfl
    refine ⟨?_, fun _ => ⟨hR, hM, hS₁, hS₂⟩⟩
    rw [hR, less_spec, hS₁]
    change ((bif (D.lv ℓ).shrink then decide ((if all then j else j / termStride ag ℓ) <
      P1Batch.bval (bin (D.lv ℓ).bases)) else false) = true) ↔ _
    rw [bval_bin]
    cases all
    · change ((bif (D.lv ℓ).shrink then decide (j / termStride ag ℓ < (D.lv ℓ).bases) else false) = true) ↔
        ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true ∧ j < (D.lv ℓ).bases * termStride ag ℓ
      cases (D.lv ℓ).shrink
      · simp only [Bool.cond_false, Bool.false_eq_true, false_and, and_false, h]
      · simp only [Bool.cond_true, decide_eq_true_eq, h, true_and,
          Nat.div_lt_iff_lt_mul (termStride_pos ag ℓ)]
    · change ((bif (D.lv ℓ).shrink then decide (j < (D.lv ℓ).bases) else false) = true) ↔
        ℓ ≤ D.top ∧ (D.lv ℓ).shrink = true ∧ j < (D.lv ℓ).bases
      cases (D.lv ℓ).shrink
      · simp only [Bool.cond_false, Bool.false_eq_true, false_and, and_false, h]
      · simp only [Bool.cond_true, decide_eq_true_eq, h, true_and]
  · refine ⟨?_, fun hn => (h hn).elim⟩
    rw [hr, ite_eq_right h]
    have hn : ¬ ShrinkIdx (if all then D else termDims D ag) (P1Batch.bval i) := by
      intro hi
      apply h
      cases all <;> exact hi.1
    simp only [defaultRow, Bool.cond_false, Bool.false_eq_true, hn]

theorem setupMotif_active (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord)
    (hi : ShrinkIdx (if all then D else termDims D ag) (P1Batch.bval i)) :
    let ℓ := P1Batch.bval i % 2 ^ levBits D
    let p := setupMotif all (motifFormat all D M ag, i)
    p = activeMotif all D ℓ (ag ℓ).1 (ag ℓ).2 (bin M) p.1.2.2.1 p.2.2 := by
  have h : P1Batch.bval i % 2 ^ levBits D ≤ D.top := by cases all <;> exact hi.1
  obtain ⟨hv, hs⟩ := setupMotif_spec all D M ag i
  exact Prod.ext (Prod.ext rfl (Prod.ext (hv.mpr hi) (Prod.ext rfl (hs h).1)))
    (Prod.ext (hs h).2.1 rfl)

end P1SolGreedy.SolDemand
