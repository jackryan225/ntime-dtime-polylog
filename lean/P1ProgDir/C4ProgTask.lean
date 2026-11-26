import P1ProgDir.C4ProgPrepare
import P1ProgDir.C4ProgLength

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Wit P1ChkDir

/-- The level-zero part of the witness format as a function of input length. -/
structure C4Format (K : Type) where
  dims : ℕ → Dims
  height : ℕ → ℕ
  tapes : ℕ → K → ℕ
  contentWidth : ℕ → ℕ
  stateWidth : ℕ → ℕ
  tableWidth : ℕ → ℕ

variable {K : Type} [Fintype K] [DecidableEq K] {a : ℕ}

abbrev C4Query := Word × Word × Word

def C4Format.check (F : C4Format K) (ha : 4 ≤ 2 ^ a) (n : ℕ) (u : Word) (i : ℕ) : Prop :=
  C4F ha (F.dims n) (dirAt (F.dims n) (F.tapes n) (F.dims n).I (2 ^ F.height n)) u
    (F.contentWidth n) (F.stateWidth n) (F.tableWidth n) i

noncomputable def C4Format.prepareAtLength (F : C4Format K) (a n m i : ℕ) : ReadPlan :=
  prepareC4 (F.dims n) (F.tapes n) a (F.height n) m
    (F.contentWidth n) (F.stateWidth n) (F.tableWidth n) i

noncomputable def C4Format.prepare (F : C4Format K) (a : ℕ) (query : C4Query) : ReadPlan :=
  F.prepareAtLength a (value query.1) (value query.2.1) (value query.2.2)

theorem C4Format.widths_dom (F : C4Format K) (a : ℕ) (W : ℕ → ℕ)
    (hW : ∀ n s, s < 13 → (F.dims n).width s ≤ W n)
    (hSmall : Dom size (fun q : C4Query => W (value q.1)))
    (hLanes : Dom size (fun q : C4Query => 2 ^ F.height (value q.1))) :
    Dom size (fun q : C4Query => allFieldWidths (F.prepare a q)) :=
  (((Dom.const _ 3).add ((Dom.const _ (2 ^ a)).mul ((Dom.const _ 6).add hLanes))).mul hSmall).mono
    (fun q => widths_prepareC4 (F.dims (value q.1)) (F.tapes (value q.1)) _ _ _ _ _ _ _ _ (hW _))

/-- The input to format preparation contains the two binary lengths and the
selector word. It contains no witness field values. -/
def compactQuery (p : C4Query) : C4Query :=
  (Length.born p.1.length, Length.born p.2.1.length, p.2.2)

theorem compactQuery_size (p : C4Query) : size (compactQuery p) ≤
    2 * (Nat.log 2 (p.1.length + 1) + 1 + (Nat.log 2 (p.2.1.length + 1) + 1) + p.2.2.length) + 5 := by
  have h₁ := Length.length_born_log p.1.length
  have h₂ := Length.length_born_log p.2.1.length
  have hn : Nat.log 2 p.1.length ≤ Nat.log 2 (p.1.length + 1) := Nat.log_mono_right (Nat.le_succ _)
  have hm : Nat.log 2 p.2.1.length ≤ Nat.log 2 (p.2.1.length + 1) := Nat.log_mono_right (Nat.le_succ _)
  simp only [compactQuery, size_prod, size_word]
  omega

open scoped Classical in
theorem taskC4_of_format (F : C4Format K) (ha : 4 ≤ 2 ^ a)
    (hFormat : Poly (F.prepare a))
    (hWidths : Dom size (fun q : C4Query => allFieldWidths (F.prepare a q))) :
    ∃ k C : ℕ, Task (fun p : C4Query => size p + p.2.1.length + C * (size (compactQuery p) + 1) ^ k)
      (fun p => send p) (fun p => send (decide (F.check ha p.1.length p.2.1 (P1Batch.bval p.2.2)))) := by
  let u (p : C4Query) := p.2.1
  let plan (p : C4Query) := F.prepare a (compactQuery p)
  let s (p : C4Query) := size (compactQuery p)
  have he : Task size (fun p : C4Query => send p) (fun p => send (compactQuery p, u p)) :=
    easy_queryLengths Length.born Length.easy_lengthWord
  have hPre := ScanTask.compact (u := u) (small := s) hFormat compactQuery (Dom.base s)
  have hMid := checkPlan_task u s plan (by
    intro p
    simp only [plan, C4Format.prepare, compactQuery, Length.birthValue, u]
    exact prepareC4_length ..)
    (hFormat.length.map compactQuery) (hWidths.map compactQuery)
  obtain ⟨budget, ⟨k, C, hb⟩, hT⟩ := hPre.compose hMid
  refine ⟨k, C, ((Task.compose he hT).mono ?_).conform (fun _ => rfl) (fun _ => rfl) ?_⟩
  · intro p
    have h := hb p
    dsimp only [u, s] at h ⊢
    omega
  · intro p
    apply congrArg (send (X := Bool))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, u, plan, C4Format.prepare, compactQuery, Length.birthValue,
      bval_eq_value, C4Format.check]
    rw [C4Format.prepareAtLength]
    exact checkPlan_prepareC4 (D := F.dims p.1.length) (h := F.height p.1.length)
      (F.tapes p.1.length) ha p.2.1 (F.contentWidth p.1.length)
      (F.stateWidth p.1.length) (F.tableWidth p.1.length) (value p.2.2)

end P1ProgDir.SolC4

#print axioms P1ProgDir.SolC4.checkPlan_prepareC4
#print axioms P1ProgDir.SolC4.taskC4_of_format
