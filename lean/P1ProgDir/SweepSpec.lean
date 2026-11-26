import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace P1ProgDir.SolSweepSpec

/-- A full left-to-right row scan visits all rows in order, even after
the accumulated answer becomes false. -/
def sweep {A : Type} (test : ℕ → A → Bool) (rows : List A) (first : ℕ) (ok : Bool) :=
  rows.foldl (fun acc row => (acc.1 + 1, acc.2 && test acc.1 row)) (first, ok)

theorem sweep_index {A : Type} (test : ℕ → A → Bool) (rows : List A) (first : ℕ) (ok : Bool) :
    (sweep test rows first ok).1 = first + rows.length := by
  unfold sweep
  induction rows generalizing first ok with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, ih]
    omega

theorem sweep_correct {A : Type} (test : ℕ → A → Bool) (rows : List A) (first : ℕ) (ok : Bool) :
    (sweep test rows first ok).2 = true ↔
      ok = true ∧ ∀ j : Fin rows.length, test (first + j.val) rows[j] = true := by
  unfold sweep
  induction rows generalizing first ok with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Bool.and_eq_true]
    have get_succ (j : Fin xs.length) : (x :: xs)[j.succ] = xs[j] := by
      change (x :: xs)[j.val + 1] = xs[j.val]
      exact List.getElem_cons_succ x xs j.val (by simpa using j.isLt)
    constructor
    · rintro ⟨⟨ha, hx⟩, hs⟩
      refine ⟨ha, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · simpa using hx
      · have h := hs j'
        simpa only [get_succ, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h
    · rintro ⟨ha, hj⟩
      refine ⟨⟨ha, ?_⟩, fun j => ?_⟩
      · simpa using hj ⟨0, by simp⟩
      · have h := hj j.succ
        simpa only [get_succ, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h

end P1ProgDir.SolSweepSpec
