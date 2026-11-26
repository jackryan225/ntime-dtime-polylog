import P1Wit.Decode
import Mathlib.Algebra.BigOperators.Intervals

namespace P1Wit.SolWitfill

/-- A finite table read by its natural index, with the default outside its domain. -/
def atIndex {n : ℕ} {A : Type*} [Inhabited A] (f : Fin n → A) (i : ℕ) : A :=
  if h : i < n then f ⟨i, h⟩ else default

theorem atIndex_fin {n : ℕ} {A : Type*} [Inhabited A] (f : Fin n → A) (i : Fin n) :
    atIndex f i.val = f i := dite_eq_left i.isLt

theorem atIndex_lt {n k : ℕ} (f : Fin n → ℕ) (h : ∀ j, f j < 2 ^ k) (i : ℕ) :
    atIndex f i < 2 ^ k := by
  unfold atIndex
  split
  · exact h _
  · exact Nat.two_pow_pos _

/-- Bits of one payload field in coordinate order. -/
def arcBits {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool)
    (j : ℕ) : List Bool :=
  if h : j < n then List.ofFn (z ⟨j, h⟩) else []

theorem arcBits_fin {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool)
    (i : Fin n) : arcBits z i.val = List.ofFn (z i) := dite_eq_left i.isLt

theorem arcBits_length {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool)
    (j : ℕ) : (arcBits z j).length = atIndex w j := by
  unfold arcBits atIndex
  split
  · exact List.length_ofFn
  · rfl

/-- Sum of the lengths of the first `j` arc fields. -/
def widthPrefix (w : ℕ → ℕ) (j : ℕ) : ℕ := ∑ k ∈ Finset.range j, w k

theorem cat_length_eq_prefix (f : ℕ → List Bool) (j : ℕ) :
    (cat f j).length = widthPrefix (fun k => (f k).length) j := by
  induction j with
  | zero => simp [cat, widthPrefix]
  | succ j ih => simp only [cat, List.length_append, ih, widthPrefix, Finset.sum_range_succ]

/-- Concatenate the payload words in their prescribed arc order, placing bit 0 first. -/
def flatten {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool) : List Bool :=
  cat (arcBits z) n

theorem flatten_length {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool) :
    (flatten z).length = widthPrefix (atIndex w) n := by
  rw [flatten, cat_length_eq_prefix]
  simp only [arcBits_length]

theorem flatten_read {n : ℕ} {w : Fin n → ℕ} (z : (i : Fin n) → Fin (w i) → Bool)
    (i : Fin n) :
    ((flatten z).drop (widthPrefix (atIndex w) i.val)).take (w i) = List.ofFn (z i) := by
  obtain ⟨rest, hr⟩ := cat_split (arcBits z) i.isLt
  rw [flatten, hr, List.append_assoc, ← show (cat (arcBits z) i.val).length =
      widthPrefix (atIndex w) i.val by simp only [cat_length_eq_prefix, arcBits_length],
    List.drop_left, arcBits_fin, List.take_left' List.length_ofFn]

theorem flatten_injective {n : ℕ} (w : Fin n → ℕ) :
    Function.Injective (flatten (w := w)) := by
  intro z z' h
  funext i k
  have hi := (flatten_read z i).symm.trans
    ((congrArg (fun bits : List Bool => (bits.drop (widthPrefix (atIndex w) i.val)).take (w i)) h).trans
      (flatten_read z' i))
  simpa only [getD_ofFn] using congrArg (fun bits : List Bool => bits.getD k.val false) hi

end P1Wit.SolWitfill
