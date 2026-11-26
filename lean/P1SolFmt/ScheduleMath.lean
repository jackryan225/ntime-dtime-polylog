import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.TakeDrop

namespace P1SolFmt.SolSchedule

variable {A : Type*}

def blocks (block : List A) : ℕ → List A
  | 0 => []
  | t + 1 => block ++ blocks block t

theorem blocks_length (block : List A) (t : ℕ) :
    (blocks block t).length = block.length * t := by
  induction t with
  | zero => simp only [blocks, List.length_nil, Nat.mul_zero]
  | succ t ih => rw [blocks, List.length_append, ih, Nat.mul_succ, Nat.add_comm]

theorem blocks_get (block : List A) (t i : ℕ) (h : i < block.length * t) :
    (blocks block t)[i]? = block[i % block.length]? := by
  induction t generalizing i with
  | zero => simp only [Nat.mul_zero, Nat.not_lt_zero] at h
  | succ t ih =>
    rw [blocks]
    by_cases hi : i < block.length
    · rw [List.getElem?_append_left hi, Nat.mod_eq_of_lt hi]
    · have hle : block.length ≤ i := by omega
      have hj : i - block.length < block.length * t := by
        rw [Nat.mul_succ] at h
        omega
      have he : (i - block.length) % block.length = i % block.length := by
        conv_rhs => rw [show i = i - block.length + block.length by omega, Nat.add_mod_right]
      rw [List.getElem?_append_right hle, ih _ hj, he]

theorem blocks_take (block : List A) (t i : ℕ) (h : i ≤ block.length * t) :
    (blocks block t).take i = blocks block (i / block.length) ++ block.take (i % block.length) := by
  induction t generalizing i with
  | zero =>
    have hi : i = 0 := by simpa only [Nat.mul_zero, Nat.le_zero] using h
    subst i
    simp only [blocks, List.take_zero, Nat.zero_div, Nat.zero_mod, List.nil_append]
  | succ t ih =>
    rw [blocks]
    by_cases hi : i < block.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hi), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, blocks,
        List.nil_append]
    · by_cases hb : 0 < block.length
      · have hle : block.length ≤ i := by omega
        have hj : i - block.length ≤ block.length * t := by
          rw [Nat.mul_succ] at h
          omega
        have he : (i - block.length) % block.length = i % block.length := by
          conv_rhs => rw [show i = i - block.length + block.length by omega, Nat.add_mod_right]
        have hq : i / block.length = (i - block.length) / block.length + 1 := by
          conv_lhs => rw [show i = i - block.length + block.length * 1 by omega,
            Nat.add_mul_div_left _ _ hb]
        rw [List.take_append, List.take_of_length_le hle, ih _ hj, he, hq, blocks, List.append_assoc]
      · have hnil : block = [] := List.length_eq_zero_iff.1 (by omega)
        subst block
        simp only [List.length_nil, Nat.zero_mul, Nat.le_zero] at h
        subst i
        simp only [List.take_zero, Nat.zero_div, Nat.zero_mod, blocks, List.append_nil]

theorem blocks_prod (block : List A) (f : A → ℕ) (t : ℕ) :
    ((blocks block t).map f).prod = (block.map f).prod ^ t := by
  induction t with
  | zero => simp only [blocks, List.map_nil, List.prod_nil, pow_zero]
  | succ t ih => rw [blocks, List.map_append, List.prod_append, ih, pow_succ']

theorem blocks_sum (block : List A) (f : A → ℕ) (t : ℕ) :
    ((blocks block t).map f).sum = (block.map f).sum * t := by
  induction t with
  | zero => simp only [blocks, List.map_nil, List.sum_nil, Nat.mul_zero]
  | succ t ih =>
    rw [blocks, List.map_append, List.sum_append, ih, Nat.mul_succ, Nat.add_comm]

/-- A row is determined by the two accumulated prefix statistics and the current phase. -/
theorem indexedRows {L : Type*} (build : ℕ → ℕ → Option A → L)
    (rows : ℕ → ℕ → List A → List L) (divisor loss : A → ℕ)
    (hnil : ∀ p g, rows p g [] = [build p g none])
    (hcons : ∀ p g ph xs, rows p g (ph :: xs) =
      build p g (some ph) :: rows (p / divisor ph) (g - loss ph) xs)
    (fallback : L) (p g : ℕ) (xs : List A) (i : ℕ) :
    ((rows p g xs)[i]?).getD fallback =
      if i ≤ xs.length then
        build (p / ((xs.take i).map divisor).prod) (g - ((xs.take i).map loss).sum) (xs[i]?)
      else fallback := by
  induction xs generalizing p g i with
  | nil =>
    cases i with
    | zero =>
      simp only [hnil, List.length_nil, Nat.le_refl, ite_true, List.getElem?_cons_zero,
        Option.getD_some, List.getElem?_nil, List.take_zero, List.map_nil,
        List.sum_nil, List.prod_nil, Nat.sub_zero, Nat.div_one]
    | succ i =>
      have hi : ¬i + 1 ≤ 0 := by omega
      simp only [hnil, List.length_nil, ite_eq_right hi, List.getElem?_cons_succ,
        List.getElem?_nil, Option.getD_none]
  | cons ph xs ih =>
    cases i with
    | zero =>
      simp only [hcons, List.getElem?_cons_zero, Option.getD_some, Nat.zero_le, ite_true,
        List.take_zero, List.map_nil, List.sum_nil, List.prod_nil, Nat.sub_zero, Nat.div_one]
    | succ i =>
      simpa only [hcons, List.getElem?_cons_succ, List.length_cons, Nat.succ_le_succ_iff,
        List.take_succ_cons, List.map_cons, List.sum_cons, List.prod_cons, Nat.sub_sub,
        Nat.div_div_eq_div_mul] using ih (p / divisor ph) (g - loss ph) i

end P1SolFmt.SolSchedule
