import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Basic

/-!
# P1, wave 2, checks C11 and C12 (lane P1-lean-W2-chkfinal), and the payload reader of C13

Paper `research/papers/ntime-dtime-polylog.tex` l.1055-1060 (C11, C12 in the REPAIRED form of PLAN.md section 9,
08:55Z), segment S3 (l.1027) and the payload order of C13 ("the bits of an arc are stored once, at its source
position, in the order base, lane, outgoing slot").

Data model (stored data only; P6 binds the readers): `N` final bases with addresses `0, ..., N-1`; `Ω y` the stored
prefix (P4) of base `y`; `ws y` the sum of the widths read from the stored final panel (P2) of `y`; `tail` the
segment S3 (payload `z`, then zeros up to `m`).

* `C11 N Ω ws y` (one per final base `y < N`; `y ≥ N` accepts): `Ω 0 = 0` at the first base; `Ω (y+1) = Ω y + ws y` only when
  `y + 1 < N` (the last base has no stored successor; its sum is checked by C12).
* `C12 N Ω ws tail` (one): with `total = Ω (N-1) + ws (N-1)` (`0` if `N = 0`): `total ≤ |tail|` and every bit of
  `tail` from position `total` on is `0`.
* `C11_true`, `C11_unique`, `C11_iff`; `C12_true`, `C12_unique`: the checks hold exactly for the true prefixes
  `pre ws` and for `tail = z ++ zeros` with `|z| = pre ws N`.
* `read_arc`: in the payload of the encoder (arcs in the order base, then arc index `t < A`), the field at offset
  `Ω y + pre (w y) t` of length `w y t` is the bit string of arc `(y, t)`. This is how C13 reads `z|_v`.
-/

namespace P1ChkFinal

open Finset

/-! ## Prefix sums -/

/-- `pre w y = w 0 + ... + w (y - 1)`. -/
def pre (w : ℕ → ℕ) (y : ℕ) : ℕ := ∑ i ∈ range y, w i

@[simp] theorem pre_zero (w : ℕ → ℕ) : pre w 0 = 0 := by simp [pre]

theorem pre_succ (w : ℕ → ℕ) (y : ℕ) : pre w (y + 1) = pre w y + w y := sum_range_succ _ _

/-! ## Check C11 (repaired form) -/

/-- **Check C11** at final base `y`, for `N` final bases, stored prefixes `Ω` and stored width sums `ws`. -/
def C11 (N : ℕ) (Ω ws : ℕ → ℕ) (y : ℕ) : Prop :=
  y < N → (y = 0 → Ω 0 = 0) ∧ (y + 1 < N → Ω (y + 1) = Ω y + ws y)

/-- Indices out of range accept (D5 amendment). -/
theorem C11_out {N : ℕ} {Ω ws : ℕ → ℕ} {y : ℕ} (hy : N ≤ y) : C11 N Ω ws y :=
  fun h => absurd h (not_lt.mpr hy)

/-- **C11, soundness.** The true prefixes pass C11 at every base. -/
theorem C11_true (N : ℕ) (ws : ℕ → ℕ) (y : ℕ) : C11 N (pre ws) ws y :=
  fun _ => ⟨fun _ => pre_zero ws, fun _ => pre_succ ws y⟩

/-- **C11, uniqueness.** If C11 holds at every final base, the stored prefixes are the true ones. -/
theorem C11_unique {N : ℕ} {Ω ws : ℕ → ℕ} (h : ∀ y < N, C11 N Ω ws y) : ∀ y < N, Ω y = pre ws y := by
  intro y hy
  induction y with
  | zero => rw [(h 0 hy hy).1 rfl, pre_zero]
  | succ y ih =>
    have hy' : y < N := Nat.lt_of_succ_lt hy
    rw [(h y hy' hy').2 hy, ih hy', pre_succ]

/-- C11 at every final base holds iff the stored prefixes are the true ones (at the `N` actual bases). -/
theorem C11_iff {N : ℕ} {Ω ws : ℕ → ℕ} : (∀ y < N, C11 N Ω ws y) ↔ ∀ y < N, Ω y = pre ws y := by
  refine ⟨C11_unique, fun h y hy _ => ⟨?_, fun hy1 => ?_⟩⟩
  · rintro rfl
    rw [h 0 hy, pre_zero]
  · rw [h (y + 1) hy1, h y hy, pre_succ]

/-! ## Check C12 (zero tail) -/

/-- The payload length claimed by the stored data: the prefix plus the width sum of the last final base. -/
def total (N : ℕ) (Ω ws : ℕ → ℕ) : ℕ := if N = 0 then 0 else Ω (N - 1) + ws (N - 1)

/-- **Check C12**: the claimed payload length fits into S3 and S3 is zero after it. -/
def C12 (N : ℕ) (Ω ws : ℕ → ℕ) (tail : List Bool) : Prop :=
  total N Ω ws ≤ tail.length ∧ ∀ b ∈ tail.drop (total N Ω ws), b = false

theorem total_pre (N : ℕ) (ws : ℕ → ℕ) : total N (pre ws) ws = pre ws N := by
  cases N with
  | zero => simp [total]
  | succ n => simp only [total, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, pre_succ]

/-- Under C11 the claimed payload length is the true one. -/
theorem total_eq {N : ℕ} {Ω ws : ℕ → ℕ} (h : ∀ y < N, C11 N Ω ws y) : total N Ω ws = pre ws N := by
  cases N with
  | zero => simp [total]
  | succ n =>
    simp only [total, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [C11_unique h n (Nat.lt_succ_self n), pre_succ]

/-- **C12, soundness.** The true prefixes and S3 = payload of the true length, then zeros, pass C12. -/
theorem C12_true (N : ℕ) (ws : ℕ → ℕ) (z : List Bool) (hz : z.length = pre ws N) (k : ℕ) :
    C12 N (pre ws) ws (z ++ List.replicate k false) := by
  rw [C12, total_pre, ← hz]
  refine ⟨by simp, fun b hb => ?_⟩
  rw [List.drop_left] at hb
  exact List.eq_of_mem_replicate hb

/-- **C12, uniqueness.** Under C11 at every final base and C12, S3 is a payload of the true length
`pre ws N` followed by zeros. -/
theorem C12_unique {N : ℕ} {Ω ws : ℕ → ℕ} {tail : List Bool} (h11 : ∀ y < N, C11 N Ω ws y)
    (h12 : C12 N Ω ws tail) :
    pre ws N ≤ tail.length ∧
      tail = tail.take (pre ws N) ++ List.replicate (tail.length - pre ws N) false := by
  rw [C12, total_eq h11] at h12
  obtain ⟨hl, hz⟩ := h12
  refine ⟨hl, ?_⟩
  conv_lhs => rw [← List.take_append_drop (pre ws N) tail]
  congr 1
  rw [List.eq_replicate_iff]
  exact ⟨List.length_drop, hz⟩

/-! ## The payload reader of C13 -/

/-- Concatenation of `f 0, ..., f (n-1)`. -/
def cat {α : Type*} (f : ℕ → List α) (n : ℕ) : List α := (List.range n).flatMap f

theorem cat_succ {α : Type*} (f : ℕ → List α) (n : ℕ) : cat f (n + 1) = cat f n ++ f n := by
  simp [cat, List.range_succ, List.flatMap_append]

theorem length_cat {α : Type*} (f : ℕ → List α) (n : ℕ) :
    (cat f n).length = pre (fun j => (f j).length) n := by
  induction n with
  | zero => simp [cat]
  | succ n ih => rw [cat_succ, List.length_append, ih, pre_succ]

/-- Dropping the prefix sum of the first `i` lengths from `cat f n ++ rest` leaves `f i ++ (something)`. -/
theorem drop_cat {α : Type*} (f : ℕ → List α) {n i : ℕ} (hi : i < n) (rest : List α) :
    ∃ r, (cat f n ++ rest).drop (pre (fun j => (f j).length) i) = f i ++ r := by
  induction n generalizing rest with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rw [cat_succ, List.append_assoc]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih h (f n ++ rest)
    · subst h
      refine ⟨rest, ?_⟩
      rw [List.drop_left' (length_cat f i)]

/-- **Arc reader.** The payload of the encoder lists, for each final base `y < N` in address order, the bit
strings `zz y t` of its arcs `t < A` (order: lane, then out-slot, as fixed by P6), `|zz y t| = w y t`. With the
true prefixes `Ω = pre ws`, `ws y = pre (w y) A`, the field of length `w y t` at offset `Ω y + pre (w y) t` of
S3 (any continuation `rest`) is `zz y t`. -/
theorem read_arc {N A : ℕ} {w : ℕ → ℕ → ℕ} (zz : ℕ → ℕ → List Bool) (hzz : ∀ y t, (zz y t).length = w y t)
    (rest : List Bool) {y t : ℕ} (hy : y < N) (ht : t < A) :
    ((cat (fun y => cat (zz y) A) N ++ rest).drop (pre (fun y => pre (w y) A) y + pre (w y) t)).take (w y t) =
      zz y t := by
  have hlen : (fun y => (cat (zz y) A).length) = fun y => pre (w y) A := by
    funext y
    rw [length_cat]
    simp only [hzz]
  obtain ⟨r, hr⟩ := drop_cat (fun y => cat (zz y) A) hy rest
  rw [hlen] at hr
  rw [← List.drop_drop, hr]
  have hlen2 : (fun t => (zz y t).length) = w y := by
    funext t
    exact hzz y t
  obtain ⟨r2, hr2⟩ := drop_cat (zz y) ht r
  rw [hlen2] at hr2
  rw [hr2, List.take_left' (hzz y t)]

/-- The reader with STORED prefixes: under C11 at every final base, the stored prefix gives the same field. -/
theorem read_arc_of_C11 {N A : ℕ} {w : ℕ → ℕ → ℕ} {Ω : ℕ → ℕ} (zz : ℕ → ℕ → List Bool)
    (hzz : ∀ y t, (zz y t).length = w y t)
    (h11 : ∀ y < N, C11 N Ω (fun y => pre (w y) A) y) (rest : List Bool) {y t : ℕ} (hy : y < N) (ht : t < A) :
    ((cat (fun y => cat (zz y) A) N ++ rest).drop (Ω y + pre (w y) t)).take (w y t) = zz y t := by
  rw [C11_unique h11 y hy]
  exact read_arc zz hzz rest hy ht

end P1ChkFinal
