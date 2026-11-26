import P1Case1.Flip

/-!
# P1, Case 1, task C1: the verdict of the coTRANS verifier and the guess code (lane case1b, copy A)

The verifier reads the guess `w` (length exactly `guessLen n`, `n = |x|`) as two interleaved numbers:
`i` from the bits at even positions, `k` from the bits at odd positions, least significant bit first.
(On a stack the last bit read is on top, so the stack decodes with `v ↦ 2 v + b` from the top: `val`.)

`Verdict w x`: `|x| = 2 N²`, `i < N`, `k < N` and entry `(i, k)` of the first matrix differs from entry
`(k, i)` of the second one (`CoTrans` of `Flip.lean`, positional form).

Main result: `coTRANS_iff_verdict : coTRANS x = true ↔ ∃ w, |w| = guessLen |x| ∧ verdict w x = true`.
The guess budget suffices because `N < 2^(⌊g/2⌋)` for `g = guessLen (2N²) = ⌊log₂ (4 N⁴)⌋`.
-/

namespace P1Case1.CoTransV

open C1Challenge

/-- Elements at even positions `0, 2, 4, …`. -/
def evens {α : Type} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: t => a :: evens t

/-- Elements at odd positions `1, 3, 5, …`. -/
def odds {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: t => b :: odds t

/-- Stack decoding: the head is the most significant bit. -/
def val (l : List Bool) : ℕ := l.foldl (fun v b => 2 * v + b.toNat) 0

/-- The two numbers of a guess. -/
def guessI (w : List Bool) : ℕ := val (evens w).reverse
def guessK (w : List Bool) : ℕ := val (odds w).reverse

/-- The verdict of the verifier on guess `w` and word `x`. -/
def Verdict (w x : List Bool) : Prop :=
  ∃ N : ℕ, x.length = 2 * N * N ∧ guessI w < N ∧ guessK w < N ∧
    x.getD (N * guessI w + guessK w) false ≠ x.getD (N * N + N * guessK w + guessI w) false

open Classical in
/-- The verdict as a Boolean. -/
noncomputable def verdict (w x : List Bool) : Bool := decide (Verdict w x)

theorem verdict_eq_true {w x : List Bool} : verdict w x = true ↔ Verdict w x := by
  simp [verdict]

/-! ## Binary code -/

theorem val_append_single (l : List Bool) (b : Bool) : val (l ++ [b]) = 2 * val l + b.toNat := by
  simp [val, List.foldl_append]

/-- `L` bits of `i`, most significant first. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | L + 1, i => toBits L (i / 2) ++ [decide (i % 2 = 1)]

theorem length_toBits (L i : ℕ) : (toBits L i).length = L := by
  induction L generalizing i with
  | zero => rfl
  | succ L ih => simp [toBits, ih]

theorem val_toBits (L : ℕ) : ∀ i : ℕ, i < 2 ^ L → val (toBits L i) = i := by
  induction L with
  | zero => intro i hi; simp at hi; subst hi; rfl
  | succ L ih =>
    intro i hi
    rw [toBits, val_append_single, ih (i / 2) (by rw [pow_succ] at hi; omega)]
    have h2 : (decide (i % 2 = 1)).toNat = i % 2 := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    omega

/-! ## Interleaving -/

/-- `x₀ y₀ x₁ y₁ …`. -/
def interleave {α : Type} : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  | xs, [] => xs
  | [], ys => ys

theorem interleave_spec {α : Type} :
    ∀ (xs ys : List α), (xs.length = ys.length ∨ xs.length = ys.length + 1) →
      evens (interleave xs ys) = xs ∧ odds (interleave xs ys) = ys ∧
        (interleave xs ys).length = xs.length + ys.length
  | [], [], _ => ⟨rfl, rfl, rfl⟩
  | [x], [], _ => ⟨rfl, rfl, rfl⟩
  | x :: xs, y :: ys, h => by
    have h' : xs.length = ys.length ∨ xs.length = ys.length + 1 := by
      simp only [List.length_cons] at h; omega
    obtain ⟨h1, h2, h3⟩ := interleave_spec xs ys h'
    refine ⟨?_, ?_, ?_⟩
    · simp only [interleave, evens, h1]
    · simp only [interleave, odds, h2]
    · simp only [interleave, List.length_cons, h3]; omega
  | [], _ :: _, h => by simp at h
  | _ :: _ :: _, [], h => by simp at h

/-! ## The guess budget -/

/-- For `n = 2N²` the guess has `guessLen n = ⌊log₂ (4N⁴)⌋` bits and `N < 2^(⌊g/2⌋)`. -/
theorem lt_two_pow_half {N : ℕ} (hN : 0 < N) : N < 2 ^ (guessLen (2 * N * N) / 2) := by
  set g := guessLen (2 * N * N) with hg
  have h1 : (2 * N * N) ^ 2 < 2 ^ (g + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  by_contra hcon'
  have hcon : 2 ^ (g / 2) ≤ N := Nat.le_of_not_lt hcon'
  have h2 : 2 ^ (g + 1) ≤ 2 ^ (2 * (g / 2) + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (2 * (g / 2) + 2) = 4 * (2 ^ (g / 2)) ^ 2 := by
    rw [show 2 * (g / 2) + 2 = (g / 2) * 2 + 2 by ring, pow_add, pow_mul]; ring
  have h4 : (2 ^ (g / 2)) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hcon 2
  have h5 : N ^ 2 ≤ N ^ 2 * N ^ 2 := Nat.le_mul_of_pos_right _ (pow_pos hN 2)
  have h6 : (2 * N * N) ^ 2 = 4 * (N ^ 2 * N ^ 2) := by ring
  omega

/-- **Guess code.** Any pair `i < 2^⌈g/2⌉`, `k < 2^⌊g/2⌋` is the pair of some guess of length `g`. -/
theorem exists_guess {g i k : ℕ} (hi : i < 2 ^ ((g + 1) / 2)) (hk : k < 2 ^ (g / 2)) :
    ∃ w : List Bool, w.length = g ∧ guessI w = i ∧ guessK w = k := by
  set xs := (toBits ((g + 1) / 2) i).reverse with hxs_def
  set ys := (toBits (g / 2) k).reverse with hys_def
  have hxs : xs.length = (g + 1) / 2 := by rw [hxs_def, List.length_reverse, length_toBits]
  have hys : ys.length = g / 2 := by rw [hys_def, List.length_reverse, length_toBits]
  obtain ⟨he, ho, hl⟩ := interleave_spec xs ys (by rw [hxs, hys]; omega)
  refine ⟨interleave xs ys, by rw [hl, hxs, hys]; omega, ?_, ?_⟩
  · rw [guessI, he, hxs_def, List.reverse_reverse, val_toBits ((g + 1) / 2) i hi]
  · rw [guessK, ho, hys_def, List.reverse_reverse, val_toBits (g / 2) k hk]

/-! ## coTRANS and the verdict -/

theorem coTRANS_iff_verdict (x : List Bool) :
    coTRANS x = true ↔ ∃ w : List Bool, w.length = guessLen x.length ∧ verdict w x = true := by
  have hco : coTRANS x = true ↔ CoTrans x := by simp [coTRANS]
  rw [hco]
  constructor
  · rintro ⟨N, i, k, hi, hk, hlen, hne⟩
    have hN : 0 < N := by omega
    set g := guessLen x.length with hg
    have hb : N < 2 ^ (g / 2) := by rw [hg, hlen]; exact lt_two_pow_half hN
    have ha : N < 2 ^ ((g + 1) / 2) :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    set xs := (toBits ((g + 1) / 2) i).reverse with hxs_def
    set ys := (toBits (g / 2) k).reverse with hys_def
    have hxs : xs.length = (g + 1) / 2 := by rw [hxs_def, List.length_reverse, length_toBits]
    have hys : ys.length = g / 2 := by rw [hys_def, List.length_reverse, length_toBits]
    obtain ⟨he, ho, hl⟩ := interleave_spec xs ys (by rw [hxs, hys]; omega)
    have hI : guessI (interleave xs ys) = i := by
      rw [guessI, he, hxs_def, List.reverse_reverse, val_toBits ((g + 1) / 2) i (by omega)]
    have hK : guessK (interleave xs ys) = k := by
      rw [guessK, ho, hys_def, List.reverse_reverse, val_toBits (g / 2) k (by omega)]
    refine ⟨interleave xs ys, by rw [hl, hxs, hys]; omega, ?_⟩
    rw [verdict_eq_true]
    exact ⟨N, hlen, by rw [hI]; exact hi, by rw [hK]; exact hk, by rw [hI, hK]; exact hne⟩
  · rintro ⟨w, -, hv⟩
    obtain ⟨N, hlen, hi, hk, hne⟩ := verdict_eq_true.mp hv
    exact ⟨N, guessI w, guessK w, hi, hk, hlen, hne⟩

end P1Case1.CoTransV
