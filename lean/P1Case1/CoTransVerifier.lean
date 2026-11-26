import P1Case1.CoTransDecode
import P1Case1.CoTransFinal

/-!
# P1, Case 1, task C1: the verifier `readGuess; decode 1 5; decode 2 6; rest` (lane case1b, copy A)

`ntime_coTRANS_of_rest`: `NTIMELinLog coTRANS` from the run lemma of the last part `rest` (copy B,
`CoTransLoops.lean`): from registers `0 = x`, `5 = i`, `6 = k` (unary), all others empty, `rest` leaves on
top of register `0` the truth value of `∃ N, |x| = 2N², i < N, k < N, x[N i + k] ≠ x[N² + N k + i]`, in
cost `K (|x| + i + k + 1)`. The decoded numbers satisfy `i, k < 2^⌈g/2⌉ ≤ 2 (|x| + 1)`, so the total cost
is linear in `|withGuess w x|`.
-/

namespace P1Case1.CoTransV

open OAI.Computability.IntegerMultiplication P1Case1.CoTrans C1Challenge

theorem length_evens_odds : ∀ w : List Bool,
    (evens w).length = (w.length + 1) / 2 ∧ (odds w).length = w.length / 2
  | [] => by simp [evens, odds]
  | [_] => by simp [evens, odds]
  | _ :: _ :: t => by
    obtain ⟨h1, h2⟩ := length_evens_odds t
    simp only [evens, odds, List.length_cons, h1, h2]
    omega

theorem length_pairs (w : List Bool) : (w.flatMap fun b => [true, b]).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem length_withGuess (w x : List Bool) :
    (withGuess w x).length = 2 * w.length + 1 + x.length := by
  simp only [withGuess, List.length_append, length_pairs, List.length_cons]
  omega

/-- The guess budget is logarithmic: `2^⌈g/2⌉ ≤ 2 (n + 1)` for `g = guessLen n`. -/
theorem pow_half_le (n : ℕ) : 2 ^ ((guessLen n + 1) / 2) ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [guessLen]
  · set g := guessLen n with hg
    have h1 : 2 ^ g ≤ n ^ 2 := Nat.pow_log_le_self 2 (by positivity)
    set h := (g + 1) / 2 with hh
    have h2 : 2 ^ (2 * h) ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (2 * h) = 2 ^ h * 2 ^ h := by rw [two_mul, pow_add]
    have e2 : 2 ^ (g + 1) = 2 * 2 ^ g := by rw [pow_succ]; ring
    by_contra hc'
    have hc : 2 * (n + 1) < 2 ^ h := Nat.lt_of_not_le hc'
    have hsq : (2 * (n + 1)) * (2 * (n + 1)) < 2 ^ h * 2 ^ h := Nat.mul_self_lt_mul_self hc
    nlinarith

/-- The verifier: read the guess, decode both numbers, run `rest`. -/
def verifier (rest : Pg) : Pg := .join readGuess (.join (decode 1 5) (.join (decode 2 6) rest))

theorem val_reverse_evens_lt (w : List Bool) : guessI w < 2 ^ ((w.length + 1) / 2) := by
  have := val_lt (evens w).reverse
  rwa [List.length_reverse, (length_evens_odds w).1] at this

theorem val_reverse_odds_lt (w : List Bool) : guessK w < 2 ^ (w.length / 2) := by
  have := val_lt (odds w).reverse
  rwa [List.length_reverse, (length_evens_odds w).2] at this

/-- **C1 from the run lemma of `rest`.** -/
theorem ntime_coTRANS_of_rest (rest : Pg) (K : ℕ)
    (hrest : ∀ (Γ : Sc) (r : Rg) (x : List Bool) (i k : ℕ), r 0 = x →
      r 5 = List.replicate i true → r 6 = List.replicate k true →
      (∀ j, j ≠ 0 → j ≠ 5 → j ≠ 6 → r j = []) →
      ∃ (r1 : Rg) (b : Bool), Runs Γ rest r r1 (K * (x.length + i + k + 1)) ∧
        (r1 0).head? = some b ∧
        (b = true ↔ ∃ N, x.length = 2 * N * N ∧ i < N ∧ k < N ∧
          x.getD (N * i + k) false ≠ x.getD (N * N + N * k + i) false)) :
    NTIMELinLog coTRANS := by
  refine ntime_coTRANS_of_runs (verifier rest) (400 + 10 * K) ?_
  intro x w hw
  set r0 := initReg (withGuess w x) with hr0
  have hr0j : ∀ j, j ≠ 0 → r0 j = [] := by intro j hj; simp [hr0, initReg, hj]
  have h0 : r0 0 = withGuess w x := by simp [hr0, initReg]
  have hA := run_readGuess [] w x r0 h0
  set r1 := readF w x r0 with hr1
  have h11 : r1 1 = (evens w).reverse := by simp [hr1, readF, hr0j]
  have h12 : r1 2 = (odds w).reverse := by simp [hr1, readF, hr0j]
  have h1j : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → r1 j = [] := by
    intro j a b c; simp [hr1, readF, a, b, c, hr0j]
  have hB := runs_decode (S := 1) (R := 5) (by norm_num) (by norm_num) (by norm_num) [] r1
    (h1j 5 (by norm_num) (by norm_num) (by norm_num)) (h1j 7 (by norm_num) (by norm_num) (by norm_num))
  set r2 := Function.update (Function.update r1 1 []) 5 (List.replicate (val (r1 1)) true) with hr2
  have h22 : r2 2 = (odds w).reverse := by simp [hr2, h12]
  have hC := runs_decode (S := 2) (R := 6) (by norm_num) (by norm_num) (by norm_num) [] r2
    (by simp [hr2, h1j 6 (by norm_num) (by norm_num) (by norm_num)])
    (by simp [hr2, h1j 7 (by norm_num) (by norm_num) (by norm_num)])
  set r3 := Function.update (Function.update r2 2 []) 6 (List.replicate (val (r2 2)) true) with hr3
  have h30 : r3 0 = x := by simp [hr3, hr2, hr1, readF]
  have h35 : r3 5 = List.replicate (guessI w) true := by simp [hr3, hr2, h11, guessI]
  have h36 : r3 6 = List.replicate (guessK w) true := by simp [hr3, h22, guessK]
  have h3j : ∀ j, j ≠ 0 → j ≠ 5 → j ≠ 6 → r3 j = [] := by
    intro j a b c
    by_cases j1 : j = 1
    · subst j1; simp [hr3, hr2]
    · by_cases j2 : j = 2
      · subst j2; simp [hr3]
      · simp [hr3, hr2, a, b, c, j1, j2, h1j j a j1 j2]
  obtain ⟨r4, b, hD, hb0, hbiff⟩ := hrest [] r3 x (guessI w) (guessK w) h30 h35 h36 h3j
  refine ⟨r4, (hA.join (hB.join (hC.join hD))).mono ?_, ?_⟩
  · -- cost
    have hlen := length_withGuess w x
    have hpow := pow_half_le x.length
    rw [← hw] at hpow
    have hI := val_reverse_evens_lt w
    have hK := val_reverse_odds_lt w
    have hab : 2 ^ (w.length / 2) ≤ 2 ^ ((w.length + 1) / 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hl1 : (r1 1).length = (w.length + 1) / 2 := by
      rw [h11, List.length_reverse, (length_evens_odds w).1]
    have hl2 : (r2 2).length = w.length / 2 := by
      rw [h22, List.length_reverse, (length_evens_odds w).2]
    rw [hl1, hl2, hlen]
    have hKm : K * (x.length + guessI w + guessK w + 1) ≤ K * (5 * x.length + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    have hKm2 : K * (5 * x.length + 5) ≤ 10 * K * (2 * w.length + 1 + x.length + 1) := by
      nlinarith
    have hw1 : (w.length + 1) / 2 ≤ w.length + 1 := Nat.div_le_self _ _
    have hw2 : w.length / 2 ≤ w.length := Nat.div_le_self _ _
    linarith
  · -- verdict
    rw [hb0]
    congr 1
    apply Bool.eq_iff_iff.mpr
    rw [hbiff, verdict_eq_true]
    rfl

end P1Case1.CoTransV
