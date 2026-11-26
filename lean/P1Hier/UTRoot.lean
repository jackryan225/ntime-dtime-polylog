import P1Hier.UTLog

/-!
# P1Hier.UTRoot (copy B of lane hier): `rootLog q` on unary numbers in linear time

`easy_rootLog : Easy (fun n : ℕ => rootLog q n)`.

Method: `L = log₂ n` in linear time (`easy_log2`); then the search `r ↦ r + 1` while
`r ^ Q < L + 1` (`Q = max q 1`), iterated `L + 2` times from `r = 0` (OpenAI's `Poly.rider`).
This costs a polynomial in `L`, and `(L + 1) ^ k ≤ k! 2^k (n + 1)` (`polylog_le`), so the whole
computation is linear in `n`.
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

theorem easy_succ : Easy (fun n : ℕ => n + 1) :=
  easy_congr (((Easy.const ()).pair easy_tally).compose Easy.cons) (fun _ => rfl)

/-- Unary multiplication is polynomial. -/
theorem poly_mul : Poly (fun i : ℕ × ℕ => i.1 * i.2) := by
  have h1 : Easy (fun i : ℕ × ℕ => (tally i.1, tally i.2)) :=
    ((Easy.fst (X := ℕ) (Y := ℕ)).compose easy_tally).pair
      ((Easy.snd (X := ℕ) (Y := ℕ)).compose easy_tally)
  have c1 := Computes.comp (generate (X := Tally)) h1
  have c2 := Computes.comp (Easy.flatten (X := Unit)) c1
  refine Poly.of_bound (c2.conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)) ⟨2, 20, fun i => ?_⟩
  · show send ((List.replicate (tally i.1).length (tally i.2)).flatten) = send (tally (i.1 * i.2))
    simp only [tally, List.length_replicate, List.flatten_replicate_replicate]
  · show size i + ((tally i.1).length + 1) * size (tally i.2) +
        size (List.replicate (tally i.1).length (tally i.2)) ≤ 20 * (size i + 1) ^ 2
    simp only [size_replicate, size_tally, tally_length, size_prod, size_nat']
    nlinarith [Nat.zero_le i.1, Nat.zero_le i.2]

/-- Unary powers are polynomial. -/
theorem poly_pow : ∀ Q : ℕ, Poly (fun r : ℕ => r ^ Q)
  | 0 => by
    have e : (fun r : ℕ => r ^ 0) = (fun _ : ℕ => (1 : ℕ)) := funext fun r => pow_zero r
    rw [e]
    exact Code.Poly.const 1
  | Q + 1 => by
    have h : Poly (fun r : ℕ => r ^ Q * r) := ((poly_pow Q).pair Poly.identity).compose poly_mul
    have e : (fun r : ℕ => r ^ (Q + 1)) = (fun r : ℕ => r ^ Q * r) := funext fun r => pow_succ r Q
    rw [e]
    exact h

/-- One step of the search. -/
def rstep (Q : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  bif decide (s.1 + 1 ≤ s.2 ^ Q) then s else (s.1, s.2 + 1)

theorem poly_rstep (Q : ℕ) : Poly (rstep Q) := by
  have hv : Poly (fun s : ℕ × ℕ => decide (s.1 + 1 ≤ s.2 ^ Q)) :=
    ((((Easy.fst (X := ℕ) (Y := ℕ)).compose easy_succ).poly).pair
      ((Easy.snd (X := ℕ) (Y := ℕ)).poly.compose (poly_pow Q))).compose easy_le.poly
  have hg : Poly (fun s : ℕ × ℕ => (s.1, s.2 + 1)) :=
    ((Easy.fst (X := ℕ) (Y := ℕ)).pair ((Easy.snd (X := ℕ) (Y := ℕ)).compose easy_succ)).poly
  exact Poly.choose hv Poly.identity hg

theorem size_rstep (Q : ℕ) (s : ℕ × ℕ) : size (rstep Q s) ≤ size s + 2 := by
  unfold rstep
  cases decide (s.1 + 1 ≤ s.2 ^ Q)
  · simp only [Bool.cond_false, size_prod, size_nat']
    omega
  · simp only [Bool.cond_true]
    omega

theorem iter_rstep (Q L : ℕ) (h : ∃ r, L + 1 ≤ r ^ Q) :
    ∀ i, (rstep Q)^[i] (L, 0) = (L, min i (Nat.find h))
  | 0 => by simp
  | i + 1 => by
    rw [Function.iterate_succ_apply', iter_rstep Q L h i]
    by_cases hi : i < Nat.find h
    · have h1 : ¬ (L + 1 ≤ i ^ Q) := Nat.find_min h hi
      rw [Nat.min_eq_left hi.le, Nat.min_eq_left (by omega : i + 1 ≤ Nat.find h)]
      simp [rstep, h1]
    · have h1 : L + 1 ≤ (Nat.find h) ^ Q := Nat.find_spec h
      rw [Nat.min_eq_right (by omega : Nat.find h ≤ i),
        Nat.min_eq_right (by omega : Nat.find h ≤ i + 1)]
      simp [rstep, h1]

theorem ride_rootLog (q n : ℕ) :
    ride (rstep (max q 1)) (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0)) =
      (Nat.log 2 n, rootLog q n) := by
  rw [ride_t, tally_length, iter_rstep (max q 1) (Nat.log 2 n) (exists_rootLog q n)]
  have hle : Nat.find (exists_rootLog q n) ≤ Nat.log 2 n + 1 :=
    Nat.find_min' _ (Nat.le_self_pow (by omega) _)
  show (Nat.log 2 n, min (Nat.log 2 n + 2) (Nat.find (exists_rootLog q n))) =
    (Nat.log 2 n, Nat.find (exists_rootLog q n))
  rw [Nat.min_eq_right (by omega)]

/-- Polylogarithmic against linear. -/
theorem polylog_le (k n : ℕ) : (Nat.log 2 n + 1) ^ k ≤ (k.factorial * 2 ^ k) * (n + 1) := by
  have h1 := Nat.pow_succ_le_ascFactorial (Nat.log 2 n + 1) k
  have h2 := Nat.ascFactorial_eq_factorial_mul_choose (Nat.log 2 n) k
  have h3 := Nat.choose_le_two_pow (Nat.log 2 n + k) k
  have h4 := pow_log_le_succ n
  calc (Nat.log 2 n + 1) ^ k ≤ k.factorial * (Nat.log 2 n + k).choose k := h1.trans h2.le
    _ ≤ k.factorial * 2 ^ (Nat.log 2 n + k) := Nat.mul_le_mul_left _ h3
    _ = (k.factorial * 2 ^ k) * 2 ^ Nat.log 2 n := by rw [pow_add]; ring
    _ ≤ (k.factorial * 2 ^ k) * (n + 1) := Nat.mul_le_mul_left _ h4

/-- **`rootLog q` on unary numbers** in linear time. -/
theorem easy_rootLog (q : ℕ) : Easy (fun n : ℕ => rootLog q n) := by
  have hA : Easy (fun n : ℕ => (tally (Nat.log 2 n + 2), (Nat.log 2 n, (0 : ℕ)))) := by
    have h2 : Easy (fun m : ℕ => (tally (m + 2), (m, (0 : ℕ)))) :=
      (((Easy.const ()).pair (((Easy.const ()).pair easy_tally).compose Easy.cons)).compose
        Easy.cons).pair (easy_id.pair (Easy.const 0))
    exact easy_log2.compose h2
  obtain ⟨t, ⟨k, C, ht⟩, hc⟩ := Poly.rider (rstep (max q 1)) (poly_rstep _) 2 (size_rstep _)
  have hB := Computes.comp (Easy.snd (X := ℕ) (Y := ℕ)) (Computes.comp hc hA)
  refine Easy.of_bound (hB.conform (fun _ => rfl) (fun _ => rfl) (fun n => ?_))
    (6 + C * (k.factorial * 2 ^ k) * 10 ^ k) (fun n => ?_)
  · show send (ride (rstep (max q 1)) (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0))).2 =
      send (rootLog q n)
    rw [ride_rootLog]
  · have hρ := rootLog_le q n
    have hL : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    have hP := polylog_le k n
    have hT := ht (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0))
    have hs : size ((tally (Nat.log 2 n + 2), (Nat.log 2 n, (0 : ℕ))) : Tally × ℕ × ℕ) + 1 =
        4 * Nat.log 2 n + 10 := by
      simp only [size_prod, size_tally, tally_length, size_nat']
      omega
    rw [hs] at hT
    have h10 : (4 * Nat.log 2 n + 10) ^ k ≤ 10 ^ k * (Nat.log 2 n + 1) ^ k := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by omega) k
    show size n + t (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0)) +
        size (ride (rstep (max q 1)) (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0))) ≤
      (6 + C * (k.factorial * 2 ^ k) * 10 ^ k) * size n
    rw [ride_rootLog, size_prod, size_nat', size_nat', size_nat']
    have hmain : t (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0)) ≤
        C * (k.factorial * 2 ^ k) * 10 ^ k * (2 * n + 1) := by
      calc t (tally (Nat.log 2 n + 2), (Nat.log 2 n, 0))
          ≤ C * (4 * Nat.log 2 n + 10) ^ k := hT
        _ ≤ C * (10 ^ k * (Nat.log 2 n + 1) ^ k) := Nat.mul_le_mul_left _ h10
        _ ≤ C * (10 ^ k * ((k.factorial * 2 ^ k) * (n + 1))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hP)
        _ = C * (k.factorial * 2 ^ k) * 10 ^ k * (n + 1) := by ring
        _ ≤ C * (k.factorial * 2 ^ k) * 10 ^ k * (2 * n + 1) := Nat.mul_le_mul_left _ (by omega)
    have e : (6 + C * (k.factorial * 2 ^ k) * 10 ^ k) * (2 * n + 1) =
        6 * (2 * n + 1) + C * (k.factorial * 2 ^ k) * 10 ^ k * (2 * n + 1) := by ring
    rw [e]
    omega

end P1Hier.UM
