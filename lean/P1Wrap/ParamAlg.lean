import P1Wrap.W3Arith
import Mathlib.Data.Nat.Size

/-!
# Bit-level algorithm for the parameters of Lemma P (target for the Prog implementations of W3)

The machines of W3 (`InnerImpl`, `OuterImpl`) must compute `m(n)`, `padLen(n)` and `k(n)` from `n`. This file
gives the parameters in terms of bit length (`Nat.size`, the number of binary digits) and right shifts, so that a
program only needs: binary counter, add, multiply, bit length, shift right.

* `clog_two_eq_size : Nat.clog 2 t = Nat.size (t - 1)`
* `log_two_eq_size : Nat.log 2 x = Nat.size x - 1`
* `lpM2_alg`: with `t = (b + 2a)(n² + 1) + n + 1`, `λ = size (t - 1)`, `p = size λ - 1`, `T = p >>> j`:
  `m = (p + 1)^6 * ((t + 2^T - 1) >>> T)`; `k = λ`; `padLen = (p + 1) m`.
-/

namespace P1Wrap.W3

open P1Int

theorem clog_two_eq_size (t : ℕ) : Nat.clog 2 t = Nat.size (t - 1) := by
  have key : ∀ y, Nat.clog 2 t ≤ y ↔ Nat.size (t - 1) ≤ y := by
    intro y
    rw [Nat.clog_le_iff_le_pow one_lt_two, Nat.size_le]
    have : 0 < 2 ^ y := by positivity
    omega
  exact le_antisymm ((key (Nat.size (t - 1))).2 le_rfl) ((key (Nat.clog 2 t)).1 le_rfl)

theorem log_two_eq_size (x : ℕ) : Nat.log 2 x = Nat.size x - 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hs : 0 < Nat.size x := Nat.size_pos.2 hx
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact Nat.lt_size.1 (by omega)
    · rw [show Nat.size x - 1 + 1 = Nat.size x by omega]
      exact Nat.lt_size_self x

theorem lpTime_eq (a b n : ℕ) : lpTime a b n = (b + 2 * a) * (n ^ 2 + 1) + n + 1 := by
  unfold lpTime; ring

/-- The parameters of Lemma P by bit length and shifts. -/
theorem lpM2_alg (j a b n : ℕ) :
    let t := (b + 2 * a) * (n ^ 2 + 1) + n + 1
    let lam := Nat.size (t - 1)
    let p := Nat.size lam - 1
    let T := p >>> j
    lpLam2 a b n = lam ∧ lpP2 a b n = p ∧ lpT2 (sOf j) a b n = T ∧
      lpM2 (sOf j) a b n = (p + 1) ^ 6 * ((t + 2 ^ T - 1) >>> T) ∧
      lpK2 a b n = lam ∧ padLen j a b n = (p + 1) * ((p + 1) ^ 6 * ((t + 2 ^ T - 1) >>> T)) := by
  intro t lam p T
  have h1 : lpLam2 a b n = lam := by
    unfold lpLam2; rw [lpTime_eq, clog_two_eq_size]
  have h2 : lpP2 a b n = p := by
    unfold lpP2; rw [h1, log_two_eq_size]
  have h3 : lpT2 (sOf j) a b n = T := by
    rw [lpT2_sOf, h2]
    show p / 2 ^ j = p >>> j
    rw [Nat.shiftRight_eq_div_pow]
  have h4 : lpM2 (sOf j) a b n = (p + 1) ^ 6 * ((t + 2 ^ T - 1) >>> T) := by
    unfold lpM2; rw [h3, h2, lpTime_eq]
    show _ = (p + 1) ^ 6 * ((t + 2 ^ T - 1) >>> T)
    rw [Nat.shiftRight_eq_div_pow]
  refine ⟨h1, h2, h3, h4, h1, ?_⟩
  unfold padLen; rw [h2, h4]

end P1Wrap.W3
