import P1Int.LemmaP
import P1Wrap.Params
import P1P7.SolFit

/-!
# P1, decision D14 (G3-chief 12:13Z): the scan part of the cone budget fits the branch budget

The cone program (Sol P1-sol-cone, `WHyp` of C13link) gets the budget
`βW = c ((Λ + 1)(|u| + |x| + |ρ|)) + 2^{O(C M̄)} poly(log t)`, `Λ` = number of compression phases. The witness
layout of P6 has `Λ = top = (S.steps + 1) · T` levels after level 0 (`P1Wit.genuineDims`, `runPhases_length`), with
`T = Params.T K t = p / 2^j`. Here:
* `phases_succ_le`: `(steps + 1) T + 1 ≤ (steps + 1)(p + 1)`;
* `params_p_lpTime`: the `p` of `P1Wrap.Params` at the time `lpTime a b n` of Lemma P is `lpP2 a b n` (by `rfl`);
* `cone_scan_fit`: the scan part `c (Λ + 1)(|x| + |u| + |ρ| + 1)` is at most the branch budget
  `lpCost2 (4 c (steps + 1)) s a b n = 4 c (steps + 1) · m · (p + 1)`, given `n ≤ m`, `k ≤ m` (both hold for
  `s ≤ 1`, `1 ≤ b`, `16 ≤ n`: `P1Dispatch.SolBudget.input_le_witness`, BudgetBounds.lean:53) and `|u| = m`, `|ρ| ≤ k`.
The local part `2^{O(C M̄)} poly(log t)` is a separate item (it needs the final form of `βW` of the cone prover).
-/

namespace P1P5

open P1Int

/-- The `p` of `P1Wrap.Params` at the Lemma P time bound is `lpP2`. -/
theorem params_p_lpTime (a b n : ℕ) : P1Wrap.Params.p (lpTime a b n) = lpP2 a b n := rfl

/-- `Λ + 1 ≤ (steps + 1)(p + 1)` for `Λ = (steps + 1) T`, `T = p / 2^j`. -/
theorem phases_succ_le (K : P1Wrap.Consts) (steps t : ℕ) :
    (steps + 1) * P1Wrap.Params.T K t + 1 ≤ (steps + 1) * (P1Wrap.Params.p t + 1) := by
  have hT : P1Wrap.Params.T K t ≤ P1Wrap.Params.p t := Nat.div_le_self _ _
  have h := Nat.mul_le_mul_left (steps + 1) hT
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **D14 fit, scan part.** -/
theorem cone_scan_fit (K : P1Wrap.Consts) (steps : ℕ) (s : ℝ) (a b n c : ℕ) (hn : 1 ≤ n)
    (hnM : n ≤ lpM2 s a b n) (hkM : lpK2 a b n ≤ lpM2 s a b n)
    (x u ρ : List Bool) (hx : x.length = n) (hu : u.length = lpM2 s a b n) (hρ : ρ.length ≤ lpK2 a b n) :
    c * (((steps + 1) * P1Wrap.Params.T K (lpTime a b n) + 1) * (x.length + u.length + ρ.length + 1)) ≤
      lpCost2 (4 * c * (steps + 1)) s a b n := by
  have hΛ := phases_succ_le K steps (lpTime a b n)
  rw [params_p_lpTime] at hΛ
  have hlen : x.length + u.length + ρ.length + 1 ≤ 4 * lpM2 s a b n := by omega
  have h := Nat.mul_le_mul hΛ hlen
  rw [lpCost2]
  calc
    _ ≤ c * ((steps + 1) * (lpP2 a b n + 1) * (4 * lpM2 s a b n)) := Nat.mul_le_mul_left c h
    _ = 4 * c * (steps + 1) * lpM2 s a b n * (lpP2 a b n + 1) := by ring

/-! ## D14 fit, LOCAL part

The local part of the cone budget (P1-sol-cone `βW`, `Mbar = C^T (tupWidth (toOAI V) (B t) + 1)`) is
`2^(c C Mbar) (log2 (n+1) + |ρ| + 1)^c`. With `tupWidth V B = card (Ext K) (B |Γ| + |Q| + |K| B)`, so `W ≤ A (B t + 1)`
for a constant `A`, and `log2 (n+1) + |ρ| + 1 ≤ 2 λ + 2` (`n < t`, `|ρ| ≤ lpK2 = λ`), it suffices that, for large `t`,
`2^(c C C^T (W + 1)) (2 λ + 2)^c ≤ m K t`. True because `C^T ≤ C2^T ≤ λ^(1/64)` and `B ≤ λ^(1/2)` (so the exponent is
`O(λ^(33/64))`) while `m ≥ t / 2^T ≥ 2^(λ - 1) / λ` (P1Wrap.Params: `C2_pow_T_pow_le`, `B_sq_le`, `B_C2_pow_le`,
`m_mul_two_pow_T_ge`, `two_pow_T_le`). Then `P1Int.m_eq_lpM2` (Interfaces/P1Int/WitnessFit.lean) turns `m K t` into
`lpM2 (2^(-j)) a b n` at `t = lpTime a b n`. -/

/-- **D14 fit, local part.** PROVED by Sol P1-sol-localfit (`P1P7.SolFit.cone_local_fit'`, file P7/P1P7/SolFit.lean =
the Sol file UNCHANGED, sha256 8b53cbf2..defe, runner DONE 12:36:34Z); this statement was compiled with `sorry` (eval-p5-2). -/
theorem cone_local_fit (K : P1Wrap.Consts) (C A c : ℕ) (hC : C ≤ K.C2) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ W : ℕ, W ≤ A * (P1Wrap.Params.B t + 1) →
      2 ^ (c * C * (C ^ P1Wrap.Params.T K t * (W + 1))) * (2 * P1Wrap.Params.lam t + 2) ^ c ≤
        P1Wrap.Params.m K t :=
  P1P7.SolFit.cone_local_fit' K C A c hC

end P1P5

#print axioms P1P5.phases_succ_le
#print axioms P1P5.cone_scan_fit
#print axioms P1P5.cone_local_fit
