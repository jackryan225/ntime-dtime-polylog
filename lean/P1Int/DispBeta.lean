import P1ChkFinal.FamC13link
import P1SolCone.Wof
import P1Int.WitnessFit

/-!
# P1Int.DispBeta: the cone budget `βW` in the D14 form `BetaBound` (lane P1-lean-disp, family 12)

`famProg_of_task_beta` (the converter of C13link, FamConv.lean) needs `∀ p, βW p ≤ BetaBound a b cβ p.val`. For the
cone's budget `P1SolCone.βW Bt V a b cW` (Wof.lean:652) on the query domain of the branch,
`QDom (lpM2 (2^-j) a b) (λ n, lpK2 a b n - 4)`, this holds with one constant `cβ`:
* scan part: `cW (Λ+1)(|x|+|u|+|ρ|+1) ≤ 2 cW (steps+1)(p+1)(|x|+|u|+|ρ|)` (`phases_succ_le`; `|u| ≥ 1`);
* local part `2^(cW C M̄) (log₂(|x|+1)+|ρ|+1)^cW`: for long inputs `≤ m = |u|` by the PROVED D14 fit
  `P1P5.cone_local_fit` (`log₂(|x|+1)+|ρ|+1 ≤ 2λ+2`, `tupWidth ≤ A (B+1)`); for the finitely many short lengths it is a
  function of `|x|` only (`|ρ| = lpK2 - 4`), bounded by the finite sum `G`; so it is `≤ (G+1)|u|`.
-/

namespace P1Int

namespace P11

namespace Disp

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1ChkFinal P1ChkFinal.FamC13

theorem lpM2_pos' (s : ℝ) (a b n : ℕ) : 0 < lpM2 s a b n := by
  unfold lpM2
  apply Nat.mul_pos (by positivity)
  have h1 : 1 ≤ lpTime a b n := by unfold lpTime; omega
  have h2 : 0 < 2 ^ lpT2 s a b n := by positivity
  apply Nat.div_pos _ h2
  omega

theorem log_le_lpK2 (a b n : ℕ) : Nat.log 2 (n + 1) ≤ lpK2 a b n := by
  have h : n + 1 ≤ lpTime a b n := by unfold lpTime; omega
  calc Nat.log 2 (n + 1) ≤ Nat.log 2 (2 ^ lpK2 a b n) :=
        Nat.log_mono_right (le_trans h (Nat.le_pow_clog one_lt_two _))
    _ = lpK2 a b n := Nat.log_pow (by decide) _

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine) (a b : ℕ)

/-- The local part of the cone budget at input length `n` (with `|ρ| = lpK2 a b n - 4`). -/
def betaLocal (cW n : ℕ) : ℕ :=
  2 ^ (cW * Bt.growthConstant * P1SolCone.SolCone.Mbar Bt V a b n) *
    (Nat.log 2 (n + 1) + (lpK2 a b n - 4) + 1) ^ cW

/-- The local part is at most `(G + 1) m` for one constant `G` (long inputs: the D14 fit; short ones: a finite sum). -/
theorem betaLocal_le (cW : ℕ) :
    ∃ G : ℕ, ∀ n, betaLocal Bt V a b cW n ≤ (G + 1) * lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b n := by
  obtain ⟨t₀, ht₀⟩ := P1P5.cone_local_fit (portConsts Bt) Bt.growthConstant
    (Fintype.card (P1Net.Ext (toOAI V).K) * (Fintype.card (toOAI V).Γ + Fintype.card (toOAI V).Q +
      Fintype.card (toOAI V).K)) cW (portConsts_C2 Bt)
  refine ⟨∑ n ∈ Finset.range t₀, betaLocal Bt V a b cW n, fun n => ?_⟩
  have hm1 : 1 ≤ lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b n := lpM2_pos' _ a b n
  by_cases hn0 : t₀ ≤ n
  · haveI : NeZero (P1Wrap.Params.B (lpTime a b n)) := ⟨(P1Wrap.Params.B_pos _).ne'⟩
    have hW : P1Net.tupWidth (toOAI V) (P1Wrap.Params.B (lpTime a b n)) ≤
        Fintype.card (P1Net.Ext (toOAI V).K) * (Fintype.card (toOAI V).Γ + Fintype.card (toOAI V).Q +
          Fintype.card (toOAI V).K) * (P1Wrap.Params.B (lpTime a b n) + 1) :=
      le_trans (P1Net.tupWidth_le (toOAI V) (P1Wrap.Params.B (lpTime a b n))) (Nat.mul_le_mul_left _ (Nat.le_succ _))
    have htt : t₀ ≤ lpTime a b n := le_trans hn0 (by unfold lpTime; omega)
    have hfit := ht₀ (lpTime a b n) htt _ hW
    have hlog : Nat.log 2 (n + 1) + (lpK2 a b n - 4) + 1 ≤ 2 * P1Wrap.Params.lam (lpTime a b n) + 2 := by
      have h1 := log_le_lpK2 a b n
      have h2 : lpK2 a b n = P1Wrap.Params.lam (lpTime a b n) := rfl
      omega
    have hM : P1SolCone.SolCone.Mbar Bt V a b n = Bt.growthConstant ^ P1Wrap.Params.T (portConsts Bt) (lpTime a b n) *
        (P1Net.tupWidth (toOAI V) (P1Wrap.Params.B (lpTime a b n)) + 1) := rfl
    have hloc : betaLocal Bt V a b cW n = 2 ^ (cW * Bt.growthConstant *
        (Bt.growthConstant ^ P1Wrap.Params.T (portConsts Bt) (lpTime a b n) *
          (P1Net.tupWidth (toOAI V) (P1Wrap.Params.B (lpTime a b n)) + 1))) *
        (Nat.log 2 (n + 1) + (lpK2 a b n - 4) + 1) ^ cW := by
      unfold betaLocal
      rw [hM]
    rw [hloc]
    calc _ ≤ 2 ^ (cW * Bt.growthConstant *
          (Bt.growthConstant ^ P1Wrap.Params.T (portConsts Bt) (lpTime a b n) *
            (P1Net.tupWidth (toOAI V) (P1Wrap.Params.B (lpTime a b n)) + 1))) *
          (2 * P1Wrap.Params.lam (lpTime a b n) + 2) ^ cW := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog cW)
      _ ≤ P1Wrap.Params.m (portConsts Bt) (lpTime a b n) := hfit
      _ = lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b n := m_eq_lpM2 (portConsts Bt) a b n
      _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · have hmem : n ∈ Finset.range t₀ := Finset.mem_range.mpr (by omega)
    calc betaLocal Bt V a b cW n ≤ ∑ n ∈ Finset.range t₀, betaLocal Bt V a b cW n :=
          Finset.single_le_sum (f := betaLocal Bt V a b cW) (fun _ _ => Nat.zero_le _) hmem
      _ ≤ ∑ n ∈ Finset.range t₀, betaLocal Bt V a b cW n + 1 := Nat.le_succ _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hm1

/-- The cone budget written out at one query. -/
theorem betaW_eq (cW : ℕ) {M K : ℕ → ℕ} (x u ρ : List Bool)
    (h : (x, u, ρ).2.1.length = M (x, u, ρ).1.length ∧ (x, u, ρ).2.2.length = K (x, u, ρ).1.length) :
    P1SolCone.βW (M := M) (Kqry := K) Bt V a b cW ⟨(x, u, ρ), h⟩ =
      cW * (((S.steps + 1) * P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length) + 1) *
        (x.length + u.length + ρ.length + 1)) +
      2 ^ (cW * Bt.growthConstant * P1SolCone.SolCone.Mbar Bt V a b x.length) *
        (Nat.log 2 (x.length + 1) + ρ.length + 1) ^ cW := rfl

/-- **The cone budget is in the D14 form** `BetaBound` (family 12 of the dispatcher). -/
theorem betaW_bound (cW : ℕ) :
    ∃ cβ : ℕ, ∀ p : QDom (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b) (fun n => lpK2 a b n - 4),
      P1SolCone.βW Bt V a b cW p ≤ BetaBound a b cβ p.val := by
  obtain ⟨G, hG⟩ := betaLocal_le Bt V a b cW
  refine ⟨2 * cW * (S.steps + 1) + G + 1, ?_⟩
  rintro ⟨⟨x, u, ρ⟩, h⟩
  have hu : u.length = lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length := h.1
  have hρ : ρ.length = lpK2 a b x.length - 4 := h.2
  rw [betaW_eq]
  have hm1 : 1 ≤ u.length := by rw [hu]; exact lpM2_pos' _ a b x.length
  have hloc2 : 2 ^ (cW * Bt.growthConstant * P1SolCone.SolCone.Mbar Bt V a b x.length) *
      (Nat.log 2 (x.length + 1) + ρ.length + 1) ^ cW = betaLocal Bt V a b cW x.length := by
    rw [hρ]
    rfl
  have hloc : betaLocal Bt V a b cW x.length ≤ (G + 1) * u.length := by rw [hu]; exact hG x.length
  have hΛ := P1P5.phases_succ_le (portConsts Bt) S.steps (lpTime a b x.length)
  have hP : P1Wrap.Params.p (lpTime a b x.length) = lpP2 a b x.length := rfl
  rw [hP] at hΛ
  have hsum : x.length + u.length + ρ.length + 1 ≤ 2 * (x.length + u.length + ρ.length) := by omega
  have hscan : cW * (((S.steps + 1) * P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length) + 1) *
      (x.length + u.length + ρ.length + 1)) ≤
      2 * cW * (S.steps + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) := by
    calc cW * (((S.steps + 1) * P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length) + 1) *
          (x.length + u.length + ρ.length + 1))
        ≤ cW * (((S.steps + 1) * (lpP2 a b x.length + 1)) * (2 * (x.length + u.length + ρ.length))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hΛ hsum)
      _ = 2 * cW * (S.steps + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) := by ring
  have hlocal' : (G + 1) * u.length ≤ (G + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) := by
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc u.length ≤ x.length + u.length + ρ.length := by omega
      _ ≤ (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  rw [hloc2]
  show _ ≤ (2 * cW * (S.steps + 1) + G + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) +
      (Nat.log 2 (x.length + 1) + ρ.length + 1) ^ (2 * cW * (S.steps + 1) + G + 1)
  calc _ ≤ 2 * cW * (S.steps + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) +
        (G + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) :=
          Nat.add_le_add hscan (le_trans hloc hlocal')
    _ = (2 * cW * (S.steps + 1) + G + 1) * (lpP2 a b x.length + 1) * (x.length + u.length + ρ.length) := by ring
    _ ≤ _ := Nat.le_add_right _ _

end

end Disp

end P11

end P1Int

#print axioms P1Int.P11.Disp.betaLocal_le
#print axioms P1Int.P11.Disp.betaW_bound
