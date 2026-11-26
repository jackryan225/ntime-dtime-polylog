import P1Int.D5AsmDefs
import P1Int.FormAg
import P1Int.WitnessFit
import P1ChkFinal.Wired
import P1ChkFinal.C7RFam
import P1SolFmt.GreedyCnt

/-!
# P1Int.DispCnt: the index counts of the 16 families and their fit (lane P1-lean-disp, item p11_cntfit)

`dispCnt n c`: the index count of family `c` at input length `n`, exactly the counts of integ's `DispIn`
(FinalInputs.lean; `cnt x.length c = ...` by `rfl`; family 15 and beyond: `0`).
`dispCnt_fit`: for long inputs every count of a family `c < 15` is at most `2 ^ (lpK2 a b n - 4)`, the number of index
words. It is FALSE for short inputs (P1-sol-scoutgrp, SmallSelector.lean: `|x| = 0`, `a = 0`, `b = 15`; numeric model of
the lane, board 14:39Z: false up to about `p = 32`), so the threshold `n₀` is part of the statement.
Route: the greedy counts (families 4-9) by `P1SolGreedyCnt.greedyCount` (T5); `finN ≤ maxBases ≤ cntBase`; every other
count is at most `C (I N) (p + 1)^2` (`locCount ≤ locCoeff (h + 1)`, `finP ≤ initialPositions`, `nGB ≤ I`), and
`C (I N) (p + 1)^2 ≤ 2 ^ (λ - 4)` for large `t` (`budget_eventually`: the proof of the private
`P1SolGreedyCnt.Sol.eventually_index_budget`, ChkFinal/P1SolFmt/GreedyCnt.lean, copied).
-/

namespace P1Int

namespace P11

namespace Disp

open Filter P1Wrap P1Wit P1Wit.SolSpace
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- The interval-width radix eventually absorbs a constant times `(p + 1)^2` (copy of the proof of the private
`P1SolGreedyCnt.Sol.eventually_index_budget`). -/
theorem budget_eventually (c : ℕ) :
    ∀ᶠ t in atTop, 0 < Params.I 1 t ∧
      c * (Params.I 1 t * Params.N t) * (Params.p t + 1) ^ 2 ≤ 2 ^ (Params.lam t - 4) := by
  have hhalf : Tendsto (fun q : ℕ => q / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro q
    exact ⟨q * 2, fun _ h => (Nat.le_div_iff_mul_le (by decide)).mpr h⟩
  have hpoly := (hhalf.comp Params.tendsto_p).eventually (Params.eventually_mul_pow_lt_two_pow (1024 * c) 2)
  filter_upwards [hpoly, Params.eventually_of_p (eventually_ge_atTop 2),
    Params.eventually_of_lam (eventually_ge_atTop 4), Params.eventually_Ib 1 le_rfl,
    eventually_ge_atTop 2] with t htPoly htP htLam htI ht
  have hI : 0 < Params.I 1 t := by
    have hlo := htI.1
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, Nat.zero_mul, Nat.one_mul] at hlo
    omega
  refine ⟨hI, Nat.le_of_mul_le_mul_right ?_ (Params.B_pos t)⟩
  have hP : Params.p t + 1 ≤ 4 * (Params.p t / 2) := by omega
  have hB : 64 * c * (Params.p t + 1) ^ 2 ≤ Params.B t := by
    calc
      _ ≤ 64 * c * (4 * (Params.p t / 2)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2)
      _ = (1024 * c) * (Params.p t / 2) ^ 2 := by ring
      _ ≤ Params.B t := htPoly.le
  have hpow : (2 : ℕ) ^ Params.lam t = 16 * 2 ^ (Params.lam t - 4) := by
    calc
      _ = 2 ^ (4 + (Params.lam t - 4)) := congrArg (fun j : ℕ => (2 : ℕ) ^ j) (by omega)
      _ = _ := pow_add 2 4 _
  have hceil : Params.I 1 t * Params.bb t ≤ 4 * 2 ^ Params.lam t :=
    (by simpa only [Nat.mul_one] using htI.2 : _ ≤ 4 * t).trans
      (Nat.mul_le_mul_left _ (Params.t_le_two_pow_lam t))
  calc
    _ = (Params.I 1 t * Params.bb t) * (c * (Params.p t + 1) ^ 2) := by unfold Params.bb; ring
    _ ≤ (4 * 2 ^ Params.lam t) * (c * (Params.p t + 1) ^ 2) := Nat.mul_le_mul_right _ hceil
    _ = 2 ^ (Params.lam t - 4) * (64 * c * (Params.p t + 1) ^ 2) := by rw [hpow]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hB

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
  (a b d bigBias termBias : ℕ)

/-- **The index counts of the 16 families** at input length `n` (the counts of `DispIn`; family 15 and beyond: `0`). -/
def dispCnt (n c : ℕ) : ℕ :=
  match c with
  | 0 => (gdims Bt V a b d bigBias termBias n).I * (gdims Bt V a b d bigBias termBias n).N *
      (gdims Bt V a b d bigBias termBias n).r
  | 1 => (gdims Bt V a b d bigBias termBias n).I * (gdims Bt V a b d bigBias termBias n).r
  | 2 => (gdims Bt V a b d bigBias termBias n).I * (gdims Bt V a b d bigBias termBias n).r * 3 * 2
  | 3 => P1ChkDir.cnt4 (toOAI V).K (c4dims Bt V a b d bigBias termBias) n
  | 4 => P1ChkGreedy.cntBase (gdims Bt V a b d bigBias termBias n)
  | 5 => P1ChkGreedy.cntBase (gdims Bt V a b d bigBias termBias n)
  | 6 => P1ChkFinal.C7R.cnt7all (gdims Bt V a b d bigBias termBias n)
      (genuineAg (gdims Bt V a b d bigBias termBias) n)
  | 7 => P1ChkGreedy.cntBase (gdims Bt V a b d bigBias termBias n)
  | 8 => P1ChkGreedy.cntLev (gdims Bt V a b d bigBias termBias n)
  | 9 => P1ChkGreedy.cntBase (gdims Bt V a b d bigBias termBias n)
  | 10 => P1ChkFinal.cnt11 (gdims Bt V a b d bigBias termBias) n
  | 11 => P1ChkFinal.cnt12 (gdims Bt V a b d bigBias termBias) n
  | 12 => P1ChkFinal.cnt13link (gdims Bt V a b d bigBias termBias) n
  | 13 => P1ChkFinal.cnt13ends (gdims Bt V a b d bigBias termBias) n
  | 14 => (gdims Bt V a b d bigBias termBias n).nGB
  | _ => 0

/-- `finN ≤ cntBase`: the bases of the top level are at most the largest number of bases. -/
theorem finN_le_cntBase (D : P1Wit.Dims) : P1ChkFinal.finN D ≤ P1ChkGreedy.cntBase D :=
  (P1ChkGreedy.bases_le_maxBases D (le_refl D.top)).trans
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))

/-- The constant of the non-greedy counts. -/
def cntCoeff : ℕ := 6 * Fintype.card (toOAI V).K + 20 * locCoeff (toOAI V) + 2

/-- **The non-greedy counts** are at most `cntCoeff (I N) (p + 1)^2` (once `0 < I`). -/
theorem counts_le (n : ℕ) (hI : 0 < Params.I 1 (lpTime a b n)) :
    ∀ c, (c ≤ 3 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14) →
      dispCnt Bt V a b d bigBias termBias n c ≤
        cntCoeff V * (Params.I 1 (lpTime a b n) * Params.N (lpTime a b n)) * (Params.p (lpTime a b n) + 1) ^ 2 := by
  intro c hc
  set t := lpTime a b n with ht
  set I := Params.I 1 t
  set N := Params.N t
  set P := Params.p t
  set r := Fintype.card (toOAI V).K
  set L := locCoeff (toOAI V)
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hP2 : 1 ≤ (P + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hIN : I ≤ I * N := Nat.le_mul_of_pos_right _ hN
  have hsq (X : ℕ) : X ≤ X * (P + 1) ^ 2 := Nat.le_mul_of_pos_right _ hP2
  have hP1 : P + 1 ≤ (P + 1) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hloc : P1Net.locCount (toOAI V).K (Params.h t) ≤ 10 * L * (P + 1) := by
    calc P1Net.locCount (toOAI V).K (Params.h t) ≤ L * (Params.h t + 1) := P1Net.locCount_le
      _ ≤ L * (10 * (P + 1)) := Nat.mul_le_mul_left _ (h_succ_le t)
      _ = 10 * L * (P + 1) := by ring
  -- `2 * (I * locCount) * N ≤ 20 L (I N) (p+1)^2`
  have hpos : 2 * (I * P1Net.locCount (toOAI V).K (Params.h t)) * N ≤ 20 * L * (I * N) * (P + 1) ^ 2 := by
    calc 2 * (I * P1Net.locCount (toOAI V).K (Params.h t)) * N ≤ 2 * (I * (10 * L * (P + 1))) * N :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hloc))
      _ = 20 * L * (I * N) * (P + 1) := by ring
      _ ≤ 20 * L * (I * N) * (P + 1) ^ 2 := Nat.mul_le_mul_left _ hP1
  have hC : ∀ e, e ≤ cntCoeff V → e * (I * N) * (P + 1) ^ 2 ≤ cntCoeff V * (I * N) * (P + 1) ^ 2 :=
    fun e he => Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ he)
  have hcr : r ≤ cntCoeff V := by unfold cntCoeff; omega
  have hc6 : 6 * r ≤ cntCoeff V := by unfold cntCoeff; omega
  have hcL : 20 * L ≤ cntCoeff V := by unfold cntCoeff; omega
  have hc2 : 2 ≤ cntCoeff V := by unfold cntCoeff; omega
  have hone : 1 ≤ I * N * (P + 1) ^ 2 :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hI)) (le_trans hIN (hsq _))
  rcases hc with hc | hc | hc | hc | hc
  · interval_cases c
    · -- c = 0: I N r
      show I * N * r ≤ _
      refine le_trans ?_ (hC r hcr)
      calc I * N * r = r * (I * N) := by ring
        _ ≤ r * (I * N) * (P + 1) ^ 2 := hsq _
    · -- c = 1: I r
      show I * r ≤ _
      refine le_trans ?_ (hC r hcr)
      calc I * r = r * I := by ring
        _ ≤ r * (I * N) := Nat.mul_le_mul_left _ hIN
        _ ≤ r * (I * N) * (P + 1) ^ 2 := hsq _
    · -- c = 2: I r 3 2
      show I * r * 3 * 2 ≤ _
      refine le_trans ?_ (hC (6 * r) hc6)
      calc I * r * 3 * 2 = 6 * r * I := by ring
        _ ≤ 6 * r * (I * N) := Nat.mul_le_mul_left _ hIN
        _ ≤ 6 * r * (I * N) * (P + 1) ^ 2 := hsq _
    · -- c = 3: cnt4 = 2 (I locCount)
      show 2 * (I * P1Net.locCount (toOAI V).K (Params.h t)) ≤ _
      refine le_trans ?_ (le_trans hpos (hC (20 * L) hcL))
      exact Nat.le_mul_of_pos_right _ hN
  · -- c = 11: cnt12 = 1
    subst hc
    show 1 ≤ _
    refine le_trans hone (le_trans ?_ (hC 2 hc2))
    calc I * N * (P + 1) ^ 2 ≤ 2 * (I * N * (P + 1) ^ 2) := Nat.le_mul_of_pos_left _ (by decide)
      _ = 2 * (I * N) * (P + 1) ^ 2 := by ring
  · -- c = 12: finP = chainLen - 1 ≤ initialPositions
    subst hc
    show (initialPositions (toOAI V) 1 t / S.positionFactor ^ Params.T (portConsts Bt) t + 1) - 1 ≤ _
    rw [Nat.add_sub_cancel]
    refine le_trans (Nat.div_le_self _ _) (le_trans ?_ (le_trans hpos (hC (20 * L) hcL)))
    exact le_refl _
  · -- c = 13: cnt13ends = 2
    subst hc
    show 2 ≤ _
    refine le_trans ?_ (hC 2 hc2)
    calc 2 = 2 * 1 := rfl
      _ ≤ 2 * (I * N * (P + 1) ^ 2) := Nat.mul_le_mul_left _ hone
      _ = 2 * (I * N) * (P + 1) ^ 2 := by ring
  · -- c = 14: nGB ≤ I
    subst hc
    show guessBlocks (a * (n ^ 2 + 1)) (Params.bb t) ≤ _
    have hg : 2 * (a * (n ^ 2 + 1)) ≤ t := by rw [ht]; unfold lpTime; omega
    refine le_trans (guessBlocks_le 1 le_rfl hg) (le_trans ?_ (hC 2 hc2))
    calc I ≤ I * N * (P + 1) ^ 2 := le_trans hIN (hsq _)
      _ ≤ 2 * (I * N * (P + 1) ^ 2) := Nat.le_mul_of_pos_left _ (by decide)
      _ = 2 * (I * N) * (P + 1) ^ 2 := by ring

/-- **Item p11_cntfit: the counts fit into the index words for long inputs** (at the real parameters). -/
theorem dispCnt_fit (hb : 1 ≤ b) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ c < 15, dispCnt Bt V a b d bigBias termBias n c ≤ 2 ^ (lpK2 a b n - 4) := by
  obtain ⟨n₁, hg⟩ := P1SolGreedyCnt.greedyCount.{0} Bt V a b d bigBias termBias hb
  have he := (tendsto_lpTime a b).eventually (budget_eventually (cntCoeff V))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp he
  refine ⟨max n₁ n₂, fun n hn c hc => ?_⟩
  obtain ⟨hI, hbud⟩ := hn₂ n (le_of_max_le_right hn)
  obtain ⟨hB, hL, h7⟩ := hg n (le_of_max_le_left hn)
  have hbud' : cntCoeff V * (Params.I 1 (lpTime a b n) * Params.N (lpTime a b n)) *
      (Params.p (lpTime a b n) + 1) ^ 2 ≤ 2 ^ (lpK2 a b n - 4) := hbud
  have hcl := fun c hc => le_trans (counts_le Bt V a b d bigBias termBias n hI c hc) hbud'
  interval_cases c
  · exact hcl 0 (by omega)
  · exact hcl 1 (by omega)
  · exact hcl 2 (by omega)
  · exact hcl 3 (by omega)
  · exact hB
  · exact hB
  · exact h7
  · exact hB
  · exact hL
  · exact hB
  · exact le_trans (finN_le_cntBase _) hB
  · exact hcl 11 (by omega)
  · exact hcl 12 (by omega)
  · exact hcl 13 (by omega)
  · exact hcl 14 (by omega)

/-- The counts are DispIn's counts (`rfl`), checked for families 0, 3, 6, 10, 14. -/
example (x : List Bool) :
    dispCnt Bt V a b d bigBias termBias x.length 0 = (fixedDims Bt V a b x d bigBias termBias).I *
      (fixedDims Bt V a b x d bigBias termBias).N * (fixedDims Bt V a b x d bigBias termBias).r ∧
    dispCnt Bt V a b d bigBias termBias x.length 3 =
      P1ChkDir.cnt4 (toOAI V).K (c4dims Bt V a b d bigBias termBias) x.length ∧
    dispCnt Bt V a b d bigBias termBias x.length 6 = P1ChkFinal.C7R.cnt7all (fixedDims Bt V a b x d bigBias termBias)
      (genuineAg (gdims Bt V a b d bigBias termBias) x.length) ∧
    dispCnt Bt V a b d bigBias termBias x.length 10 = P1ChkFinal.cnt11 (gdims Bt V a b d bigBias termBias) x.length ∧
    dispCnt Bt V a b d bigBias termBias x.length 14 = (fixedDims Bt V a b x d bigBias termBias).nGB :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end Disp

end P11

end P1Int

#print axioms P1Int.P11.Disp.budget_eventually
#print axioms P1Int.P11.Disp.counts_le
#print axioms P1Int.P11.Disp.dispCnt_fit
