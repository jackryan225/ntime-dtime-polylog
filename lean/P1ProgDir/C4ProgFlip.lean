import P1ProgDir.C4ProgRank

namespace P1ProgDir.SolC4

open P1Net NatCode
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP Compression

def stageNumber (m c : ℕ) : ℕ := (bif ltb c m then m - 1 - c else c + 1 - m) % m

@[fun_prop] theorem poly_stageNumber : Poly (fun p : ℕ × ℕ => stageNumber p.1 p.2) := by
  unfold stageNumber
  fun_prop

theorem stageNumber_eq (m : ℕ) [NeZero m] (c : ℕ) :
    stageNumber m c = (Routing.stageBit m c).val := by
  by_cases h : c < m
  · simp only [stageNumber, Routing.stageBit, ltb_iff.mpr h, Bool.cond_true, ite_eq_left h]
  · simp only [stageNumber, Routing.stageBit, ltb_false_iff.mpr (Nat.le_of_not_lt h),
      Bool.cond_false, ite_eq_right h]

/-- The numerical coding of a lane unit follows the big-endian convention of
bitWordFinEquiv, independently of the little-endian routing-type code. -/
theorem bwNum_single {h : ℕ} (j : Fin h) :
    P1ChkDir.bwNum (Pi.single j (1 : ZMod 2)) = 2 ^ (h - 1 - j.val) := by
  induction h with
  | zero => exact Fin.elim0 j
  | succ h ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · have ht : Fin.tail (Pi.single (0 : Fin (h + 1)) 1 : BitWord (h + 1)) = 0 := by
        funext i
        change (Pi.single (0 : Fin (h + 1)) 1 : BitWord (h + 1)) i.succ = 0
        exact Pi.single_eq_of_ne (Fin.succ_ne_zero i) _
      unfold P1ChkDir.bwNum
      rw [bitWordFinEquiv_val, ht]
      rw [← P1ChkDir.bwNum, bwNum_zero]
      simp only [Pi.single_eq_same, ZMod.val_one, Nat.mul_one, Nat.zero_add,
        Nat.add_sub_cancel, Fin.val_zero, Nat.sub_zero]
    · have ht : Fin.tail (Pi.single j.succ 1 : BitWord (h + 1)) = Pi.single j 1 := by
        funext i
        change (Pi.single j.succ 1 : BitWord (h + 1)) i.succ = (Pi.single j 1 : BitWord h) i
        simp only [Pi.single_apply, Fin.succ_inj]
      unfold P1ChkDir.bwNum
      rw [bitWordFinEquiv_val, ht, ← P1ChkDir.bwNum, ih]
      simp only [Pi.single_eq_of_ne (Ne.symm (Fin.succ_ne_zero j)), ZMod.val_zero,
        Nat.mul_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      omega

def laneFlipNumber (t : ℕ) (q : Tally × ℕ) : ℕ :=
  let h := q.1.length
  let j := stageNumber (t + h) q.2
  bif ltb j t then 0 else pow2c (h - 1 - (j - t)) q.1

@[fun_prop] theorem poly_laneFlipNumber (t : ℕ) : Poly (laneFlipNumber t) := by
  unfold laneFlipNumber
  fun_prop

theorem laneFlipNumber_eq (t h c : ℕ) [NeZero (t + h)] :
    laneFlipNumber t (tally h, c) = P1ChkDir.bwNum (lnFlip t h c) := by
  let j := (Routing.stageBit (t + h) c).val
  unfold laneFlipNumber
  simp only [tally_length, stageNumber_eq]
  by_cases hj : j < t
  · have hz : lnFlip t h c = 0 := by
      funext s
      have hs : (s : ℕ) + t ≠ j := by omega
      simp only [lnFlip, Pi.zero_apply]
      exact ite_eq_right hs
    rw [show ltb j t = true from ltb_iff.mpr hj, Bool.cond_true, hz, bwNum_zero]
  · have hj' : j < t + h := (Routing.stageBit (t + h) c).isLt
    let s : Fin h := ⟨j - t, by omega⟩
    have hs : lnFlip t h c = Pi.single s 1 := by
      funext i
      have he : ((i : ℕ) + t = j) ↔ i = s := by
        rw [Fin.ext_iff]
        change ((i : ℕ) + t = j) ↔ (i : ℕ) = j - t
        omega
      simp only [lnFlip, Pi.single_apply]
      change (if (i : ℕ) + t = j then (1 : ZMod 2) else 0) = _
      simp only [he]
    rw [show ltb j t = false from ltb_false_iff.mpr (Nat.le_of_not_lt hj), Bool.cond_false, hs,
      pow2c_eq (by rw [tally_length]; omega), bwNum_single]

private def toggle (p j : ℕ) : ℕ :=
  let d := pow2c j (tally 3)
  bif eqb ((p / d) % 2) 0 then p + d else p - d

@[fun_prop] private theorem poly_toggle : Poly (fun p : ℕ × ℕ => toggle p.1 p.2) := by
  unfold toggle
  fun_prop

def rtTypeNumber (q : ℕ × ℕ × ℕ) : ℕ :=
  let j := stageNumber (3 + q.1) q.2.1
  bif ltb j 3 then toggle q.2.2 j else q.2.2

@[fun_prop] theorem poly_rtTypeNumber : Poly rtTypeNumber := by
  unfold rtTypeNumber
  fun_prop

theorem rtTypeNumber_eq (h c : ℕ) (π : BitWord 3) :
    rtTypeNumber (h, c, num3 π) = num3 (π + tyFlip 3 h c) := by
  let j := (Routing.stageBit (3 + h) c).val
  unfold rtTypeNumber
  simp only [stageNumber_eq]
  by_cases hj : j < 3
  · let i : Fin 3 := ⟨j, hj⟩
    have hi : tyFlip 3 h c = Pi.single i 1 := by
      funext k
      simp only [tyFlip, Pi.single_apply, Fin.ext_iff]
      rfl
    rw [show ltb j 3 = true from ltb_iff.mpr hj, Bool.cond_true, hi]
    have htab : ∀ (w : BitWord 3) (i : Fin 3), toggle (num3 w) i = num3 (w + Pi.single i 1) := by decide
    exact htab π i
  · have hz : tyFlip 3 h c = 0 := by
      funext i
      have hi : (i : ℕ) ≠ j := by have := i.isLt; omega
      simp only [tyFlip, Pi.zero_apply]
      exact ite_eq_right hi
    rw [show ltb j 3 = false from ltb_false_iff.mpr (Nat.le_of_not_lt hj), Bool.cond_false, hz, add_zero]

def stTypeNumber (q : ℕ × ℕ × ℕ) : ℕ :=
  bif eqb (stageNumber (1 + q.1) q.2.1) 0 then (q.2.2 + 1) % 2 else q.2.2

@[fun_prop] theorem poly_stTypeNumber : Poly stTypeNumber := by
  unfold stTypeNumber
  fun_prop

theorem stTypeNumber_eq (h c : ℕ) (π : BitWord 1) :
    stTypeNumber (h, c, (π 0).val) = ((π + tyFlip 1 h c) 0).val := by
  unfold stTypeNumber
  simp only [stageNumber_eq, Pi.add_apply, tyFlip, Fin.val_zero]
  by_cases hj : (Routing.stageBit (1 + h) c).val = 0
  · rw [eqb_iff.mpr hj, Bool.cond_true, ite_eq_left hj.symm]
    have htab : ∀ z : ZMod 2, (z.val + 1) % 2 = (z + 1).val := by decide
    exact htab (π 0)
  · rw [eqb_false_iff.mpr hj, Bool.cond_false, ite_eq_right (Ne.symm hj), add_zero]

end P1ProgDir.SolC4
