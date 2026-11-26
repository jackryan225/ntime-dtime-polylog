import P1Wit.Layout

namespace P1ProgDir.SolOffsets

open P1Wit

def tritEnd (D : Dims) : ℕ := D.I * D.N * D.r * 2
def startEnd (D : Dims) : ℕ := tritEnd D + D.I * D.r * D.bigW
def prevEnd (D : Dims) : ℕ := startEnd D + D.I * D.r * 3 * D.bigW
def nextEnd (D : Dims) : ℕ := prevEnd D + D.I * D.r * 3 * D.bigW
def guessEnd (D : Dims) : ℕ := nextEnd D + D.nGB * D.bigW

theorem off_trit (D : Dims) : D.off secTrit = 0 := rfl

theorem off_start (D : Dims) : D.off secStart = tritEnd D :=
  Nat.zero_add _

theorem off_prev (D : Dims) : D.off secPrev = startEnd D := by
  change D.off secStart + D.I * D.r * D.bigW = _
  rw [off_start]
  rfl

theorem off_next (D : Dims) : D.off secNext = prevEnd D := by
  change D.off secPrev + D.I * D.r * 3 * D.bigW = _
  rw [off_prev]
  rfl

theorem off_guess (D : Dims) : D.off secGuess = nextEnd D := by
  change D.off secNext + D.I * D.r * 3 * D.bigW = _
  rw [off_next]
  rfl

theorem off_after_guess (D : Dims) : D.off 5 = guessEnd D := by
  change D.off secGuess + D.nGB * D.bigW = _
  rw [off_guess]
  rfl

theorem head_fits {D : Dims} {m : ℕ} (hm : D.fixedLen ≤ m) :
    guessEnd D ≤ m := by
  rw [← off_after_guess]
  apply le_trans _ hm
  change offAt D.count D.width 5 ≤ offAt D.count D.width D.nSec
  have hs : 5 ≤ D.nSec := by unfold Dims.nSec; omega
  have mono : Monotone (offAt D.count D.width) := by
    apply monotone_nat_of_le_succ
    intro n
    change offAt D.count D.width n ≤ offAt D.count D.width n + D.count n * D.width n
    exact Nat.le_add_right _ _
  exact mono hs

theorem interval_fits {D : Dims} {s i m : ℕ} (hi : i < D.count s) (hs : s + 1 ≤ 5)
    (hm : guessEnd D ≤ m) :
    D.off s + i * D.width s + D.width s ≤ m := by
  rw [← off_after_guess] at hm
  have mono : Monotone (offAt D.count D.width) := by
    apply monotone_nat_of_le_succ
    intro n
    change offAt D.count D.width n ≤ offAt D.count D.width n + D.count n * D.width n
    exact Nat.le_add_right _ _
  have h := (mono hs).trans hm
  change D.off s + D.count s * D.width s ≤ m at h
  rw [Nat.add_assoc, ← Nat.succ_mul]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _).trans h

theorem start_slice_fits (D : Dims) {m : ℕ} (hm : guessEnd D ≤ m) :
    D.off secStart + D.I * (D.r * D.bigW) ≤ m := by
  rw [off_start, ← Nat.mul_assoc]
  change startEnd D ≤ m
  unfold guessEnd nextEnd prevEnd at hm
  exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
    ((Nat.le_add_right _ _).trans hm))

theorem trit_row_fits (D : Dims) {m j : ℕ} (hm : guessEnd D ≤ m) (hj : j < D.I) :
    D.off secTrit + j * (D.N * D.r * 2) + D.N * D.r * 2 ≤ m := by
  rw [off_trit, Nat.zero_add, ← Nat.succ_mul]
  have ht : tritEnd D ≤ m := by
    unfold guessEnd nextEnd prevEnd startEnd at hm
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hm)))
  refine (Nat.mul_le_mul_right _ hj).trans ?_
  simpa only [tritEnd, Nat.mul_assoc] using ht

end P1ProgDir.SolOffsets
