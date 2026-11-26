import P1ProgDir.C4ProgTask
import P1ProgDir.C4ProgBounds

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ChkDir

variable {K : Type} [Fintype K] [DecidableEq K] {a : ℕ}

def wiredFormat (τ : K → ℕ) (dims : ℕ → C4Dims) : C4Format K where
  dims n := (dims n).D
  height n := (dims n).h
  tapes _ := τ
  contentWidth n := (dims n).Wc
  stateWidth n := (dims n).Ws
  tableWidth n := (dims n).Wt

theorem wiredFormat_check (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims)
    (x u : List Bool) (i : ℕ) : (wiredFormat τ dims).check ha x.length u i = C4w ha τ dims x u i := rfl

open Classical in
theorem progC4_of_publicPlan (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims)
    (hPlan : Poly ((wiredFormat τ dims).prepare a))
    (hWidths : Dom size (fun p : C4Query => allFieldWidths ((wiredFormat τ dims).prepare a p))) :
    ProgC4 ha τ dims := by
  obtain ⟨k, C, ht⟩ := taskC4_of_format (wiredFormat τ dims) ha hPlan hWidths
  obtain ⟨D, hD⟩ := arbitrary_binary_overhead k C
  refine ⟨k, (ht.bound (D + 8) ?_).conform (fun _ => rfl) (fun _ => rfl) (fun p => ?_)⟩
  · intro p
    have hs := Nat.add_le_add_right (compactQuery_size p) 1
    have hc := (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs k)).trans
      (hD p.1.length p.2.1.length p.2.2.length)
    let Q := P1ChkDir.budget k p + 1
    have hLin : size p + p.2.1.length + 1 ≤ 8 * Q := by
      simp only [Q, P1ChkDir.budget, size_prod, size_word]
      omega
    have hSmall : p.2.1.length + 1 + (Nat.log 2 (p.1.length + 1) + p.2.2.length + 1) ^ k ≤ Q := by
      unfold Q P1ChkDir.budget
      omega
    change size p + p.2.1.length + C * (size (compactQuery p) + 1) ^ k + 1 ≤ _
    rw [Nat.add_right_comm (size p + p.2.1.length)]
    calc
      _ ≤ 8 * Q + D * Q := Nat.add_le_add hLin (hc.trans (Nat.mul_le_mul_left D hSmall))
      _ = (D + 8) * Q := by ring
  · rw [wiredFormat_check]

end P1ProgDir.SolC4
