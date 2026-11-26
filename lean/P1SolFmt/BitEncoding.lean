import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

namespace P1SolFmt.SolBits

theorem bits_of_pos {n : ℕ} (hn : 0 < n) :
    Nat.bits n = decide (n % 2 = 1) :: Nat.bits (n / 2) := by
  have hp : decide (n % 2 = 1) = Nat.bodd n := by
    rw [Nat.mod_two_of_bodd]
    cases Nat.bodd n <;> rfl
  have hb : Nat.div2 n = 0 → Nat.bodd n = true := by
    intro hz
    have hv := Nat.bodd_add_div2 n
    cases he : Nat.bodd n
    · simp only [hz, he, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
      omega
    · rfl
  have hs := Nat.bits_append_bit (Nat.div2 n) (Nat.bodd n) hb
  rw [Nat.bit_bodd_div2, Nat.div2_val] at hs
  rw [hp]
  exact hs

theorem size_eq_clog_succ (n : ℕ) : n.size = Nat.clog 2 (n + 1) := by
  apply le_antisymm
  · apply Nat.size_le.2
    have hn := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (n + 1)
    omega
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2 (Nat.lt_size_self n)

theorem bits_length_eq_clog_succ (n : ℕ) : n.bits.length = Nat.clog 2 (n + 1) := by
  rw [Nat.size_eq_bits_len, size_eq_clog_succ]

end P1SolFmt.SolBits
