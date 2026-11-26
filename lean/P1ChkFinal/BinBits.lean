import P1ChkFinal.Skeleton
import Mathlib.Data.Nat.Bits

/-! `bin n = Nat.bits n`: the canonical binary word of the skeleton is Mathlib's `Nat.bits`. -/

namespace P1ChkFinal

theorem bin_eq_bits : ∀ n, bin n = Nat.bits n
  | 0 => by simp [bin]
  | n + 1 => by
    have hb : Nat.bit (decide ((n + 1) % 2 = 1)) ((n + 1) / 2) = n + 1 := by
      rw [Nat.bit_val]
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h] <;> omega
    have hc : (n + 1) / 2 = 0 → decide ((n + 1) % 2 = 1) = true := by
      intro h0
      have : n = 0 := by omega
      subst this
      decide
    conv_rhs => rw [← hb]
    rw [Nat.bits_append_bit _ _ hc, bin, bin_eq_bits ((n + 1) / 2)]

end P1ChkFinal
