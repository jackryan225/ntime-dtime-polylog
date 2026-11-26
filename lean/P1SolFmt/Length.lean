import P1ChkFinal.Progs
import P1SolFmt.BitEncoding
import OAI.Computability.IntegerMultiplication.Carry.Shrink

namespace P1SolFmt.SolLength

open OAI.Computability.IntegerMultiplication
open Code Carry

theorem born_eq_bits (n : ℕ) : born n = Nat.bits n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [born0, Nat.zero_bits]
    rw [birth hn, SolBits.bits_of_pos hn, ih _ (Nat.div_lt_self hn (by decide)), parity]

theorem lenHyp : P1ChkFinal.LenHyp := by
  have hh : Easy (fun x : List Bool => born (ruler x).length) :=
    (Easy.ruler (g := id) Easy.identity).compose easy_chart
  have hbits : Easy (fun x : List Bool => Nat.bits x.length) := by
    simpa only [ruler_length, born_eq_bits] using hh
  unfold P1ChkFinal.LenHyp
  refine Task.bound (show Computes size _ from hbits) 2 (fun x => ?_)
  rw [Bits.size_word]
  omega

#print axioms lenHyp

end P1SolFmt.SolLength
