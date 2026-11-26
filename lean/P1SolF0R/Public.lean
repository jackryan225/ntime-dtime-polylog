import P1P5.Factor0Target
import P1SolF0R.Budget
import P1SolFmt.Parameters
import P1SolC10P.Primitives

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Carry
open P1Int P1Wrap P1ChkFinal.AstraC10 P1SolFmt.SolFigure P1SolFmt.SolParameters
open scoped P1ChkFinal.AstraC10

/-- The public quantities needed to read the first four witness sections and input pins.
The order is big intervals, lanes per interval, cells per small block, lane bits, directory
field width, guess length. -/
abbrev Public := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def publicParams (a b bigBias n : ℕ) : Public :=
  let t := lpTime a b n
  (Params.I 1 t, Params.N t, Params.B t, Params.h t, bigBias + 6 * Params.lam t, a * (n ^ 2 + 1))

theorem publicParams_poly (a b bigBias : ℕ) : Poly (publicParams a b bigBias) := by
  let R := inputRegime ℕ
  have hn : Figure R (fun n => n) := ⟨binary, Poly.identity, value_binary⟩
  have ht : Figure R (lpTime a b) := by
    convert figure_time a b hn using 1
    funext n
    unfold lpTime
    ring
  have hI := P1SolC10P.SolC10prog.writeFigure (figure_I 1 ht)
  have hN := P1SolC10P.SolC10prog.writeFigure (figure_N ht)
  have hB := P1SolC10P.SolC10prog.writeFigure (figure_B ht)
  have hh := P1SolC10P.SolC10prog.writeFigure (Figure.of_spoken (realizes_h ht))
  have hw := P1SolC10P.SolC10prog.writeFigure (figure_big_width bigBias ht)
  have hg : Poly (fun n : ℕ => a * (n ^ 2 + 1)) := by
    rw [show (fun n : ℕ => a * (n ^ 2 + 1)) = (fun n : ℕ => a * (n * n + 1)) by
      funext n; rw [pow_two]]
    fun_prop
  exact hI.pair (hN.pair (hB.pair (hh.pair (hw.pair hg))))

theorem log_le_binary_size (n : ℕ) : Nat.log 2 (n + 1) ≤ size n := by
  have he : Nat.log 2 (n + 1) ≤ Nat.clog 2 (n + 1) := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    exact (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)).trans (Nat.le_pow_clog (by decide) _)
  change Nat.log 2 (n + 1) ≤ size (binary n)
  rw [P1ChkFinal.size_listBool, binary, Bits.short_length]
  omega

theorem binary_size_le_log (n : ℕ) : size n ≤ 2 * Nat.log 2 (n + 1) + 3 := by
  change size (binary n) ≤ _
  rw [P1SolC10P.SolC10prog.binary_eq_bin, P1ChkFinal.size_listBool]
  have h : (P1ChkFinal.bin n).length ≤ Nat.log 2 (n + 1) + 1 := (P1ChkFinal.length_bin_log n).trans
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ n)) 1)
  omega

/-- Unary clocks for the lane count, block size, and lane bit width. -/
abbrev PublicClocks := Public × Tally × Tally × Tally

def withClocks (a b bigBias n : ℕ) : PublicClocks :=
  let p := publicParams a b bigBias n
  (p, tally p.2.1, tally p.2.2.1, tally p.2.2.2.1)

theorem withClocks_poly (a b bigBias : ℕ) : Poly (withClocks a b bigBias) := by
  have hlog : Dom (size (X := ℕ)) (fun n => Nat.log 2 (n + 1)) :=
    (Dom.base _).mono log_le_binary_size
  have hbb := (block_dom a b).sub hlog
  have hB (n : ℕ) : Params.B (lpTime a b n) ≤ Params.bb (lpTime a b n) := by
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hN (n : ℕ) : Params.N (lpTime a b n) ≤ Params.bb (lpTime a b n) := by
    unfold Params.bb
    rw [Nat.mul_comm]
    exact Nat.le_mul_of_pos_right _ (Params.B_pos _)
  have hh (n : ℕ) : Params.h (lpTime a b n) ≤ Params.bb (lpTime a b n) :=
    (Nat.lt_two_pow_self : Params.h (lpTime a b n) < 2 ^ Params.h (lpTime a b n)).le.trans (hN n)
  have hp := publicParams_poly a b bigBias
  have pn := P1SolC10P.SolC10prog.poly_tally hp.sndCompose.fstCompose (hbb.mono hN)
  have pb := P1SolC10P.SolC10prog.poly_tally hp.sndCompose.sndCompose.fstCompose (hbb.mono hB)
  have ph := P1SolC10P.SolC10prog.poly_tally hp.sndCompose.sndCompose.sndCompose.fstCompose (hbb.mono hh)
  exact hp.pair (pn.pair (pb.pair ph))

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.publicParams_poly
