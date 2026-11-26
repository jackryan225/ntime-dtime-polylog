import P1Wrap.Params
import P1SolFmt.BitEncoding
import P1SolFmt.FigureTools

namespace P1SolFmt.SolParameters

open OAI.Computability.IntegerMultiplication
open Carry Staff Strip P1Wrap SolFigure

variable {X : Type} {r : Regime X} {t : X → ℕ}

/-- The time parameter for the padded input, in binary. -/
theorem figure_time (a b : ℕ) (hn : Figure r t) :
    Figure r (fun x => (b + 2 * a) * (t x ^ 2 + 1) + t x + 1) := by
  let nat := fun i => Figure.natural (r := r) i
  have sq := hn.multiplied hn
  convert (((nat (b + 2 * a)).multiplied (sq.added (nat 1))).added hn).added (nat 1) using 1
  funext i
  rw [pow_two]

theorem realizes_lam (ht : Figure r t) :
    Realizes r (fun x => Params.lam (t x)) := ht.short_log

private theorem log_eq_size_sub_one (n : ℕ) : Nat.log 2 n = n.size - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have hs : 0 < n.size := Nat.size_pos.2 hn
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact Nat.lt_size.1 (by omega)
    · rw [show n.size - 1 + 1 = n.size by omega]
      exact Nat.lt_size_self n

theorem realizes_p (ht : Figure r t) :
    Realizes r (fun x => Params.p (t x)) := by
  have h := ((Figure.of_spoken (realizes_lam ht)).added (Figure.natural (r := r) 1)).short_log
  simpa only [Params.p, ← SolBits.size_eq_clog_succ, log_eq_size_sub_one]
    using h.minused (Realizes.fix (r := r) 1)

theorem realizes_T (K : Consts) (ht : Figure r t) :
    Realizes r (fun x => Params.T K (t x)) :=
  (realizes_p ht).dividing (Realizes.fix (2 ^ K.j))

theorem realizes_h (ht : Figure r t) :
    Realizes r (fun x => Params.h (t x)) :=
  ((Realizes.fix 19).times (realizes_p ht)).dividing (Realizes.fix 2)

theorem figure_B (ht : Figure r t) :
    Figure r (fun x => Params.B (t x)) :=
  (Figure.natural 2).repeated ((realizes_p ht).dividing (Realizes.fix 2))

theorem figure_N (ht : Figure r t) :
    Figure r (fun x => Params.N (t x)) :=
  (Figure.natural 2).repeated (realizes_h ht)

theorem figure_I (a : ℕ) (ht : Figure r t) :
    Figure r (fun x => Params.I a (t x)) := by
  let nat := fun i => Figure.natural (r := r) i
  have hblock := (figure_B ht).multiplied (figure_N ht)
  have htime := (nat a).multiplied ((nat 2).repeated (realizes_lam ht))
  exact ((htime.added hblock).subtracted (nat 1)).quotients hblock

theorem figure_initial_positions (aM tapes external : ℕ) (ht : Figure r t) :
    Figure r (fun x =>
      let h := Params.h (t x)
      let localCount := 1 + (external + (tapes * 3 + (tapes * 3 +
        (tapes * (2 * (h + 3)) * 8 + (2 * (h + 1) * 2 + (1 + 1))))))
      2 * (Params.I aM (t x) * localCount) * Params.N (t x)) := by
  let num := fun n => Figure.natural (r := r) n
  have hh := Figure.of_spoken (realizes_h ht)
  have hRouting := ((num tapes).multiplied ((num 2).multiplied (hh.added (num 3)))).multiplied (num 8)
  have hState := ((num 2).multiplied (hh.added (num 1))).multiplied (num 2)
  have hPort := num (tapes * 3)
  have hLocal := (num 1).added ((num external).added
    (hPort.added (hPort.added (hRouting.added (hState.added (num (1 + 1)))))))
  exact ((num 2).multiplied ((figure_I aM ht).multiplied hLocal)).multiplied (figure_N ht)

theorem figure_tuple_width (external alphabet states tapes : ℕ) (ht : Figure r t) :
    Figure r (fun x =>
      external * (Params.B (t x) * alphabet + (states + tapes * Params.B (t x)))) := by
  let num := fun n => Figure.natural (r := r) n
  have hb := figure_B ht
  exact (num external).multiplied
    ((hb.multiplied (num alphabet)).added ((num states).added ((num tapes).multiplied hb)))

theorem figure_big_width (bias : ℕ) (ht : Figure r t) :
    Figure r (fun x => bias + 6 * Params.lam (t x)) :=
  (Figure.natural bias).added ((Figure.natural 6).multiplied (Figure.of_spoken (realizes_lam ht)))

theorem figure_small_width (bias growth : ℕ) {w n : X → ℕ}
    (hn : Realizes r n) (hw : Figure r w) :
    Figure r (fun x => bias + Nat.clog 2 (growth ^ n x * (w x + 1) + 1)) := by
  let num := fun k => Figure.natural (r := r) k
  have hg := (num growth).repeated hn
  have hwidth := ((hg.multiplied (hw.added (num 1))).added (num 1)).short_log
  exact (num bias).added (Figure.of_spoken hwidth)

theorem figure_chain_length (factor : ℕ) {p n : X → ℕ}
    (hp : Figure r p) (hn : Realizes r n) :
    Figure r (fun x => p x / factor ^ n x + 1) :=
  (hp.quotients ((Figure.natural factor).repeated hn)).added (Figure.natural 1)

theorem figure_guess_blocks {g : X → ℕ} (ht : Figure r t) (hg : Figure r g) :
    Figure r (fun x => if g x = 0 then 0 else (2 * g x - 1) / Params.bb (t x) + 1) := by
  let num := fun n => Figure.natural (r := r) n
  have hBlock := (figure_B ht).multiplied (figure_N ht)
  have hCount := ((((num 2).multiplied hg).subtracted (num 1)).quotients hBlock).added (num 1)
  exact (num 0).variant hCount (classified_eq hg (num 0))

#print axioms figure_I

end P1SolFmt.SolParameters
