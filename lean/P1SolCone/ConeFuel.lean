import P1SolCone.ConeFormat
import P1SolCone.BoundedWords

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wrap P1Int P1Int.P11 P1Wit.SolSpace
open P1SolFmt.SolFigure P1SolFmt.SolParameters

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (V : C1Challenge.Machine)
  (a b : ℕ)

theorem power_p_le_lam_succ (t : ℕ) : 2 ^ Params.p t ≤ Params.lam t + 1 := by
  unfold Params.p
  by_cases h : Params.lam t = 0
  · simp only [h, Nat.log_zero_right, pow_zero, Nat.zero_add, le_refl]
  · exact (Nat.pow_log_le_self 2 h).trans (Nat.le_succ _)

theorem Mbar_le_clock (n : ℕ) :
    Mbar B V a b n ≤ (tupleCoeff (toOAI V) + 1) *
      (Params.lam (lpTime a b n) + 1) ^ (B.growthConstant + 1) := by
  let t := lpTime a b n
  let L := Params.lam t + 1
  let C := B.growthConstant
  have hg : C ^ Params.T (portConsts B) t ≤ L ^ C := by
    simpa only [Nat.zero_add, Nat.one_mul, Nat.mul_one, L] using
      predecessor_growth_le (portConsts B) 0 t C
  have hb : Params.B t ≤ L := (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.div_le_self _ _)).trans
    (power_p_le_lam_succ t)
  have hW := P1Net.tupWidth_le (toOAI V) (Params.B t)
  have hBp := Params.B_pos t
  have hw : P1Net.tupWidth (toOAI V) (Params.B t) + 1 ≤ (tupleCoeff (toOAI V) + 1) * L := by
    calc
      _ ≤ tupleCoeff (toOAI V) * Params.B t + Params.B t := Nat.add_le_add hW hBp
      _ = (tupleCoeff (toOAI V) + 1) * Params.B t := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (tupleCoeff (toOAI V) + 1) * L := Nat.mul_le_mul_left _ hb
  calc
    Mbar B V a b n ≤ L ^ C * ((tupleCoeff (toOAI V) + 1) * L) := Nat.mul_le_mul hg hw
    _ = (tupleCoeff (toOAI V) + 1) * L ^ (C + 1) := by rw [pow_succ]; ring

theorem coneMbarFigure {X : Type} [Codec X] [Inhabited X] {n : X → Bits.Word} (hn : Poly n) :
    Figure (inputRegime X) (fun x => Mbar B V a b (P1Batch.bval (n x))) := by
  let t := fun x => lpTime a b (P1Batch.bval (n x))
  let U := toOAI V
  have ht := coneTimeFigure a b hn
  have hw : Figure (inputRegime X) (fun x => P1Net.tupWidth U (Params.B (t x))) :=
    figure_tuple_width (Fintype.card (P1Net.Ext U.K)) (Fintype.card U.Γ)
      (Fintype.card U.Q) (Fintype.card U.K) ht
  exact ((Figure.natural B.growthConstant).repeated (realizes_T (portConsts B) ht)).multiplied
    (hw.added (Figure.natural 1))

theorem coneMbarRealizes {X : Type} [Codec X] [Inhabited X] {n : X → Bits.Word} (hn : Poly n) :
    Realizes (inputRegime X) (fun x => Mbar B V a b (P1Batch.bval (n x))) := by
  have hL := (diameter _ (realizes_lam (coneTimeFigure a b hn))).add (Dom.const _ 1)
  apply (coneMbarFigure B V a b hn).pay
  exact ((Dom.const _ (tupleCoeff (toOAI V) + 1)).mul (hL.pow (B.growthConstant + 1))).mono
    (fun x => Mbar_le_clock B V a b (P1Batch.bval (n x)))

/-- The power-of-two tally is built from its unary exponent, which is small before expansion. -/
def coneFuelExponent (w : Bits.Word) : Tally :=
  tally (B.growthConstant ^ 2 * (Mbar B V a b (P1Batch.bval w) + 1))

theorem coneFuelExponent_poly : Poly (coneFuelExponent B V a b) :=
  (Realizes.fix (r := inputRegime Bits.Word) (B.growthConstant ^ 2)).times
    ((coneMbarRealizes B V a b Code.Poly.identity).plus (Realizes.fix 1))

theorem coneFuel_fromExponent :
    Task (fun w : Bits.Word => 2 ^ (coneFuelExponent B V a b w).length)
      (fun w => send (coneFuelExponent B V a b w))
      (fun w => send (conePad B.growthConstant (Mbar B V a b (P1Batch.bval w)))) := by
  simpa only [coneFuelExponent, conePad, tally_length] using
    powTwoTally_computes.on (coneFuelExponent B V a b)

end

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.coneFuel_fromExponent
