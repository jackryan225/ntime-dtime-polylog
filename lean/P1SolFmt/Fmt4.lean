import P1ChkDir.C4Wired
import P1ChkFinal.BinBits
import P1SolFmt.Genuine

namespace P1SolFmt

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1Wrap
open SolFigure SolFormat SolParameters SolGeometry
open private levelDims layoutRows runPhases from P1Wit.SpaceFacts

namespace SolFmt4

private theorem poly_cons {X Y : Type} [Codec X] [Codec Y] {f : X → Y}
    {g : X → List Y} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) :=
  (hf.pair hg).compose Poly.cons

private theorem lanes_le (t : ℕ) : 2 ^ Params.h t ≤ (Params.lam t + 1) ^ 10 := by
  have hh : Params.h t ≤ 10 * Params.p t := by
    unfold Params.h
    omega
  have hp : 2 ^ Params.p t ≤ Params.lam t + 1 := by
    unfold Params.p
    rcases Nat.eq_zero_or_pos (Params.lam t) with h | h
    · rw [h]
      decide
    · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ _)
  calc
    _ ≤ 2 ^ (10 * Params.p t) := Nat.pow_le_pow_right (by decide) hh
    _ = (2 ^ Params.p t) ^ 10 := by rw [Nat.mul_comm 10, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left hp _

private theorem realizes_lanes {X : Type} {r : Regime X} {t : X → ℕ}
    (ht : Figure r t) : Realizes r (fun x => 2 ^ Params.h (t x)) := by
  have hd := (diameter _ (realizes_lam ht)).add (Dom.const r.scale 1)
  exact (figure_N ht).pay ((hd.pow 10).mono (fun x => lanes_le (t x)))

private theorem realizes_width {X : Type} {r : Regime X} {W T : X → ℕ}
    (bias growth : ℕ) (hT : Realizes r T) (hW : Figure r W) :
    Realizes r (fun x => bias + Nat.clog 2 (growth ^ T x * (W x + 1) + 1)) := by
  let num := fun n => Carry.Figure.natural (r := r) n
  have h := (((num growth).repeated hT).multiplied (hW.added (num 1))).added (num 1)
  exact (Staff.Realizes.fix bias).plus h.short_log

private theorem row_zero_widths {k : Type*} [Field k] (S : BlockSchedule k)
    (P H : ℕ) (phases : List Phase) :
    let row := ((layoutRows S P H phases)[0]?).getD
      (levelDims S.expanderExponent 0 0 0 none)
    row.laneW = Nat.clog 2 row.lanes ∧ row.slotW = Nat.clog 2 row.slots := by
  cases phases <;> constructor <;> exact (Nat.clog_pow 2 _ (by decide)).symm

private theorem offset_figure {D : Bits.Word → Dims}
    (data : DimsFigures (inputRegime (Bits.Word × Tally)) (fun p => D p.1))
    (s : ℕ) : Figure (inputRegime Bits.Word) (fun w => (D w).off s) := by
  have hs : Realizes (inputRegime (Bits.Word × Tally)) (fun p => p.2.length) :=
    realizes_of_tally (show (inputRegime (Bits.Word × Tally)).Has Prod.snd from Easy.snd.poly)
  obtain ⟨word, hword, hv⟩ := (data.count hs).multiplied (data.width hs)
  exact offsets_with_value (d := D) (s := fun _ => s) (Code.Poly.const (tally s)) hword hv

private theorem value_bits (n : ℕ) : P1Batch.bval (Nat.bits n) = n := by
  rw [← P1ChkFinal.bin_eq_bits, P1ChkFinal.bval_bin]

variable {k : Type*} [Field k] {S : BlockSchedule k}

private theorem fmt4_of_figures (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine)
    (aM d bigBias termBias : ℕ) (t g : ℕ → ℕ)
    (ht : Figure (inputRegime Bits.Word) (fun w => t (P1Batch.bval w)))
    (hg : Figure (inputRegime Bits.Word) (fun w => g (P1Batch.bval w))) :
    P1ChkDir.FmtHyp4 (fun n =>
      { D := genuineDims A K V aM (t n) (g n) d bigBias termBias
        h := Params.h (t n)
        Wc := P1Net.strWidth V (Params.B (t n))
        Ws := P1Net.strWidth V (Params.B (t n))
        Wt := P1Net.tupWidth V (Params.B (t n)) }) := by
  let R := inputRegime Bits.Word
  let D : Bits.Word → Dims :=
    fun w => genuineDims A K V aM (t (P1Batch.bval w)) (g (P1Batch.bval w)) d bigBias termBias
  let P : Bits.Word → P1ChkDir.C4Dims := fun w =>
    { D := D w
      h := Params.h (t (P1Batch.bval w))
      Wc := P1Net.strWidth V (Params.B (t (P1Batch.bval w)))
      Ws := P1Net.strWidth V (Params.B (t (P1Batch.bval w)))
      Wt := P1Net.tupWidth V (Params.B (t (P1Batch.bval w))) }
  let num := fun n => Carry.Figure.natural (r := R) n
  let fix := fun n => Staff.Realizes.fix (r := R) n
  have data : DimsFigures R D := genuineDims_figures A K V aM d bigBias termBias ht hg
  have sdata : DimsFigures (inputRegime (Bits.Word × Tally)) (fun p => D p.1) :=
    genuineDims_figures A K V aM d bigBias termBias
      (SolFigure.Figure.pullback Easy.fst.poly ht) (SolFigure.Figure.pullback Easy.fst.poly hg)
  have level := data.level (fix 0)
  have hoff (s : ℕ) : Poly (fun w => Nat.bits ((D w).off s)) :=
    figure_poly (offset_figure sdata s)
  have hB := figure_B ht
  have hStr : Figure R (fun w => (P w).Wc) :=
    (hB.multiplied (num (Fintype.card V.Γ))).added
      ((num (Fintype.card V.Q)).added ((num (Fintype.card V.K)).multiplied hB))
  have hTup : Figure R (fun w => (P w).Wt) :=
    (num (Fintype.card (P1Net.Ext V.K))).multiplied hStr
  have hBig : Poly (fun w => (P1ChkDir.fmtBig (P w)).map Nat.bits) := by
    simp only [P1ChkDir.fmtBig, List.map_cons, List.map_nil]
    exact poly_cons (figure_poly data.intervals) <|
      poly_cons (figure_poly data.rTape) <|
      poly_cons (figure_poly level.slots) <|
      poly_cons (figure_poly level.lanes) <|
      poly_cons (hoff secStart) <|
      poly_cons (hoff secPrev) <|
      poly_cons (hoff secNext) <|
      poly_cons (hoff (secLev 0 .outAddr)) <|
      poly_cons (hoff (secLev 0 .outDisp)) <|
      poly_cons (hoff (secLev 0 .outFar)) <|
      poly_cons (hoff (secLev 0 .inAddr)) <|
      poly_cons (hoff (secLev 0 .inDisp)) <|
      poly_cons (hoff (secLev 0 .inFar)) <|
      poly_cons (hoff (secLev 0 .width)) <|
      poly_cons (figure_poly hStr) <|
      poly_cons (figure_poly hStr) <|
      poly_cons (figure_poly hTup) (Code.Poly.const [])

  have hN : Realizes R (fun w => 2 ^ (P w).h) := realizes_lanes ht
  have hh : Realizes R (fun w => (P w).h) := realizes_h ht
  have hBigW : Realizes R (fun w => (D w).bigW) :=
    (fix bigBias).plus ((fix 6).times (realizes_lam ht))
  have hWidth : Realizes R (fun w => (D w).wW) :=
    realizes_width termBias A.growthConstant (realizes_T K ht) hTup
  have rowWidths (w : Bits.Word) := row_zero_widths S
    (initialPositions V aM (t (P1Batch.bval w))) ((P w).h)
      (runPhases S (Params.T K (t (P1Batch.bval w))))
  have hLaneW : Realizes R (fun w => ((D w).lv 0).laneW) := by
    convert level.lanes.short_log using 1
    funext w
    exact (rowWidths w).1
  have hSlotW : Realizes R (fun w => ((D w).lv 0).slotW) := by
    convert level.slots.short_log using 1
    funext w
    exact (rowWidths w).2
  have hLevEq (w : Bits.Word) (m : Mem) :
      (D w).width (secLev 0 m) = (D w).levWidth ((D w).lv 0) m := by
    rw [Dims.width, (D w).kind_secLev m (Nat.zero_le _)]
  have hSmall : Poly (fun w => (P1ChkDir.fmtSmall (P w)).map tally) := by
    simp only [P1ChkDir.fmtSmall, List.map_cons, List.map_nil]
    dsimp only [P]
    simp only [hLevEq, Dims.levWidth]
    simp only [Dims.width, Dims.kind_start, Dims.kind_prev, Dims.kind_next]
    exact poly_cons hN <| poly_cons hh <|
      poly_cons hBigW <| poly_cons hBigW <| poly_cons hBigW <|
      poly_cons hBigW <| poly_cons hLaneW <| poly_cons hSlotW <|
      poly_cons hBigW <| poly_cons hLaneW <| poly_cons hSlotW <|
      poly_cons hWidth (Code.Poly.const [])
  refine ⟨_, hBig.pair hSmall, fun w => ⟨?_, ?_⟩⟩
  · change ((P1ChkDir.fmtBig (P w)).map Nat.bits).map P1Batch.bval = P1ChkDir.fmtBig (P w)
    simp only [P1ChkDir.fmtBig, List.map_cons, List.map_nil, value_bits]
  · change ((P1ChkDir.fmtSmall (P w)).map tally).map List.length = P1ChkDir.fmtSmall (P w)
    simp only [P1ChkDir.fmtSmall, List.map_cons, List.map_nil, tally_length]

end SolFmt4

theorem fmtHyp4_genuine {k : Type*} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) :
    P1ChkDir.FmtHyp4 (fun n =>
      { D := P1Wit.SolSpace.genuineDims A K V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias
        h := P1Wrap.Params.h (P1Int.lpTime a b n)
        Wc := P1Net.strWidth V (P1Wrap.Params.B (P1Int.lpTime a b n))
        Ws := P1Net.strWidth V (P1Wrap.Params.B (P1Int.lpTime a b n))
        Wt := P1Net.tupWidth V (P1Wrap.Params.B (P1Int.lpTime a b n)) }) := by
  have ht : Figure (inputRegime Bits.Word) (fun w => P1Int.lpTime a b (P1Batch.bval w)) := by
    simpa only [P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hg : Figure (inputRegime Bits.Word) (fun w => a * (P1Batch.bval w ^ 2 + 1)) := by
    let num := fun n => Carry.Figure.natural (r := inputRegime Bits.Word) n
    simpa only [pow_two] using (num a).multiplied ((figure_bval.multiplied figure_bval).added (num 1))
  exact SolFmt4.fmt4_of_figures A K V aM d bigBias termBias _ _ ht hg

#print axioms fmtHyp4_genuine

end P1SolFmt
