import P1SolFmt.SectionTable
import P1SolFmt.Format

namespace P1SolFmt.SolGeometry

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open P1Wit SolFigure

variable {X : Type} {r : Regime X}

/-- Binary computations of the numeric fields used in each level of the layout. -/
structure LevelFigures (r : Regime X) (L : X → LevelDims) : Prop where
  bases : Figure r (fun x => (L x).bases)
  slots : Figure r (fun x => (L x).slots)
  slotW : Figure r (fun x => (L x).slotW)
  lanes : Figure r (fun x => (L x).lanes)
  laneW : Figure r (fun x => (L x).laneW)
  shrink : Figure r (fun x => (L x).shrink.toNat)
  colW : Figure r (fun x => (L x).colW)
  tagW : Figure r (fun x => (L x).tagW)
  termKeys : Figure r (fun x => (L x).termKeys)
  termArity : Figure r (fun x => (L x).termArity)

theorem LevelFigures.count {L : X → LevelDims} (h : LevelFigures r L) (m : Mem) :
    Figure r (fun x => (L x).count m) := by
  let num := fun n => Carry.Figure.natural (r := r) n
  have hshrink : Classified r (fun x => (L x).shrink = true) := by
    apply classified_congr (classified_eq h.shrink (num 1))
    intro x
    cases (L x).shrink <;> decide
  have hArc := h.bases.multiplied h.slots
  cases m
  · exact (num 1).variant (num 0) hshrink
  · exact hArc
  · exact hArc
  · exact hArc
  · exact hArc
  · exact hArc
  · exact hArc
  · exact (h.bases.multiplied h.lanes).multiplied h.slots
  · exact h.bases.variant (num 0) hshrink
  · exact h.bases.variant (num 0) hshrink
  · exact (h.bases.multiplied (num 2)).variant (num 0) hshrink
  · exact (h.bases.multiplied h.termKeys).multiplied (h.termArity.added (num 1))

theorem LevelFigures.width {d : X → Dims} {L : X → LevelDims} (h : LevelFigures r L)
    (hbig : Figure r (fun x => (d x).bigW)) (hw : Figure r (fun x => (d x).wW)) (m : Mem) :
    Figure r (fun x => (d x).levWidth (L x) m) := by
  cases m
  · exact Carry.Figure.natural 1
  · exact hbig
  · exact h.laneW
  · exact h.slotW
  · exact hbig
  · exact h.laneW
  · exact h.slotW
  · exact hw
  · exact h.colW
  · exact h.tagW
  · exact hbig
  · exact hw

end P1SolFmt.SolGeometry

namespace P1SolFmt.SolFormat

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open P1Wit SolGeometry

variable {X : Type} {r : Regime X}

/-- Computable data used by the layout's section arithmetic. -/
structure DimsFigures (r : Regime X) (d : X → Dims) : Prop where
  top : Realizes r (fun x => (d x).top)
  rTape : Figure r (fun x => (d x).r)
  intervals : Figure r (fun x => (d x).I)
  blocksPerInterval : Figure r (fun x => (d x).N)
  guessBlocks : Figure r (fun x => (d x).nGB)
  bigW : Figure r (fun x => (d x).bigW)
  wW : Figure r (fun x => (d x).wW)
  chainLen : Figure r (fun x => (d x).chainLen)
  chainW : Figure r (fun x => (d x).chainW)
  level : ∀ {i : X → ℕ}, Realizes r i → LevelFigures r (fun x => (d x).lv (i x))

variable {d : X → Dims}

theorem DimsFigures.count (h : DimsFigures r d) {s : X → ℕ} (hs : Realizes r s) :
    Figure r (fun x => (d x).count (s x)) := by
  let num := fun n => Carry.Figure.natural (r := r) n
  let fix := fun n => Staff.Realizes.fix (r := r) n
  have hlev := h.level ((hs.minused (fix 5)).dividing (fix 12))
  have hfin := h.level h.top
  let f : X → Kind → ℕ := fun x k => match k with
    | .trit => (d x).I * (d x).N * (d x).r
    | .start => (d x).I * (d x).r
    | .prevOwn | .nextOwn => (d x).I * (d x).r * 3
    | .guess => (d x).nGB
    | .lev ℓ m => ((d x).lv ℓ).count m
    | .Omega => ((d x).lv (d x).top).bases
    | .chain => (d x).chainLen
    | .unused => 0
  have hStart := h.intervals.multiplied h.rTape
  have hOwn := hStart.multiplied (num 3)
  exact sectionFigure d hs h.top f ((h.intervals.multiplied h.blocksPerInterval).multiplied h.rTape)
    hStart hOwn hOwn h.guessBlocks hlev.count hfin.bases h.chainLen (num 0)

theorem DimsFigures.width (h : DimsFigures r d) {s : X → ℕ} (hs : Realizes r s) :
    Figure r (fun x => (d x).width (s x)) := by
  let num := fun n => Carry.Figure.natural (r := r) n
  let fix := fun n => Staff.Realizes.fix (r := r) n
  have hlev := h.level ((hs.minused (fix 5)).dividing (fix 12))
  let f : X → Kind → ℕ := fun x k => match k with
    | .trit => 2
    | .start | .prevOwn | .nextOwn | .guess | .Omega => (d x).bigW
    | .lev ℓ m => (d x).levWidth ((d x).lv ℓ) m
    | .chain => (d x).chainW
    | .unused => 0
  exact sectionFigure d hs h.top f (num 2) h.bigW h.bigW h.bigW h.bigW
    (hlev.width h.bigW h.wW) h.bigW h.chainW (num 0)

/-- The layout programs supply the components of the exact check format. -/
theorem fmtHyp_of_figures (dims : ℕ → Dims)
    (wdata : DimsFigures (SolFigure.inputRegime Bits.Word) (fun w => dims (P1Batch.bval w)))
    (sdata : DimsFigures (SolFigure.inputRegime (Bits.Word × Tally))
      (fun p => dims (P1Batch.bval p.1))) :
    P1ChkFinal.FmtHyp dims := by
  have hs : Realizes (SolFigure.inputRegime (Bits.Word × Tally)) (fun x => x.2.length) :=
    SolFigure.realizes_of_tally
      (show (SolFigure.inputRegime (Bits.Word × Tally)).Has Prod.snd from Easy.snd.poly)
  have hf := wdata.level wdata.top
  exact fmtHyp_of_sections dims wdata.top (sdata.count hs) (sdata.width hs) hf.slots hf.lanes

end P1SolFmt.SolFormat
