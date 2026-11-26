import P1SolFmt.Assembly
import P1Wit.Decode
import P1SolFmt.FigureTools
import P1SolFmt.Length
import P1SolFmt.Offsets

namespace P1SolFmt.SolFormat

open OAI.Computability.IntegerMultiplication
open Code Carry Staff Strip P1Wit SolFigure

theorem figure_bval : Figure (inputRegime Bits.Word) P1Batch.bval := by
  refine ⟨id, Poly.identity, fun w => ?_⟩
  change Bits.value w = P1Batch.bval w
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp only [Bits.value_cons, Bits.d0, Bits.d1, P1Batch.bval,
      Bool.toNat_false, Bool.toNat_true, ih]

private theorem cut_eq_bits (w : Bits.Word) : Carry.cut w = Nat.bits (Bits.value w) := by
  obtain ⟨hv, _, hshape⟩ := cut_v w
  have hlen := measure (Bits.value w + 1) (Carry.cut w) (by rw [hv, Nat.add_sub_cancel]) hshape
  apply Bits.word_inject _ _
  · rw [← hlen, SolBits.bits_length_eq_clog_succ]
  · rw [hv, ← SolLength.born_eq_bits, birthValue]

theorem figure_poly {X : Type} [Codec X] {f : X → ℕ} (hf : Figure (inputRegime X) f) :
    Poly (fun x => Nat.bits (f x)) := by
  obtain ⟨w, hw, hv⟩ := hf
  have hw' : Poly w := hw
  simpa only [cut_eq_bits, hv] using hw'.compose polyCut

private theorem index_poly {s : Bits.Word → ℕ}
    (hs : Realizes (inputRegime Bits.Word) s)
    {f : Bits.Word → ℕ → ℕ} (hf : Figure (inputRegime (Bits.Word × Tally))
      (fun p => f p.1 p.2.length)) :
    Poly (fun x => Nat.bits (f x (s x))) := by
  have hs' : Poly (fun x => tally (s x)) := hs
  have h := (Poly.identity.pair hs').compose (figure_poly hf)
  simpa only [tally_length] using h

private theorem offset_poly {d : Bits.Word → Dims} {s : Bits.Word → ℕ}
    (hs : Realizes (inputRegime Bits.Word) s)
    (hf : Figure (inputRegime (Bits.Word × Tally))
      (fun p => (d p.1).count p.2.length * (d p.1).width p.2.length)) :
    Poly (fun x => Nat.bits ((d x).off (s x))) := by
  have hs' : Poly (fun x => tally (s x)) := hs
  obtain ⟨word, hword, hv⟩ := hf
  have hword' : Poly word := hword
  exact figure_poly (offsets_with_value hs' hword' hv : Figure (inputRegime Bits.Word) _)

private theorem format_words_of_sections (d : Bits.Word → Dims)
    (hTop : Realizes (inputRegime Bits.Word) (fun w => (d w).top))
    (hCount : Figure (inputRegime (Bits.Word × Tally)) (fun q => (d q.1).count q.2.length))
    (hWidth : Figure (inputRegime (Bits.Word × Tally)) (fun q => (d q.1).width q.2.length))
    (hSlots : Figure (inputRegime Bits.Word) (fun w => ((d w).lv (d w).top).slots))
    (hLanes : Figure (inputRegime Bits.Word) (fun w => ((d w).lv (d w).top).lanes)) :
    Poly (fun w => P1ChkFinal.fmt (d w)) := by
  let const := fun n => Realizes.fix (r := inputRegime Bits.Word) n
  have hLevels := (const 12).times (hTop.plus (const 1))
  have hOmega : Realizes (inputRegime Bits.Word) (fun w => (d w).secOmega) :=
    (const 5).plus hLevels
  have hChain : Realizes (inputRegime Bits.Word) (fun w => (d w).secChain) :=
    (const 6).plus hLevels
  have hWidthSec : Realizes (inputRegime Bits.Word) (fun w => secLev (d w).top .width) :=
    ((const 5).plus ((const 12).times hTop)).plus (const 7)
  have hAll : Realizes (inputRegime Bits.Word) (fun w => (d w).nSec) :=
    (const 7).plus hLevels
  have hFin : Poly (fun w => Nat.bits (P1ChkFinal.finN (d w))) := by
    have e (w : Bits.Word) : (d w).count (d w).secOmega = P1ChkFinal.finN (d w) := by
      simp only [Dims.count, Dims.kind_Omega, P1ChkFinal.finN]
    simpa only [e] using index_poly (f := fun w => (d w).count) hOmega hCount
  have hArcs : Poly (fun w => Nat.bits (P1ChkFinal.finArcs (d w))) :=
    figure_poly (hLanes.multiplied hSlots)
  have hChainLen : Poly (fun w => Nat.bits (d w).chainLen) := by
    have e (w : Bits.Word) : (d w).count (d w).secChain = (d w).chainLen := by
      simp only [Dims.count, Dims.kind_chain]
    simpa only [e] using index_poly (f := fun w => (d w).count) hChain hCount
  have hExt : Figure (inputRegime (Bits.Word × Tally))
      (fun p => (d p.1).count p.2.length * (d p.1).width p.2.length) :=
    hCount.multiplied hWidth
  exact format_words_poly_of d hFin hArcs (figure_poly hSlots) (figure_poly hLanes)
    (offset_poly (d := d) hOmega hExt) (index_poly (f := fun w => (d w).width) hOmega hWidth)
    (offset_poly (d := d) hWidthSec hExt) (index_poly (f := fun w => (d w).width) hWidthSec hWidth)
    (offset_poly (d := d) hChain hExt) (index_poly (f := fun w => (d w).width) hChain hWidth)
    (offset_poly (d := d) hAll hExt) hChainLen

/-- Produce the exact check format from a polynomial-time section table and final dimensions. -/
theorem fmtHyp_of_sections (dims : ℕ → Dims)
    (hTop : Realizes (inputRegime Bits.Word) (fun w => (dims (P1Batch.bval w)).top))
    (hCount : Figure (inputRegime (Bits.Word × Tally))
      (fun q => (dims (P1Batch.bval q.1)).count q.2.length))
    (hWidth : Figure (inputRegime (Bits.Word × Tally))
      (fun q => (dims (P1Batch.bval q.1)).width q.2.length))
    (hSlots : Figure (inputRegime Bits.Word)
      (fun w => let d := dims (P1Batch.bval w); (d.lv d.top).slots))
    (hLanes : Figure (inputRegime Bits.Word)
      (fun w => let d := dims (P1Batch.bval w); (d.lv d.top).lanes)) :
    P1ChkFinal.FmtHyp dims :=
  format_words_of_sections (fun w => dims (P1Batch.bval w)) hTop hCount hWidth hSlots hLanes

#print axioms fmtHyp_of_sections

end P1SolFmt.SolFormat
