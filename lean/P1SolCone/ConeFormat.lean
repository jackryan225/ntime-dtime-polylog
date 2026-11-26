import P1SolFmt.Genuine
import P1SolCone.BudgetLayout
import P1SolCone.Wof
import P1SolCone.ProgramLists

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open scoped P1ChkFinal.AstraC10
open Carry Staff Strip
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1Wrap
open P1SolFmt.SolFigure P1SolFmt.SolFormat P1SolFmt.SolGeometry P1SolFmt.SolParameters

open private sumWords sumWords_poly value_sumWords from P1SolFmt.Offsets

noncomputable section

variable {X : Type} [Codec X] [Inhabited X]

/-- Section offsets on arbitrary small encoded input, computed by the verified format adder. -/
theorem coneOffsetFigure {D : X → Dims}
    (data : DimsFigures (inputRegime (X × Tally)) (fun p => D p.1))
    {s : X → ℕ} (hs : Realizes (inputRegime X) s) :
    Figure (inputRegime X) (fun x => (D x).off (s x)) := by
  have hi : Realizes (inputRegime (X × Tally)) (fun p => p.2.length) :=
    realizes_of_tally (show (inputRegime (X × Tally)).Has Prod.snd from Easy.snd.poly)
  obtain ⟨word, hw, he⟩ := (data.count hi).multiplied (data.width hi)
  have hindex := Code.Poly.identity.pair ((show Poly (fun x => tally (s x)) from hs).compose Iter.poly_line)
  let rows (x : X) := polyPush word (x, Iter.lineup (tally (s x)))
  have hrows : Poly rows := hindex.compose (Poly.push ((default : X)) ([] : Tally) hw)
  refine ⟨fun x => sumWords (rows x), hrows.compose sumWords_poly, fun x => ?_⟩
  change Bits.value (sumWords (polyPush word (x, Iter.lineup (tally (s x))))) = _
  rw [value_sumWords, Iter.lined]
  simp only [polyPush, List.map_ofFn, Function.comp_def, he, tally_length]
  exact offAt_ofFn _ _ _

private theorem poly_consWord {f : X → Bits.Word} {g : X → List Bits.Word}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x :: g x) :=
  (hf.pair hg).compose Poly.cons

private theorem poly_flatFixed {A : Type} (xs : List A) (f : A → X → List Bits.Word)
    (h : ∀ a ∈ xs, Poly (f a)) : Poly (fun x => xs.flatMap (fun a => f a x)) := by
  induction xs with
  | nil => exact Code.Poly.const []
  | cons a as ih =>
    exact (h a List.mem_cons_self).app (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private def phaseMemories : List Mem :=
  [.layout, .outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar, .width, .colour, .offset, .energy, .terms]

/-- The numerical header packet, with the C10 format's field order. -/
def phaseNumbers (D : Dims) (l : ℕ) : List ℕ :=
  [D.top, Nat.clog 2 (D.top + 1), D.fixedLen,
    (D.lv l).bases, (D.lv l).slots, (D.lv l).lanes, (D.lv l).laneW, (D.lv l).shrink.toNat,
    (D.lv l).termKeys, (D.lv l).termArity,
    (D.lv (l + 1)).bases, (D.lv (l + 1)).slots, (D.lv (l + 1)).lanes, (D.lv (l + 1)).laneW] ++
    (phaseMemories.flatMap fun m => [D.off (secLev l m), D.width (secLev l m)]) ++
    (phaseMemories.flatMap fun m => [D.off (secLev (l + 1) m), D.width (secLev (l + 1) m)])

def phaseFormat (D : Dims) (l : ℕ) : List Bits.Word := (phaseNumbers D l).map Nat.bits

/-- The C10 header row for a phase supplied as a unary index. -/
theorem conePhaseFormat_poly {D : X → Dims}
    (data : DimsFigures (inputRegime X) D)
    (secData : DimsFigures (inputRegime (X × Tally)) (fun p => D p.1))
    {l : X → ℕ} (hl : Realizes (inputRegime X) l) :
    Poly (fun x => phaseFormat (D x) (l x)) := by
  let fix := fun n => Realizes.fix (r := inputRegime X) n
  let ht := data.top
  let h0 := data.level hl
  let h1 := data.level (hl.plus (fix 1))
  have allsec : Realizes (inputRegime X) (fun x => (D x).nSec) :=
    (fix 7).plus ((fix 12).times (ht.plus (fix 1)))
  have hlen : Figure (inputRegime X) (fun x => (D x).fixedLen) := coneOffsetFigure secData allsec
  have hbits : Figure (inputRegime X) (fun x => Nat.clog 2 ((D x).top + 1)) :=
    Figure.of_spoken ((Figure.of_spoken ht).added (Figure.natural 1)).short_log
  have head : Poly (fun x =>
      ([ (D x).top, Nat.clog 2 ((D x).top + 1), (D x).fixedLen,
         ((D x).lv (l x)).bases, ((D x).lv (l x)).slots, ((D x).lv (l x)).lanes, ((D x).lv (l x)).laneW,
         ((D x).lv (l x)).shrink.toNat, ((D x).lv (l x)).termKeys, ((D x).lv (l x)).termArity,
         ((D x).lv (l x + 1)).bases, ((D x).lv (l x + 1)).slots, ((D x).lv (l x + 1)).lanes,
         ((D x).lv (l x + 1)).laneW ]).map Nat.bits) := by
    simp only [List.map_cons, List.map_nil]
    exact poly_consWord (figure_poly (Figure.of_spoken ht)) <|
      poly_consWord (figure_poly hbits) <| poly_consWord (figure_poly hlen) <|
      poly_consWord (figure_poly h0.bases) <| poly_consWord (figure_poly h0.slots) <|
      poly_consWord (figure_poly h0.lanes) <| poly_consWord (figure_poly h0.laneW) <|
      poly_consWord (figure_poly h0.shrink) <| poly_consWord (figure_poly h0.termKeys) <|
      poly_consWord (figure_poly h0.termArity) <| poly_consWord (figure_poly h1.bases) <|
      poly_consWord (figure_poly h1.slots) <| poly_consWord (figure_poly h1.lanes) <|
      poly_consWord (figure_poly h1.laneW) (Code.Poly.const [])
  have sections {j : X → ℕ} (hj : Realizes (inputRegime X) j) :
      Poly (fun x => (phaseMemories.flatMap fun m =>
        [(D x).off (secLev (j x) m), (D x).width (secLev (j x) m)]).map Nat.bits) := by
    have one (m : Mem) : Poly (fun x =>
        [Nat.bits ((D x).off (secLev (j x) m)), Nat.bits ((D x).width (secLev (j x) m))]) := by
      have hsec : Realizes (inputRegime X) (fun x => secLev (j x) m) :=
        ((fix 5).plus ((fix 12).times hj)).plus (fix m.toNat)
      exact poly_consWord (figure_poly (coneOffsetFigure secData hsec))
        (poly_consWord (figure_poly (data.width hsec)) (Code.Poly.const []))
    simpa only [List.map_flatMap, List.map_cons, List.map_nil] using
      (poly_flatFixed phaseMemories _ (fun m _ => one m))
  have hs := (head.app (sections hl)).app (sections (hl.plus (fix 1)))
  simpa only [phaseFormat, phaseNumbers, List.map_append] using hs

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ)

/-- Clock and header parameters shared by cone correctness and the program. -/
abbrev coneDims (n : ℕ) : Dims :=
  genuineDims B (P1Int.P11.portConsts B) (P1Int.toOAI V) 1 (P1Int.lpTime a b n)
    (a * (n ^ 2 + 1)) d bigBias termBias

theorem coneTimeFigure {n : X → Bits.Word} (hn : Poly n) :
    Figure (inputRegime X) (fun x => P1Int.lpTime a b (P1Batch.bval (n x))) := by
  simpa only [P1Wrap.W3.lpTime_eq] using
    figure_time a b (P1SolFmt.SolFigure.Figure.pullback hn figure_bval)

theorem coneDimsFigures {n : X → Bits.Word} (hn : Poly n) :
    DimsFigures (inputRegime X) (fun x => coneDims B V a b d bigBias termBias (P1Batch.bval (n x))) := by
  let num := fun m => Figure.natural (r := inputRegime X) m
  have v := P1SolFmt.SolFigure.Figure.pullback hn figure_bval
  have hg : Figure (inputRegime X) (fun x => a * (P1Batch.bval (n x) ^ 2 + 1)) := by
    simpa only [pow_two] using (num a).multiplied ((v.multiplied v).added (num 1))
  exact genuineDims_figures B (P1Int.P11.portConsts B) (P1Int.toOAI V)
    1 d bigBias termBias (coneTimeFigure a b hn) hg

/-- Chronological headers of the compression passes, excluding the terminal row. -/
def conePhaseFormats (w : Bits.Word) : List (List Bits.Word) :=
  let D := coneDims B V a b d bigBias termBias (P1Batch.bval w)
  (List.range D.top).map (phaseFormat D)

theorem conePhaseFormats_poly : Poly (conePhaseFormats B V a b d bigBias termBias) := by
  let D := fun w : Bits.Word => coneDims B V a b d bigBias termBias (P1Batch.bval w)
  have ht : Poly (fun w : Bits.Word => tally ((D w).top)) :=
    (coneDimsFigures B V a b d bigBias termBias Code.Poly.identity).top
  have hi : Realizes (inputRegime (Bits.Word × Tally)) (fun x => x.2.length) :=
    realizes_of_tally (show (inputRegime (Bits.Word × Tally)).Has Prod.snd from Easy.snd.poly)
  have hh := conePhaseFormat_poly
    (coneDimsFigures B V a b d bigBias termBias (Easy.fst.poly : Poly (Prod.fst : Bits.Word × Tally → Bits.Word)))
    (coneDimsFigures B V a b d bigBias termBias (show Poly (fun p : (Bits.Word × Tally) × Tally => p.1.1) from
      (Easy.fst.compose Easy.fst).poly)) hi
  have h := (Code.Poly.identity.pair (ht.compose Iter.poly_line)).compose
    (Poly.push ([] : Bits.Word) ([] : Tally) hh)
  convert h using 1
  funext w
  simp only [conePhaseFormats, polyPush, Iter.lined, List.map_ofFn, Function.comp_def, tally_length, D]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intros
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- The final row supplies the incidence fields, and the C11 format supplies the prefix section. -/
def terminalFormats (w : Bits.Word) : List Bits.Word × List Bits.Word :=
  let D := coneDims B V a b d bigBias termBias (P1Batch.bval w)
  (phaseFormat D D.top, P1ChkFinal.fmt D)

theorem terminalFormats_poly : Poly (terminalFormats B V a b d bigBias termBias) := by
  have main := coneDimsFigures B V a b d bigBias termBias (Code.Poly.identity (X := Bits.Word))
  have aux := coneDimsFigures B V a b d bigBias termBias
    (Easy.fst.poly : Poly (Prod.fst : Bits.Word × Tally → Bits.Word))
  have hC11 := fmtHyp_genuine B (P1Int.P11.portConsts B) (P1Int.toOAI V)
    1 a b d bigBias termBias
  exact (conePhaseFormat_poly main aux main.top).pair hC11

section FormatLookup

open P1ChkFinal.AstraC10

def packetNat (row : List Bits.Word) (i : ℕ) : ℕ :=
  P1Batch.bval (readAt [] row i)

@[fun_prop] theorem packetNat_poly {U : Type} [Codec U] {r : U → List Bits.Word} {i : U → ℕ}
    (hr : Poly r) (hi : Poly i) : Poly (fun x => packetNat (r x) (i x)) :=
  poly_bval (poly_readAt [] hr hi)

theorem packetNat_phaseFormat (D : Dims) (l i : ℕ) :
    packetNat (phaseFormat D l) i = readAt 0 (phaseNumbers D l) i := by
  simp only [packetNat, phaseFormat, readAt, List.getElem?_map]
  cases (phaseNumbers D l)[i]? with
  | none => rfl
  | some value =>
    have hv : P1Batch.bval value.bits = value := by rw [← P1ChkFinal.bin_eq_bits, P1ChkFinal.bval_bin]
    exact hv

/-- The offset and width for one old-row field in a numerical phase packet. -/
def packetSection (row : List Bits.Word) (m : ℕ) : ℕ × ℕ :=
  (packetNat row (14 + 2 * m), packetNat row (15 + 2 * m))

theorem packetSection_poly :
    Poly (fun p : List Bits.Word × ℕ => packetSection p.1 p.2) := by
  unfold packetSection
  fun_prop

theorem packetSection_phaseFormat (D : Dims) (l : ℕ) (m : Mem) :
    packetSection (phaseFormat D l) m.toNat = (D.off (secLev l m), D.width (secLev l m)) := by
  unfold packetSection
  rw [packetNat_phaseFormat, packetNat_phaseFormat]
  cases m <;> rfl

end FormatLookup

end

end P1SolCone.SolCone
