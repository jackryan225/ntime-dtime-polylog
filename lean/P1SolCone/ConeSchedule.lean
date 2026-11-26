import P1SolCone.ConeFormat
import P1SolCone.FieldPrograms

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

abbrev PhaseDescriptor := ℕ × List Bits.Word

private def phaseIndices (ls : List (List Bits.Word)) : List ℕ :=
  capRange (ls.map (fun _ => ()), ls.length)

private theorem phaseIndices_eq (ls : List (List Bits.Word)) :
    phaseIndices ls = List.range ls.length := by
  simp only [phaseIndices, capRange, List.length_map, min_self]

private theorem phaseIndices_poly : Poly phaseIndices := by
  unfold phaseIndices
  exact ((Code.Poly.maps _ (Code.Poly.const ())).pair
    (poly_lengthNat (Code.Poly.identity (X := List (List Bits.Word))))).compose capRange_poly

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ)

/-- Chronological indices with formatted rows, delivered to the cone in reverse order. -/
def coneSchedule (w : Bits.Word) : List PhaseDescriptor :=
  let formats := conePhaseFormats Bt V a b d bigBias termBias w
  ((phaseIndices formats).zip formats).reverse

theorem coneSchedule_poly : Poly (coneSchedule Bt V a b d bigBias termBias) := by
  have zip := (phaseIndices_poly.pair Code.Poly.identity).compose poly_zipLists
  have rev : Easy (List.reverse (α := PhaseDescriptor)) := by fun_prop
  exact ((conePhaseFormats_poly Bt V a b d bigBias termBias).compose zip).compose rev.poly

theorem coneSchedule_eq (w : Bits.Word) :
    let D := coneDims Bt V a b d bigBias termBias (P1Batch.bval w)
    coneSchedule Bt V a b d bigBias termBias w = ((List.range D.top).map fun l => (l, phaseFormat D l)).reverse := by
  let D := coneDims Bt V a b d bigBias termBias (P1Batch.bval w)
  unfold coneSchedule
  dsimp only
  rw [phaseIndices_eq]
  change ((List.range (((List.range D.top).map (phaseFormat D)).length)).zip
    ((List.range D.top).map (phaseFormat D))).reverse = _
  simp only [List.length_map,List.length_range]
  apply congrArg List.reverse
  apply List.ext_getElem
  · simp <;> rfl
  · intros
    simp only [List.getElem_zip, List.getElem_map]
    rfl

end

end P1SolCone.SolCone
