import P1SolCone.OnePhaseTask
import P1SolCone.PhaseKernelMatch
import P1SolCone.ConeTraceBounds

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open private slotCap levelConstant from P1Wit.SpaceFacts

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
variable {F : Type} [CommRing F] [Fintype F]

local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w

def numericKernelValues (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F) : KernelValues F :=
  ⟨fun i _ z => (shr (i,z)).val, fun z => (ref z).val⟩

theorem phaseStep_exact (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (dH : ℕ) (u : List Bool) (w : Bits.Word) (l : ℕ) (hl : l < (Dobs w).top)
    (pad : Tally) (cap : ℕ) (hpad : 2 ^ cap ≤ pad.length) (s : CheckedTableState F) :
    let h := actualPhaseHeader (Dobs w) u l 0 (Clock w)
    stepPhaseCode (levelConstant S) (slotCap S) B.recordLimit (kernelFieldKeys dH)
      (cachedPhaseKernel shr ref dH) u (h,(pad,cap),encodeConeState s) =
    encodeConeState (advanceChecked (phaseAllowed (Dobs w) u B.recordLimit cap)
      (phasePreimages (Dobs w) u) (phaseHalves (Dobs w) u)
      (phaseKernel (numericKernelValues shr ref) pad dH (Dobs w) u) s l) := by
  intro h
  cases s with
  | none => rfl
  | some val =>
    obtain ⟨keys,levels⟩ := val
    let D := Dobs w
    let ctx := phaseLocalOf (levelConstant S) (kernelFieldKeys dH) u h pad cap keys
    change advanceConeCode B.recordLimit (localAllowed (levelConstant S) B.recordLimit)
      (localParents (levelConstant S)) (localHalves (slotCap S)) (cachedPhaseKernel shr ref dH)
      (ctx,encodeConeState (some (keys,levels))) = _
    refine advanceConeCode_eq _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun q hq => phaseLocalOf_allowed B V a b d bigBias termBias (kernelFieldKeys dH) u w l hl keys q hq pad cap)
      (fun q ok => (phaseAllowed_limits D u B.recordLimit cap l q ok).1)
      (fun q hq => phaseLocalOf_parents B V a b d bigBias termBias (kernelFieldKeys dH) u w l hl keys q hq pad cap)
      ?_ ?_
    · intro q hq ok pos hpos
      let widths := readHalfWidths D u l pos
      have eq : localWidths (ctx,pos) = widths :=
        phaseLocalOf_widths B V a b d bigBias termBias (kernelFieldKeys dH) u w l hl keys q hq pos hpos pad cap
      have hw := (phaseAllowed_limits D u B.recordLimit cap l q ok).2 pos hpos
      obtain ⟨hout,hin⟩ := widthsWithin_fields cap widths hw
      have slots := (coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le).slots_le
      obtain ⟨h₁,h₂⟩ := readHalfWidths_lengths D u l pos
      change fueledHalves (slotCap S) (pad, localWidths (ctx,pos)) = halfCodes widths
      rw [eq]
      refine fueledHalves_eq _ _ _ (h₁.le.trans slots) (h₂.le.trans slots) (fun t ht => ?_)
      apply le_trans _ hpad
      apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      rcases List.mem_append.mp ht with hmem | hmem
      · exact hout t hmem
      · exact hin t hmem
    · intro q hq ps _
      exact cachedPhaseKernel_eq B V a b d bigBias termBias shr ref dH u w l hl keys q hq pad cap ps

end

end P1SolCone.SolCone
