import P1SolCone.TerminalTask
import P1SolCone.PhaseGeometry

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wrap P1Int P1Int.P11 P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10
open P1SolFmt.SolFigure
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly poly_le

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k}
variable (Bt : S.Templates) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

def coneTerminalHeader (p : Bits.Word × Bits.Word × Bits.Word) : TerminalHeader :=
  let n := P1Batch.bval p.1
  let D := coneDims Bt V a b d bigBias termBias n
  actualTerminalHeader D (P1Batch.bval p.2.1) (Mbar Bt V a b n) (P1Batch.bval p.2.2)
    (coneReadClock Bt V a b bigBias termBias p.1)

theorem coneTerminalHeader_poly : Poly (coneTerminalHeader Bt V a b d bigBias termBias) := by
  let A := Bits.Word × Bits.Word × Bits.Word
  have hN : Poly (fun p : A => p.1) := Easy.fst.poly
  have axis := hN.compose (coneReadClock_poly Bt V a b bigBias termBias)
  have tallyW := coneMbarRealizes Bt V a b hN
  have width := poly_lengthNat (show Poly (fun p : A => tally (Mbar Bt V a b (P1Batch.bval p.1))) from tallyW)
  have width' : Poly (fun p : A => Mbar Bt V a b (P1Batch.bval p.1)) := by
    simpa only [tally_length] using width
  have m : Poly (fun p : A => P1Batch.bval p.2.1) := by unfold A; fun_prop
  have v : Poly (fun p : A => P1Batch.bval p.2.2) := by unfold A; fun_prop
  exact axis.pair (m.pair (width'.pair (v.pair (hN.compose (terminalFormats_poly Bt V a b d bigBias termBias)))))

theorem coneTerminalHeader_width (p : Bits.Word × Bits.Word × Bits.Word) (f : FieldKey) (hf : f.1 < 13) :
    P1Batch.bval (terminalFieldReq (coneTerminalHeader Bt V a b d bigBias termBias p) f).2 ≤
      coneFieldWidth Bt V a b bigBias termBias (P1Batch.bval p.1) := by
  let n := P1Batch.bval p.1
  let D := coneDims Bt V a b d bigBias termBias n
  unfold coneTerminalHeader
  dsimp only
  rw [terminalFieldReq_eq _ _ _ _ _ _ hf]
  change P1Batch.bval (bin (D.width (terminalPhysicalKey D f).1)) ≤ _
  rw [bval_bin]
  unfold terminalPhysicalKey
  by_cases hf' : f.1 = 12
  · simp only [hf', ite_true]
    exact coneOmegaWidth_le Bt V a b d bigBias termBias n
  · simp only [hf', ite_false]
    exact coneLevelWidth_le Bt V a b d bigBias termBias n D.top le_rfl _

/-- The outer Wof check uses chainLen while the payload reader also checks the terminal product. -/
def coneTerminalGate (h : TerminalHeader) : Bool :=
  decide (packetNat h.2.2.2.2.1 2 ≤ h.2.1) &&
    decide (h.2.2.2.1 < packetNat h.2.2.2.2.2 11 - 1)

theorem coneTerminalGate_poly : Poly coneTerminalGate := by
  unfold coneTerminalGate
  have u : Poly (fun h : TerminalHeader => decide (packetNat h.2.2.2.2.1 2 ≤ h.2.1)) := by fun_prop
  have v : Poly (fun h : TerminalHeader => decide (h.2.2.2.1 < packetNat h.2.2.2.2.2 11 - 1)) := by fun_prop
  exact (u.pair v).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

theorem coneTerminalGate_eq (D : Dims) (m w v : ℕ) (clock : Tally) :
    coneTerminalGate (actualTerminalHeader D m w v clock) = decide (D.fixedLen ≤ m ∧ v < finP D) := by
  have hfix : packetNat (phaseFormat D D.top) 2 = D.fixedLen := by rw [packetNat_phaseFormat]; rfl
  have hchain : packetNat (fmt D) 11 = D.chainLen := by
    change P1Batch.bval D.chainLen.bits = _
    rw [← bin_eq_bits, bval_bin]
  apply Bool.eq_iff_iff.mpr
  unfold coneTerminalGate
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  change (packetNat (phaseFormat D D.top) 2 ≤ m ∧ v < packetNat (fmt D) 11 - 1) ↔ _
  rw [hfix,hchain]
  rfl

end

end P1SolCone.SolCone
