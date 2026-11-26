import P1SolCone.ConeSchedule
import P1SolCone.PhaseStepExact
import P1SolCone.ConeStartTask
import P1SolCone.ConeFuel

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open private slotCap levelConstant from P1Wit.SpaceFacts

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

abbrev FullPhaseDescriptor := PhaseHeader × Tally × ℕ

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w
local notation "Wobs" w => Mbar B V a b (P1Batch.bval w)
local notation "Pad" w => conePad B.growthConstant (Wobs w)

def fullPhase (D : Dims) (clock pad : Tally) (width : ℕ) (u : List Bool) (l : ℕ) : FullPhaseDescriptor :=
  (actualPhaseHeader D u l 0 clock,pad,width)

def fullScheduleInput (p : QueryWords × Tally) : List FullPhaseDescriptor :=
  let clock := Clock p.1.1
  let m := P1Batch.bval p.1.2.1
  let width := Wobs p.1.1
  (coneSchedule B V a b d bigBias termBias p.1.1).map fun r =>
    ((clock,m,r.1,0,r.2),p.2,width)

theorem fullScheduleInput_poly : Poly (fullScheduleInput B V a b d bigBias termBias) := by
  let X := QueryWords × Tally
  have n : Poly (fun p : X => p.1.1) := Easy.fst.poly.fstCompose
  have h : Poly (fun p : X => (Clock p.1.1, P1Batch.bval p.1.2.1, p.2, Wobs p.1.1)) := by
    have m : Poly (fun p : X => P1Batch.bval p.1.2.1) := by unfold X QueryWords; fun_prop
    have w := poly_lengthNat (show Poly (fun p : X => tally (Wobs p.1.1)) from coneMbarRealizes B V a b n)
    have w' : Poly (fun p : X => Wobs p.1.1) := by simpa only [tally_length] using w
    exact (n.compose (coneReadClock_poly B V a b bigBias termBias)).pair (m.pair (Easy.snd.poly.pair w'))
  let Y := (Tally × ℕ × Tally × ℕ) × List PhaseDescriptor
  let pack (p : Y × PhaseDescriptor) : FullPhaseDescriptor :=
    ((p.1.1.1,p.1.1.2.1,p.2.1,0,p.2.2),p.1.1.2.2)
  have hp : Poly pack := by unfold pack Y FullPhaseDescriptor PhaseHeader PhaseDescriptor; fun_prop
  exact (h.pair (n.compose (coneSchedule_poly B V a b d bigBias termBias))).compose
    (poly_mapParameter Easy.snd.poly hp)

theorem fullSchedule_eq (q : Qry) (pad : Tally) :
    let w := bin q.1.length
    fullScheduleInput B V a b d bigBias termBias (smallQuery q,pad) =
      (List.range (Dobs w).top).reverse.map
        (fullPhase (Dobs w) (Clock w) pad (Wobs w) q.2.1) := by
  intro w
  unfold fullScheduleInput
  change ((coneSchedule B V a b d bigBias termBias w).map fun r =>
    ((Clock w, P1Batch.bval (bin q.2.1.length),r.1,0,r.2),pad,Wobs w)) = _
  rw [coneSchedule_eq B V a b d bigBias termBias, bval_bin, ← List.map_reverse, List.map_map]
  rfl

variable {F : Type} [CommRing F] [Fintype F]

def conePhaseStep (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F) (u : List Bool)
    (s : ConeStateCode F) (p : FullPhaseDescriptor) : ConeStateCode F :=
  stepPhaseCode (levelConstant S) (slotCap S) B.recordLimit (kernelFieldKeys (2 ^ S.expanderExponent))
    (cachedPhaseKernel shr ref (2 ^ S.expanderExponent)) u (p.1,p.2,s)

def checkedPhaseStep (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (u : List Bool) (w : Bits.Word) : CheckedTableState F → ℕ → CheckedTableState F :=
  advanceChecked (phaseAllowed (Dobs w) u B.recordLimit (Wobs w)) (phasePreimages (Dobs w) u)
    (phaseHalves (Dobs w) u)
    (phaseKernel (numericKernelValues shr ref) (Pad w) (2 ^ S.expanderExponent) (Dobs w) u)

set_option maxHeartbeats 1000000 in
theorem phaseFold_eq (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (u : List Bool) (w : Bits.Word) (ls : List ℕ) (hls : ∀ l ∈ ls, l < (Dobs w).top) (s : CheckedTableState F) :
    (ls.map (fullPhase (Dobs w) (Clock w) (Pad w) (Wobs w) u)).foldl
        (conePhaseStep B shr ref u) (encodeConeState s) =
      encodeConeState (ls.foldl (checkedPhaseStep B V a b d bigBias termBias shr ref u w) s) := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    have hl := hls l List.mem_cons_self
    have hp : 2 ^ (Wobs w) ≤ (Pad w).length := by
      rw [conePad,tally_length]
      apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      have hc : 1 ≤ B.growthConstant := (by decide : 1 ≤ 2).trans (le_max_left _ _)
      exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos hc))
    simp only [List.map_cons, List.foldl_cons]
    have hstep := phaseStep_exact B V a b d bigBias termBias shr ref (2 ^ S.expanderExponent)
      u w l hl (Pad w) (Wobs w) hp s
    change conePhaseStep B shr ref u (encodeConeState s)
      (fullPhase (Dobs w) (Clock w) (Pad w) (Wobs w) u l) = _ at hstep
    rw [hstep]
    exact ih (fun j hj => hls j (List.mem_cons_of_mem _ hj)) _

end

end P1SolCone.SolCone
