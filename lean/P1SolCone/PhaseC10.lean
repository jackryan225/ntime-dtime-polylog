import P1SolC10P.Decision
import P1SolCone.KernelBallProgram
import P1SolCone.PhaseStage

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

theorem phaseFormat_eq_fmt10 (D : Dims) (l : ℕ) : phaseFormat D l = P1C10.fmt10 D l := by
  unfold phaseFormat phaseNumbers P1C10.fmt10
  have h : (D.lv l).shrink.toNat = (if (D.lv l).shrink then 1 else 0) := by
    cases (D.lv l).shrink <;> rfl
  rw [h]
  rfl

theorem phaseHeader_eq_C10 (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) :
    actualPhaseHeader D u l y clock = P1SolC10P.SolC10prog.actualHead D u l y clock := by
  unfold actualPhaseHeader P1SolC10P.SolC10prog.actualHead
  rw [phaseFormat_eq_fmt10]

def kernelFieldKeys (dH : ℕ) (p : PhaseHeader × ℕ) : List FieldKey := P1SolC10P.SolC10prog.oldKeyList dH p.1 p.2

theorem kernelFieldKeys_poly (dH : ℕ) : Poly (kernelFieldKeys dH) := P1SolC10P.SolC10prog.poly_oldKeyList dH

theorem kernelFieldKeys_bounds (dH : ℕ) (h : PhaseHeader) (y : ℕ) (k : FieldKey)
    (hk : k ∈ kernelFieldKeys dH (h,y)) : k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length :=
  P1SolC10P.SolC10prog.oldKeyList_bounds dH h y hk

theorem kernelFieldKeys_read (dH : ℕ) (u : List Bool) (h : PhaseHeader) (ys : List ℕ)
    (y : ℕ) (hy : y ∈ ys) (k : FieldKey) (hk : k ∈ kernelFieldKeys dH (h,y)) :
    P1SolC10P.SolC10prog.tableRead (rawRoundCache (kernelFieldKeys dH) u h ys) k = P1SolC10P.SolC10prog.fieldAt u k := by
  unfold rawRoundCache
  rw [fetchPhaseFields_eq_map]
  have he (q : FieldKey) : phaseFieldAt u q = P1SolC10P.SolC10prog.fieldAt u q := by
    unfold phaseFieldAt P1SolC10P.SolC10prog.fieldAt
    exact P1SolC10P.SolC10prog.bitsVal_eq_bval _
  simp only [he]
  exact P1SolC10P.SolC10prog.tableRead_map _ (mem_rawRoundKeys_extra (kernelFieldKeys dH) hy hk)

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ)

theorem coneClock_fits_C10 (w : Bits.Word) (l : ℕ)
    (hl : l < (coneDims B V a b d bigBias termBias (P1Batch.bval w)).top) :
    P1SolC10P.SolC10prog.Fits (coneDims B V a b d bigBias termBias (P1Batch.bval w)) l
      (coneReadClock B V a b bigBias termBias w) := by
  let n := P1Batch.bval w
  let D := coneDims B V a b d bigBias termBias n
  let clk := coneReadClock B V a b bigBias termBias w
  have ho := coneDims_rowBounds B V a b d bigBias termBias n l hl.le
  have hn := coneDims_rowBounds B V a b d bigBias termBias n (l+1) hl
  have hslot0 : P1C10.slotBits D l = (D.lv l).slotW := by
    unfold P1C10.slotBits
    rw [ho.slots_eq, Nat.log_pow (by decide : 1 < 2)]
  have hslot1 : P1C10.slotBits D (l+1) = (D.lv (l+1)).slotW := by
    unfold P1C10.slotBits
    rw [hn.slots_eq, Nat.log_pow (by decide : 1 < 2)]
  have haxis (j : ℕ) (hj : j ≤ D.top) :
      (D.lv j).lanes * (D.lv j).slots ≤ clk.length :=
    (coneAxisClock_fits B V a b d bigBias termBias w j hj).trans (coneReadClock_axes B V a b bigBias termBias w)
  have hs (j : ℕ) (hj : j ≤ D.top) : (D.lv j).slots ≤ clk.length := by
    have e := (coneDims_rowBounds B V a b d bigBias termBias n j hj).lanes_eq
    exact (Nat.le_mul_of_pos_left _ (by rw [e]; exact Nat.two_pow_pos _)).trans (haxis j hj)
  have hlane : 2 ^ (D.lv (l+1)).laneW ≤ clk.length := by
    rw [← hn.lanes_eq]
    exact (Nat.le_mul_of_pos_right _ (by rw [hn.slots_eq]; exact Nat.two_pow_pos _)).trans (haxis (l+1) hl)
  have sh : 2 ^ packingLaneBits (P1C10.slotBits D l) (D.lv (l+1)).laneW ≤ clk.length := by
    rw [hslot0]
    exact coneReadClock_shrinkLanes B V a b d bigBias termBias w l hl
  change P1SolC10P.SolC10prog.Fits D l clk
  refine ⟨?_, ?_, hlane, sh, ?_, ?_, ?_⟩
  · rw [hslot0, ← ho.slots_eq]
    exact hs l hl.le
  · rw [hslot1, ← hn.slots_eq]
    exact hs (l+1) hl
  · apply le_trans _ sh
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    unfold packingLaneBits
    omega
  · apply le_trans _ sh
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    unfold packingLaneBits
    omega
  · intro next m
    have h (i : ℕ) (hi : i ≤ D.top) : D.width (secLev i m) ≤ clk.length :=
      (coneLevelWidth_le B V a b d bigBias termBias n i hi m).trans
        (coneReadClock_width B V a b bigBias termBias w)
    cases next
    · exact h l hl.le
    · exact h (l+1) hl

end P1SolCone.SolCone
