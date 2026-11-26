import P1SolCone.ConeGeometry

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open P1Wrap P1Int P1Int.P11 P1Wit P1Wit.SolSpace
open P1SolFmt.SolFigure P1SolFmt.SolParameters
open private slotCap levelConstant from P1Wit.SpaceFacts

variable {k : Type} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

theorem conePhaseShape_eq (n l : ℕ) (hl : l < (coneDims B V a b d bigBias termBias n).top) :
    let D := coneDims B V a b d bigBias termBias n
    phaseShape D l = ⟨(D.lv l).slotW, (D.lv (l + 1)).slotW, (D.lv l).laneW, (D.lv (l + 1)).laneW⟩ := by
  let s := coneDims_rowBounds B V a b d bigBias termBias n l hl.le
  let s' := coneDims_rowBounds B V a b d bigBias termBias n (l+1) hl
  exact phaseShape_eq _ _ _ _ _ _ s.slots_eq s'.slots_eq s.lanes_eq s'.lanes_eq

theorem conePhaseShape_kind (n l : ℕ) (hl : l < (coneDims B V a b d bigBias termBias n).top) :
    let D := coneDims B V a b d bigBias termBias n
    (phaseShape D l).isShrink = (D.lv l).shrink := by
  let D := coneDims B V a b d bigBias termBias n
  let X := D.lv l
  let Y := D.lv (l+1)
  change (phaseShape D l).isShrink = X.shrink
  rw [conePhaseShape_eq B V a b d bigBias termBias n l hl]
  have hg := (coneDims_step B V a b d bigBias termBias n l hl).loss
  change X.laneW = (if X.shrink then _ else _) + Y.laneW at hg
  cases hk : X.shrink
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hg
    rw [show (D.lv l).laneW = X.slotW + Y.laneW from hg]
    exact shape_refresh _ _ _
  · simp only [hk, ↓reduceIte] at hg
    have he : (D.lv l).laneW = packingLaneBits X.slotW Y.laneW := by
      have hzero : X.laneW = packingLaneBits X.slotW 0 + Y.laneW := hg
      refine hzero.trans ?_
      unfold packingLaneBits
      omega
    rw [he]
    exact shape_shrink _ _ _

/-- A uniform field width bound, in unary clock units. -/
noncomputable def coneFieldWidth (n : ℕ) : ℕ :=
  2 + (bigBias + 6 * Params.lam (lpTime a b n)) + (termBias + Mbar B V a b n + 1) +
    levelConstant S + Params.h (lpTime a b n)

theorem coneFieldWidth_realizes {A : Type} [Codec A] [Inhabited A] {w : A → Bits.Word}
    (hw : Poly w) :
    Realizes (inputRegime A) (fun x => coneFieldWidth B V a b bigBias termBias (P1Batch.bval (w x))) := by
  let r := inputRegime A
  let fix := fun n => Realizes.fix (r := r) n
  have time := coneTimeFigure a b hw
  simpa only [coneFieldWidth, Nat.add_assoc] using (((fix 2).plus ((fix bigBias).plus ((fix 6).times (realizes_lam time)))).plus
    (((fix termBias).plus (coneMbarRealizes B V a b hw)).plus (fix 1))).plus
    ((fix (levelConstant S)).plus (realizes_h time))

theorem coneLevelWidth_le (n l : ℕ) (hl : l ≤ (coneDims B V a b d bigBias termBias n).top) (m : Mem) :
    (coneDims B V a b d bigBias termBias n).width (secLev l m) ≤ coneFieldWidth B V a b bigBias termBias n := by
  let D := coneDims B V a b d bigBias termBias n
  let W := Mbar B V a b n
  have sh := coneDims_rowBounds B V a b d bigBias termBias n l hl
  have hW : D.wW ≤ termBias + W + 1 := by
    change termBias + Nat.clog 2 (W + 1) ≤ _
    have hlog : Nat.clog 2 (W + 1) ≤ W + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    omega
  have hbig : D.bigW = bigBias + 6 * Params.lam (lpTime a b n) := rfl
  rw [D.width_secLev m hl]
  have hslot : (D.lv l).slotW ≤ levelConstant S := sh.slotW_le
  have hlane : (D.lv l).laneW ≤ Params.h (lpTime a b n) := sh.laneW_le
  have hcol : (D.lv l).colW ≤ levelConstant S := sh.colW_le
  have htag : (D.lv l).tagW ≤ levelConstant S := sh.tagW_le
  cases m <;> simp only [Dims.levWidth, coneFieldWidth, hbig] <;> omega

theorem coneOmegaWidth_le (n : ℕ) :
    let D := coneDims B V a b d bigBias termBias n
    D.width D.secOmega ≤ coneFieldWidth B V a b bigBias termBias n := by
  let D := coneDims B V a b d bigBias termBias n
  have he : D.kind D.secOmega = .Omega := by
    unfold Dims.kind Dims.secOmega
    have h : 0 < 12 * (D.top + 1) := by omega
    simp only [show 5 + 12 * (D.top + 1) ≠ 0 by omega,
      show 5 + 12 * (D.top + 1) ≠ 1 by omega, show 5 + 12 * (D.top + 1) ≠ 2 by omega,
      show 5 + 12 * (D.top + 1) ≠ 3 by omega, show 5 + 12 * (D.top + 1) ≠ 4 by omega,
      lt_self_iff_false, ite_false, ite_true]
  change D.width D.secOmega ≤ _
  rw [Dims.width, he]
  change bigBias + 6 * Params.lam (lpTime a b n) ≤ _
  unfold coneFieldWidth
  omega

private theorem packingTagBits_mono : Monotone packingTagBits := by
  intro x y h
  unfold packingTagBits
  apply Nat.add_le_add_right
  apply Nat.log_mono_right
  gcongr

theorem packingLaneBits_mono_left {x y : ℕ} (h : x ≤ y) (g : ℕ) :
    packingLaneBits x g ≤ packingLaneBits y g := by
  have hd := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h
  have ht := packingTagBits_mono hd
  unfold packingLaneBits
  omega

/-- The scan clock pays both lane alternatives of the C10 code and every field width. -/
noncomputable def coneReadClock (w : Bits.Word) : Tally :=
  tally (2 ^ packingLaneBits (levelConstant S) 0 * (coneAxisClock S a b w).length +
    coneFieldWidth B V a b bigBias termBias (P1Batch.bval w))

theorem coneReadClock_poly : Poly (coneReadClock B V a b bigBias termBias) := by
  have axes := realizes_of_tally
    (show (inputRegime Bits.Word).Has (coneAxisClock S a b) from coneAxisClock_poly (S := S) a b)
  exact ((Realizes.fix (r := inputRegime Bits.Word) (2 ^ packingLaneBits (levelConstant S) 0)).times axes).plus
    (coneFieldWidth_realizes B V a b bigBias termBias Code.Poly.identity)

theorem coneReadClock_width (w : Bits.Word) :
    coneFieldWidth B V a b bigBias termBias (P1Batch.bval w) ≤
      (coneReadClock B V a b bigBias termBias w).length := by simp [coneReadClock, tally_length]

theorem coneReadClock_axes (w : Bits.Word) :
    (coneAxisClock S a b w).length ≤ (coneReadClock B V a b bigBias termBias w).length := by
  rw [coneReadClock, tally_length]
  exact (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans (Nat.le_add_right _ _)

theorem coneReadClock_shrinkLanes (w : Bits.Word) (l : ℕ)
    (hl : l < (coneDims B V a b d bigBias termBias (P1Batch.bval w)).top) :
    let D := coneDims B V a b d bigBias termBias (P1Batch.bval w)
    2 ^ packingLaneBits (D.lv l).slotW (D.lv (l+1)).laneW ≤
      (coneReadClock B V a b bigBias termBias w).length := by
  let n := P1Batch.bval w
  let D := coneDims B V a b d bigBias termBias n
  have old := coneDims_rowBounds B V a b d bigBias termBias n l hl.le
  have child := coneDims_rowBounds B V a b d bigBias termBias n (l+1) hl
  have hchild : 2 ^ (D.lv (l+1)).laneW ≤ (coneAxisClock S a b w).length := by
    rw [← child.lanes_eq]
    exact (Nat.le_mul_of_pos_right _ (by rw [child.slots_eq]; exact Nat.two_pow_pos _)).trans
      (coneAxisClock_fits B V a b d bigBias termBias w (l+1) hl)
  have hE := packingLaneBits_mono_left old.slotW_le 0
  calc
    2 ^ packingLaneBits (D.lv l).slotW (D.lv (l+1)).laneW =
        2 ^ packingLaneBits (D.lv l).slotW 0 * 2 ^ (D.lv (l+1)).laneW := by
      rw [← pow_add]
      congr 1
      unfold packingLaneBits
      omega
    _ ≤ _ := (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hE) hchild).trans
      (by rw [coneReadClock, tally_length]; exact Nat.le_add_right _ _)

end P1SolCone.SolCone
