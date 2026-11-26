import P1SolCone.ConeFuel
import P1SolCone.FieldCache

namespace P1SolCone.SolCone

open P1Int P1Int.P11 P1Wit P1Wit.SolSpace P1Wrap
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

open private prefixPhases blockPhases runPhases shrinkPhase refreshPhase levelDims layoutRows
  slotCap slotCap_ge levelDims_bounds levelConstant layoutRows_length
  CalendarOK runPhases_OK from P1Wit.SpaceFacts

variable {k : Type} [Field k] {S : BlockSchedule k}

private theorem prefixLoss (j : ℕ) (hj : j ≤ S.steps) :
    ((prefixPhases S j hj).map Phase.laneLoss).sum =
      ∑ i ∈ Finset.range j, packingLaneBits (S.exponentAt i) 0 := by
  induction j with
  | zero => simp [prefixPhases]
  | succ j ih =>
    simp only [prefixPhases, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton, shrinkPhase, Finset.sum_range_succ, S.exponentAt_castSucc ⟨j,hj⟩]

private theorem calendarLoss (T : ℕ) :
    ((runPhases S T).map Phase.laneLoss).sum = T * S.laneBits := by
  have hb : ((blockPhases S).map Phase.laneLoss).sum = S.laneBits := by
    simp only [blockPhases, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      prefixLoss, refreshPhase, BlockSchedule.laneBits, BlockSchedule.portExponent]
    rw [← Fin.sum_univ_eq_sum_range (fun i => packingLaneBits (S.exponentAt i) 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [S.exponentAt_castSucc i]
  induction T with
  | zero => simp only [runPhases, List.map_nil, List.sum_nil, Nat.zero_mul]
  | succ T ih =>
    simp only [runPhases, List.map_append, List.sum_append, hb, ih, Nat.succ_mul, Nat.add_comm]

private theorem prefixLossKind (j : ℕ) (hj : j ≤ S.steps) :
    ∀ ph ∈ prefixPhases S j hj,
      ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent) := by
  induction j with
  | zero => simp [prefixPhases]
  | succ j ih =>
    intro ph hp
    rw [prefixPhases, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact ih _ ph hp
    · rfl

private theorem calendarLossKind (T : ℕ) :
    ∀ ph ∈ runPhases S T,
      ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent) := by
  induction T with
  | zero => simp [runPhases]
  | succ T ih =>
    intro ph hp
    rw [runPhases, blockPhases, List.mem_append, List.mem_append, List.mem_singleton] at hp
    rcases hp with (hp | rfl) | hp
    · exact prefixLossKind S.steps le_rfl ph hp
    · rfl
    · exact ih ph hp

private theorem calendarSlotCap {xs : List Phase} {flag : Bool}
    (h : CalendarOK S flag xs) : ∀ ph ∈ xs, 2 ^ ph.exponent ≤ slotCap S := by
  induction xs generalizing flag with
  | nil => simp
  | cons a as ih =>
    intro ph hp
    change 2 ^ a.exponent ≤ slotCap S ∧
      (if a.shrink then 2 ≤ a.divisor ∧ CalendarOK S true as else
        flag = true ∧ a.divisor = 1 ∧ CalendarOK S false as) at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · by_cases ha : a.shrink
      · exact ih (ite_eq_left ha ▸ h.2).2 ph hp
      · exact ih (ite_eq_right ha ▸ h.2).2.2 ph hp

/-- The row geometry required to enumerate the old and new slot and lane axes. -/
structure ConeRowBounds (S : BlockSchedule k) (h : ℕ) (L : LevelDims) : Prop where
  slots_eq : L.slots = 2 ^ L.slotW
  lanes_eq : L.lanes = 2 ^ L.laneW
  laneW_le : L.laneW ≤ h
  slots_le : L.slots ≤ slotCap S
  slotW_le : L.slotW ≤ levelConstant S
  colW_le : L.colW ≤ levelConstant S
  tagW_le : L.tagW ≤ levelConstant S
  keys_le : L.termKeys ≤ slotCap S * L.lanes
  arity_le : L.termArity ≤ levelConstant S

private theorem rowsBounds (P g : ℕ) (xs : List Phase)
    (h : ∀ ph ∈ xs, 2 ^ ph.exponent ≤ slotCap S) :
    ∀ L ∈ layoutRows S P g xs, ConeRowBounds S g L := by
  have headBounds (P g a : ℕ) (s : Option Bool) (ha : 2 ^ a ≤ slotCap S) :
      ConeRowBounds S g (levelDims S.expanderExponent a g P s) := by
    obtain ⟨hl, hw, hc, ht, hk, hr⟩ := levelDims_bounds S s ha
    exact ⟨rfl, hl, le_rfl, ha, hw, hc, ht, hk, hr⟩
  induction xs generalizing P g with
  | nil =>
    intro L hL
    change L ∈ [levelDims S.expanderExponent (S.degreeExponent 0) g P none] at hL
    rw [List.mem_singleton.mp hL]
    exact headBounds _ _ _ _ (slotCap_ge S 0)
  | cons ph xs ih =>
    intro L hL
    change L ∈ _ :: _ at hL
    rcases List.mem_cons.mp hL with rfl | ht
    · exact headBounds _ _ _ _ (h ph List.mem_cons_self)
    · have ht' := ih _ _ (fun a ha => h a (List.mem_cons_of_mem _ ha)) L ht
      exact { ht' with laneW_le := ht'.laneW_le.trans (Nat.sub_le _ _) }

variable (B : S.Templates) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

theorem coneDims_rowBounds (n l : ℕ) (hl : l ≤ (coneDims B V a b d bigBias termBias n).top) :
    ConeRowBounds S (Params.h (lpTime a b n)) ((coneDims B V a b d bigBias termBias n).lv l) := by
  let t := lpTime a b n
  let xs := runPhases S (Params.T (portConsts B) t)
  let rows := layoutRows S (initialPositions (toOAI V) 1 t) (Params.h t) xs
  have hlen : rows.length = xs.length + 1 := layoutRows_length S _ _ _
  have hi : l < rows.length := by rw [hlen]; exact Nat.lt_succ_of_le hl
  change ConeRowBounds S _ ((rows[l]?).getD _)
  rw [List.getElem?_eq_getElem hi, Option.getD_some]
  exact rowsBounds _ _ _ (calendarSlotCap (runPhases_OK S _ true)) _ (List.getElem_mem hi)

/-- The layout bit and the lane loss select the same kind of substep. -/
structure ConeStepGeometry (L L' : LevelDims) : Prop where
  loss : L.laneW = (if L.shrink then packingLaneBits L.slotW 0 else L.slotW) + L'.laneW

private theorem rowStep (P g : ℕ) (xs : List Phase)
    (h : ((xs.map Phase.laneLoss).sum) ≤ g)
    (hkind : ∀ ph ∈ xs, ph.laneLoss = (if ph.shrink then packingLaneBits ph.exponent 0 else ph.exponent))
    (l : ℕ) (hl : l < xs.length) :
    let rows := layoutRows S P g xs
    let deflt := levelDims S.expanderExponent 0 0 0 none
    ConeStepGeometry ((rows[l]?).getD deflt) ((rows[l+1]?).getD deflt) := by
  induction xs generalizing P g l with
  | nil => simp at hl
  | cons ph xs ih =>
    have hsum : ph.laneLoss + (xs.map Phase.laneLoss).sum ≤ g := h
    cases l with
    | zero =>
      simp only [layoutRows, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      constructor
      have hk := hkind ph List.mem_cons_self
      cases xs <;> change g = (if (some ph.shrink == some true) then packingLaneBits ph.exponent 0
        else ph.exponent) + (g - ph.laneLoss)
      all_goals
        have he : (some ph.shrink == some true) = ph.shrink := by cases ph.shrink <;> rfl
        rw [he, ← hk]
        omega
    | succ l =>
      simp only [layoutRows, List.getElem?_cons_succ]
      exact ih _ _ (by omega) (fun q hq => hkind q (List.mem_cons_of_mem _ hq)) l
        (Nat.lt_of_succ_lt_succ hl)

theorem coneDims_step (n l : ℕ) (hl : l < (coneDims B V a b d bigBias termBias n).top) :
    ConeStepGeometry ((coneDims B V a b d bigBias termBias n).lv l)
      ((coneDims B V a b d bigBias termBias n).lv (l+1)) := by
  let t := lpTime a b n
  let K := portConsts B
  have h := lane_bound K S.laneBits (portConsts_b0 B) t
  exact rowStep _ _ _ (by rw [calendarLoss]; exact h) (calendarLossKind _) _ hl

/-- Every slot-by-lane array fits a fixed polynomial in the binary clock length. -/
theorem coneRowLanes_le (n l : ℕ) (hl : l ≤ (coneDims B V a b d bigBias termBias n).top) :
    ((coneDims B V a b d bigBias termBias n).lv l).lanes ≤
      (Params.lam (lpTime a b n) + 1) ^ 10 := by
  let t := lpTime a b n
  let D := coneDims B V a b d bigBias termBias n
  have h := coneDims_rowBounds B V a b d bigBias termBias n l hl
  have hh : Params.h t ≤ Params.p t * 10 := by unfold Params.h; omega
  calc
    (D.lv l).lanes = 2 ^ (D.lv l).laneW := h.lanes_eq
    _ ≤ 2 ^ (Params.p t * 10) := Nat.pow_le_pow_right (by decide) (h.laneW_le.trans hh)
    _ = (2 ^ Params.p t) ^ 10 := pow_mul ..
    _ ≤ _ := Nat.pow_le_pow_left (power_p_le_lam_succ t) _

theorem coneBaseFieldCount_le (n l y : ℕ) (hl : l ≤ (coneDims B V a b d bigBias termBias n).top) :
    let L := (Params.lam (lpTime a b n) + 1) ^ 10
    (baseFields (coneDims B V a b d bigBias termBias n) l y).length ≤
      slotCap S * 6 + L * slotCap S + 2 + (slotCap S * L) * (levelConstant S + 1) := by
  rw [baseFields_length]
  have shape := coneDims_rowBounds B V a b d bigBias termBias n l hl
  have lanes := coneRowLanes_le B V a b d bigBias termBias n l hl
  have keys := shape.keys_le.trans (Nat.mul_le_mul_left _ lanes)
  gcongr <;> first | exact shape.slots_le | exact lanes | exact keys | exact shape.arity_le

open OAI.Computability.IntegerMultiplication Code Staff
open P1SolFmt.SolFigure P1SolFmt.SolParameters

noncomputable def coneAxisClock (S : BlockSchedule k) (a b : ℕ) (w : Bits.Word) : Tally :=
  tally (slotCap S * (Params.lam (lpTime a b (P1Batch.bval w)) + 1) ^ 10)

theorem coneAxisClock_poly : Poly (coneAxisClock S a b) := by
  let r := inputRegime Bits.Word
  have hL : Realizes r (fun w => Params.lam (lpTime a b (P1Batch.bval w)) + 1) :=
    (realizes_lam (coneTimeFigure a b Code.Poly.identity)).plus (Realizes.fix 1)
  have hp (e : ℕ) : Realizes r (fun w => (Params.lam (lpTime a b (P1Batch.bval w)) + 1) ^ e) := by
    induction e with
    | zero => simpa only [pow_zero] using (Realizes.fix (r := r) 1)
    | succ e ih => simpa only [pow_succ] using ih.times hL
  exact (Realizes.fix (r := r) (slotCap S)).times (hp 10)

theorem coneAxisClock_fits (w : Bits.Word) (l : ℕ) :
    let n := P1Batch.bval w
    let D := coneDims B V a b d bigBias termBias n
    l ≤ D.top → (D.lv l).lanes * (D.lv l).slots ≤ (coneAxisClock S a b w).length := by
  intro n D hl
  rw [coneAxisClock, tally_length, Nat.mul_comm (slotCap S)]
  exact Nat.mul_le_mul (coneRowLanes_le B V a b d bigBias termBias n l hl)
    (coneDims_rowBounds B V a b d bigBias termBias n l hl).slots_le

end P1SolCone.SolCone
