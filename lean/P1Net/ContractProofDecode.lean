import P1Net.ContractProofPins
import P1Net.ContractProofStateRouting

/-! Soundness: a satisfying physical labelling, completed at the unowned bits, gives an
accepting verifier run with the requested skeleton. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : RoutedGood V B L I σ ha bset)

local notation "tbl" => tableAt V B L I σ ha bset z
local notation "startW" => startWord V B L I σ ha bset z
local notation "endW" => endWord V B L I σ ha bset z

noncomputable def beforeState (t : ℕ) := encS V B (tbl t).q (tbl t).off
noncomputable def afterState (t : ℕ) := encS V B (evolve (tbl t)).q (evolve (tbl t)).off

local notation "beforeS" => beforeState V B L I σ ha bset z
local notation "afterS" => afterState V B L I σ ha bset z

theorem table_conditions (i : Fin (I * 2 ^ h)) :
    (evolve (tbl i)).move = σ i ∧ ((i : ℕ) + 1 = I * 2 ^ h → Accepts B (evolve (tbl i))) := by
  let p := (intervalEquiv I h).symm i
  have hi : intervalEquiv I h (p.1, p.2) = i := (intervalEquiv I h).apply_symm_apply i
  have H := (center_spec V B L I σ ha bset z p.1 p.2).2
  rw [hi] at H
  simpa only [tableAt, dif_pos i.isLt] using H

theorem initial_word : startW (0 : Fin I) (0 : Fin (2 ^ h)) = encS V B V.initialState (fun _ => finOfInt B 0) := by
  let l := (laneEquiv h).symm (0 : Fin (2 ^ h))
  have H := z.property ((((0 : Fin I), Loc.eIn), false), l)
  simp only [rnSiteOK, Bool.false_eq_true, ↓reduceIte, Fin.val_zero, l, Equiv.apply_symm_apply] at H
  simp only [startWord]
  exact H

theorem boundary_copy {i i' : Fin I} (hp : colPred i' = some i) (j : Fin (2 ^ h)) :
    startW i' j = endW i j := by
  let v : Fin I × Loc V.K h := (i', .eIn)
  let v' : Fin I × Loc V.K h := (i, .eOut)
  let l := (laneEquiv h).symm j
  have hi : (i' : ℕ) ≠ 0 := by
    intro hz
    simp [colPred, hz] at hp
  have hm : netMate I σ (v, 1) = some (v', 1) := by simp [v, v', netMate, locMate, interMate, hp]
  have hm' : netMate I σ (v', 1) ≠ none := by
    rw [netMate_symm I σ hm]
    exact Option.some_ne_none _
  have hd : netDisp I σ (v, 1) = 0 := by simp only [netDisp, hm, disp1, v, v', add_zero]
  have hstart := z.property ((v, false), l)
  change (if (i' : ℕ) = 0 then _ else _) at hstart
  rw [if_neg hi] at hstart
  have hout : netMate I σ (v', 1) ≠ none →
      slotOut V B I σ ha z.val v' l 1 (strWidth V B) = slotIn V B I σ ha z.val v' l 0 (strWidth V B) :=
    z.property ((v', false), l)
  have e := slotIn_mate V B I σ ha z.val hm l (strWidth V B)
  rw [hd, add_zero] at e
  exact Eq.trans hstart (e.trans (hout hm'))

section StateChain

variable (hr : Routing.route (bset (1 + h) (stAddr h)) = stAddr h)

include hr in
theorem first_lane (ι : Fin I) : beforeS ((ι : ℕ) * 2 ^ h) = startW ι 0 := by
  have H := state_delivery V B L I σ ha bset z ι hr (0, 0)
  have he : stNext (h := h) (0, 0) = (1, 0) := by simp [stNext]
  rw [he, state_output_one, state_input_zero] at H
  have hd := tableAt_lane V B L I σ ha bset z ι (0 : Fin (2 ^ h))
  simp only [Fin.val_zero, Nat.add_zero] at hd
  simpa only [beforeState, hd] using H

include hr in
theorem next_lane (ι : Fin I) (j : Fin (2 ^ h)) (hj : (j : ℕ) + 1 < 2 ^ h) :
    beforeS (((ι : ℕ) * 2 ^ h + j) + 1) = afterS ((ι : ℕ) * 2 ^ h + j) := by
  let j' : Fin (2 ^ h) := ⟨j + 1, hj⟩
  have hn : stNext (h := h) (1, j) = (1, j') := by simp [stNext, hj, j']
  have H := state_delivery V B L I σ ha bset z ι hr (1, j)
  rw [hn, state_output_one, state_input_one] at H
  rw [show (ι : ℕ) * 2 ^ h + j + 1 = (ι : ℕ) * 2 ^ h + (j' : ℕ) by dsimp only [j']; omega]
  simpa only [beforeState, afterState, tableAt_lane] using H

include hr in
theorem last_lane (ι : Fin I) (j : Fin (2 ^ h)) (hj : ¬ (j : ℕ) + 1 < 2 ^ h) :
    endW ι 0 = afterS ((ι : ℕ) * 2 ^ h + j) := by
  have hn : stNext (h := h) (1, j) = (0, 0) := by simp [stNext, hj, Fin.ext_iff]
  have H := state_delivery V B L I σ ha bset z ι hr (1, j)
  rw [hn, state_output_zero, state_input_one] at H
  simpa only [afterState, tableAt_lane] using H

include hr in
theorem state_chain (t : ℕ) (ht : t + 1 < I * 2 ^ h) : beforeS (t + 1) = afterS t := by
  have hN := Nat.two_pow_pos h
  let ι : Fin I := ⟨t / 2 ^ h, (Nat.div_lt_iff_lt_mul hN).2 (by omega)⟩
  let j : Fin (2 ^ h) := ⟨t % 2 ^ h, Nat.mod_lt _ hN⟩
  have he : (ι : ℕ) * 2 ^ h + j = t := Nat.div_add_mod' _ _
  by_cases hj : (j : ℕ) + 1 < 2 ^ h
  · simpa only [he] using next_lane V B L I σ ha bset z hr ι j hj
  · have hj' : (j : ℕ) + 1 = 2 ^ h := by have := j.isLt; omega
    have ht' : t + 1 = ((ι : ℕ) + 1) * 2 ^ h := by rw [← he, Nat.succ_mul, Nat.add_assoc, hj']
    have hb : ((ι : ℕ) + 1) * 2 ^ h < I * 2 ^ h := ht' ▸ ht
    let i' : Fin I := ⟨(ι : ℕ) + 1, (Nat.mul_lt_mul_right hN).1 hb⟩
    have hp : colPred i' = some ι := by simp [i', colPred]
    calc
      beforeS (t + 1) = beforeS ((i' : ℕ) * 2 ^ h) := congrArg beforeS ht'
      _ = startW i' 0 := first_lane V B L I σ ha bset z hr i'
      _ = endW ι 0 := boundary_copy V B L I σ ha bset z hp _
      _ = afterS ((ι : ℕ) * 2 ^ h + j) := last_lane V B L I σ ha bset z hr ι j hj
      _ = afterS t := congrArg afterS he

end StateChain

abbrev Routes (b : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) :=
  ∀ (m : ℕ) [NeZero m] (π : Equiv.Perm (Routing.Addr m)), Routing.route (b m π) = π

theorem valid_tables (route : Routes bset) (free : UnownedBits V B L I σ) :
    Valid σ (L.input (completedGuess V B L I σ ha bset z free)) tbl (fun i => evolve (tbl i)) := by
  have hr := route (1 + h) (stAddr h)
  have h0 := (first_lane V B L I σ ha bset z hr (0 : Fin I)).trans (initial_word V B L I σ ha bset z)
  simp only [Fin.val_zero, Nat.zero_mul] at h0
  have hstart := encS_injective V B h0
  have hstep (i : ℕ) (hi : i + 1 < I * 2 ^ h) :=
    encS_injective V B (state_chain V B L I σ ha bset z hr i hi)
  exact {
    table := fun _ _ => rfl
    move := fun i hi => (table_conditions V B L I σ ha bset z ⟨i, hi⟩).1
    start_q := fun _ => hstart.1
    start_off := fun _ => hstart.2
    chain_q := fun i hi => (hstep i hi).1
    chain_off := fun i hi => (hstep i hi).2
    content := table_content_valid V B L I σ ha bset z route free
  }

/-- Every completion of a satisfying routed labelling accepts and has skeleton `σ`. -/
theorem completed_good (route : Routes bset) (free : UnownedBits V B L I σ) :
    GoodW (B := B) L σ (completedGuess V B L I σ ha bset z free) := by
  let w := completedGuess V B L I σ ha bset z free
  obtain ⟨hsk, hrun⟩ := valid_unique (L.input w) (valid_tables V B L I σ ha bset z route free)
  let i : Fin (I * 2 ^ h) := lastIdx
  have hi : (i : ℕ) + 1 = I * 2 ^ h := by
    have hn := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne I)) (Nat.two_pow_pos h)
    change I * 2 ^ h - 1 + 1 = I * 2 ^ h
    omega
  have hacc := (table_conditions V B L I σ ha bset z i).2 hi
  have hout : evolve (tbl i) = runOut (B := B) (L.input w) i := (hrun i i.isLt).2
  rw [hout, accepts_runOut, hi] at hacc
  exact ⟨(haltsIn_iff _ _ _).2 hacc, hsk.symm⟩

end P1Net.AstraContract
