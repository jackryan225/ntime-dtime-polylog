import P1Net.ContractProofTables
import P1Net.ContractProofSwitch

/-! The state routing delivers the permutation of successive small intervals. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ}

theorem packed_split {t : ℕ} (x : Routing.Addr (t + h)) :
    addrOf (addrSplit (t := t) (h := h) x).1 (addrSplit (t := t) (h := h) x).2 = x :=
  (addrEquiv t h).right_inv x

theorem split_packed {t : ℕ} (π : BitWord t) (l : BitWord h) : addrSplit (addrOf π l) = (π, l) :=
  (addrEquiv t h).left_inv (π, l)

theorem packed_flip {t : ℕ} [NeZero (t + h)] (π : BitWord t) (l : BitWord h) (c : ℕ) :
    addrOf (π + tyFlip t h c) (l + lnFlip t h c) = addrOf π l + Routing.flip (t + h) c := by
  funext b
  by_cases hb : (b : ℕ) < t
  · simp only [addrOf, dif_pos hb, Pi.add_apply, tyFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
  · simp only [addrOf, dif_neg hb, Pi.add_apply, lnFlip, Routing.flip, Pi.single_apply, Fin.ext_iff]
    have e : (b : ℕ) - t + t = b := by omega
    simp only [e]

theorem split_flip {t : ℕ} [NeZero (t + h)] (x : Routing.Addr (t + h)) (c : ℕ) :
    addrSplit (t := t) (h := h) (x + Routing.flip (t + h) c) =
      ((addrSplit (t := t) (h := h) x).1 + tyFlip t h c, (addrSplit (t := t) (h := h) x).2 + lnFlip t h c) := by
  rw [← split_packed ((addrSplit (t := t) (h := h) x).1 + tyFlip t h c)
    ((addrSplit (t := t) (h := h) x).2 + lnFlip t h c), packed_flip, packed_split]

theorem state_addr_zero (j : Fin (2 ^ h)) :
    stItemEquiv h (0, j) = addrOf (code1 false) ((laneEquiv h).symm j) := by
  change addrOf (type1Equiv.symm 0) ((laneEquiv h).symm j) = _
  rw [show type1Equiv.symm 0 = code1 false by decide]

theorem state_addr_one (j : Fin (2 ^ h)) :
    stItemEquiv h (1, j) = addrOf (code1 true) ((laneEquiv h).symm j) := by
  change addrOf (type1Equiv.symm 1) ((laneEquiv h).symm j) = _
  rw [show type1Equiv.symm 1 = code1 true by decide]

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

noncomputable def stInRow (z : Labels V B I σ ha) (ι : Fin I) (s : Fin 4) : WordAt (1 + h) (strWidth V B) :=
  fun c x => if hc : c < 2 * (h + 1) then
    slotIn V B I σ ha z (ι, .st ⟨c, hc⟩ (addrSplit (t := 1) x).1) (addrSplit (t := 1) x).2 s (strWidth V B)
    else fun _ => false

noncomputable def stOutRow (z : Labels V B I σ ha) (ι : Fin I) (s : Fin 4) : WordAt (1 + h) (strWidth V B) :=
  fun c x => if hc : c < 2 * (h + 1) then
    slotOut V B I σ ha z (ι, .st ⟨c, hc⟩ (addrSplit (t := 1) x).1) (addrSplit (t := 1) x).2 s (strWidth V B)
    else fun _ => false

variable (z : RoutedGood V B L I σ ha bset) (ι : Fin I)

local notation "ins" => stInRow V B I σ ha z.val ι
local notation "outs" => stOutRow V B I σ ha z.val ι

theorem st_rows_ok (c : ℕ) (hc : c < 2 * (1 + h)) (x : Routing.Addr (1 + h)) :
    routeOK (bset (1 + h) (stAddr h)) c x (ins 2 c x) (ins 3 c x) (outs 0 c x) (outs 1 c x) := by
  have hc' : c < 2 * (h + 1) := by omega
  let p := addrSplit (t := 1) (h := h) x
  let v : Fin I × Loc V.K h := (ι, .st ⟨c, hc'⟩ p.1)
  have H := z.property ((v, false), p.2)
  change routeOK (bset (1 + h) (stAddr h)) c (addrOf p.1 p.2) _ _ _ _ at H
  have he : addrOf p.1 p.2 = x := packed_split (t := 1) (h := h) x
  rw [he] at H
  simp only [stInRow, stOutRow, dif_pos hc']
  exact H

theorem st_straight (c : ℕ) (hc : c + 1 < 2 * (1 + h)) (x : Routing.Addr (1 + h)) :
    ins 2 (c + 1) x = outs 0 c x := by
  have h0 : c < 2 * (h + 1) := by omega
  have h1 : c + 1 < 2 * (h + 1) := by omega
  let π := (addrSplit (t := 1) (h := h) x).1
  have hp : colPred (⟨c + 1, h1⟩ : Fin (2 * (h + 1))) = some ⟨c, h0⟩ := by simp [colPred]
  have hm : locMate (.st ⟨c + 1, h1⟩ π : Loc V.K h) 2 = some (.st ⟨c, h0⟩ π, 0) := by
    simp [locMate, hp]
  simp only [stInRow, stOutRow, dif_pos h1, dif_pos h0]
  exact slotIn_local V B I σ ha z.val ι hm rfl rfl _ _

theorem st_cross (c : ℕ) (hc : c + 1 < 2 * (1 + h)) (x : Routing.Addr (1 + h)) :
    ins 3 (c + 1) x = outs 1 c (x + Routing.flip (1 + h) c) := by
  have h0 : c < 2 * (h + 1) := by omega
  have h1 : c + 1 < 2 * (h + 1) := by omega
  let π := (addrSplit (t := 1) (h := h) x).1
  have hp : colPred (⟨c + 1, h1⟩ : Fin (2 * (h + 1))) = some ⟨c, h0⟩ := by simp [colPred]
  have hm : locMate (.st ⟨c + 1, h1⟩ π : Loc V.K h) 3 =
      some (.st ⟨c, h0⟩ (π + tyFlip 1 h c), 1) := by simp [locMate, hp]
  have hn := local_mate V I σ ι hm
  have hd : netDisp I σ ((ι, Loc.st ⟨c + 1, h1⟩ π), 3) = lnFlip 1 h c := by
    simp [netDisp, hn, disp1]
  simp only [stInRow, stOutRow, dif_pos h1, dif_pos h0, split_flip]
  simpa only [hd] using slotIn_mate V B I σ ha z.val hn (addrSplit (t := 1) (h := h) x).2 (strWidth V B)

theorem state_delivery (hr : Routing.route (bset (1 + h) (stAddr h)) = stAddr h)
    (x : Fin 2 × Fin (2 ^ h)) :
    outs 0 (2 * (1 + h) - 1) (stItemEquiv h (stNext x)) = ins 2 0 (stItemEquiv h x) := by
  have H := last_switch (bset (1 + h) (stAddr h)) (ins 2) (ins 3) (outs 0) (outs 1)
    (st_rows_ok V B L I σ ha bset z ι) (st_straight V B L I σ ha bset z ι)
    (st_cross V B L I σ ha bset z ι) (stItemEquiv h x)
  rw [hr] at H
  simp only [stAddr, Equiv.permCongr_apply, Equiv.symm_apply_apply] at H
  exact H

noncomputable def startWord (j : Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  slotOut V B I σ ha z.val (ι, .eIn) ((laneEquiv h).symm j) 0 (strWidth V B)

noncomputable def endWord (j : Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  slotIn V B I σ ha z.val (ι, .eOut) ((laneEquiv h).symm j) 0 (strWidth V B)

theorem state_input_zero (j : Fin (2 ^ h)) :
    ins 2 0 (stItemEquiv h (0, j)) = startWord V B L I σ ha bset z ι j := by
  have hm : locMate (.eIn : Loc V.K h) 0 = some (.st (scol0 h) (code1 false), 2) := rfl
  have hn : 0 < 2 * (h + 1) := by omega
  simp only [state_addr_zero, stInRow, dif_pos hn, split_packed]
  exact slotIn_local V B I σ ha z.val ι (locMate_symm hm) rfl rfl _ _

theorem state_output_zero (j : Fin (2 ^ h)) :
    outs 0 (2 * (1 + h) - 1) (stItemEquiv h (0, j)) = endWord V B L I σ ha bset z ι j := by
  have hm : locMate (.eOut : Loc V.K h) 0 = some (.st (scolLast h) (code1 false), 0) := rfl
  rw [show 2 * (1 + h) - 1 = 2 * (h + 1) - 1 by omega]
  have hn : 2 * (h + 1) - 1 < 2 * (h + 1) := by omega
  simp only [state_addr_zero, stOutRow, dif_pos hn, split_packed]
  exact (slotIn_local V B I σ ha z.val ι hm rfl rfl _ _).symm

theorem state_input_one (j : Fin (2 ^ h)) :
    let o := evolve (centerData V B L I σ ha bset z ι ((laneEquiv h).symm j))
    ins 2 0 (stItemEquiv h (1, j)) = encS V B o.q o.off := by
  have hm : locMate (.tabP .stOut : Loc V.K h) 2 = some (.st (scol0 h) (code1 true), 2) := rfl
  have hn : 0 < 2 * (h + 1) := by omega
  simp only [state_addr_one, stInRow, dif_pos hn, split_packed]
  exact (slotIn_local V B I σ ha z.val ι (locMate_symm hm) rfl rfl _ _).trans
    (external_eq V B L I σ ha bset z ι ((laneEquiv h).symm j) .stOut)

theorem state_output_one (j : Fin (2 ^ h)) :
    let d := centerData V B L I σ ha bset z ι ((laneEquiv h).symm j)
    outs 0 (2 * (1 + h) - 1) (stItemEquiv h (1, j)) = encS V B d.q d.off := by
  have hm : locMate (.tabP .stIn : Loc V.K h) 2 = some (.st (scolLast h) (code1 true), 0) := rfl
  rw [show 2 * (1 + h) - 1 = 2 * (h + 1) - 1 by omega]
  have hn : 2 * (h + 1) - 1 < 2 * (h + 1) := by omega
  simp only [state_addr_one, stOutRow, dif_pos hn, split_packed]
  exact (slotIn_local V B I σ ha z.val ι hm rfl rfl _ _).symm.trans
    (external_eq V B L I σ ha bset z ι ((laneEquiv h).symm j) .stIn)

end P1Net.AstraContract
