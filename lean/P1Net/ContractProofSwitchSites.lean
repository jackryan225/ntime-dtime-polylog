import P1Net.ContractProofSwitchInputs
import P1Net.GlueState

/-! All physical switching positions of the run encoder, including the final dummy content outputs. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) (input : List Bool)
  {g : ℕ} (L : GuessLayout V g)

local notation "zR" => runLabels V B I σ ha bset input
local notation "InR" => slotIn V B I σ ha zR
local notation "OutR" => slotOut V B I σ ha zR
local notation "Wx" => strWidth V B

theorem run_rt_out_zero (route : Routes bset) (ι : Fin I) (k : V.K) (c : Fin (2 * (h + 3)))
    (π : BitWord 3) (l : BitWord h) :
    OutR (ι, .rt k c π) l 0 Wx = runCArc V B I σ bset input ι k c (addrOf π l) false := by
  by_cases hm : netMate I σ ((ι, Loc.rt k c π),0) = none
  · have hs : colSucc c = none := by
      cases hp : colSucc c with
      | none => rfl
      | some d => simp [netMate, locMate, hp] at hm
    have hc : c = rcolLast h := colLast_of_no_succ (n := h + 2) hs
    have hd : 6 ≤ num3 π := by
      by_contra! h6
      by_cases h3 : num3 π < 3 <;> simp [netMate, locMate, hs, rtDst, h3, h6] at hm
    rw [slotOut_unmated V B I σ ha zR hm l Wx, hc, ← packed_content_item π l,
      runCArc_last V B I σ bset input route ι k, runContentDest_dummy V B I σ input ι k _ _ hd]
  · rw [run_out (W := Wx) V B I σ ha bset input hm rfl l]
    exact asWord_self _

theorem run_st_out_zero (ι : Fin I) (c : Fin (2 * (h + 1))) (π : BitWord 1) (l : BitWord h) :
    OutR (ι, .st c π) l 0 Wx = runSArc V B I bset input ι c (addrOf π l) false := by
  have hm : netMate I σ ((ι, Loc.st c π),0) ≠ none := by
    cases hp : colSucc c <;> simp [netMate, locMate, hp]
  rw [run_out (W := Wx) V B I σ ha bset input hm rfl l]
  exact asWord_self _

theorem run_rt_previous (ι : Fin I) (k : V.K) {c d : Fin (2 * (h + 3))} (hp : colPred c = some d)
    (π : BitWord 3) (l : BitWord h) :
    InR (ι,.rt k c π) l 2 Wx = runCArc V B I σ bset input ι k d (addrOf π l) false ∧
    InR (ι,.rt k c π) l 3 Wx = runCArc V B I σ bset input ι k d (addrOf π l + Routing.flip (3+h) d) true := by
  constructor
  · rw [run_in (W := Wx) V B I σ ha bset input (netMate_rt2 I σ ι k π hp) rfl l, netDisp_rt2 I σ ι k π hp, add_zero]
    exact asWord_self _
  · rw [run_in (W := Wx) V B I σ ha bset input (netMate_rt3 I σ ι k π hp) rfl l, netDisp_rt3 I σ ι k π hp]
    change asWord Wx (runCArc V B I σ bset input ι k d (addrOf (π + tyFlip 3 h d) (l + lnFlip 3 h d)) true) = _
    rw [asWord_self, packed_flip]

theorem run_st_previous (ι : Fin I) {c d : Fin (2 * (h + 1))} (hp : colPred c = some d)
    (π : BitWord 1) (l : BitWord h) :
    InR (ι,.st c π) l 2 Wx = runSArc V B I bset input ι d (addrOf π l) false ∧
    InR (ι,.st c π) l 3 Wx = runSArc V B I bset input ι d (addrOf π l + Routing.flip (1+h) d) true := by
  constructor
  · rw [run_in (W := Wx) V B I σ ha bset input (netMate_st2 I σ ι π hp) rfl l, netDisp_st2 I σ ι π hp, add_zero]
    exact asWord_self _
  · rw [run_in (W := Wx) V B I σ ha bset input (netMate_st3 I σ ι π hp) rfl l, netDisp_st3 I σ ι π hp]
    change asWord Wx (runSArc V B I bset input ι d (addrOf (π + tyFlip 1 h d) (l + lnFlip 1 h d)) true) = _
    rw [asWord_self, packed_flip]

theorem run_rt_ok (route : Routes bset) (ι : Fin I) (k : V.K) (c : Fin (2 * (h + 3)))
    (π : BitWord 3) (l : BitWord h) : RunSite V B I σ ha bset input L ι (.rt k c π) l := by
  have hc := c.isLt
  let s := bset (3+h) (accAddr I σ ι k)
  let src := fun x => runContentSource V B I σ input ι k ((itemEquiv h).symm x)
  change routeOK s c (addrOf π l)
    (InR (ι,.rt k c π) l 2 Wx) (InR (ι,.rt k c π) l 3 Wx)
    (OutR (ι,.rt k c π) l 0 Wx) (OutR (ι,.rt k c π) l 1 Wx)
  apply routeOK_from_canonical s src c (by omega) (addrOf π l) _ _ _ _
  · intro h0
    have he : c = rcol0 h := Fin.ext h0
    rw [he]
    exact run_rt_zero V B I σ ha bset input ι k π l
  · intro p hp
    let d : Fin (2 * (h+3)) := ⟨p, by omega⟩
    have he : colPred c = some d := by simp [colPred, hp, d]
    exact run_rt_previous V B I σ ha bset input ι k he π l
  · exact run_rt_out_zero V B I σ ha bset input route ι k c π l
  · intro hlast
    have hnext : (c : ℕ) + 1 < 2 * (h+3) := by omega
    have hm : netMate I σ ((ι, Loc.rt k c π),1) ≠ none := by simp [netMate, locMate, colSucc, hnext]
    rw [run_out (W := Wx) V B I σ ha bset input hm rfl l]
    exact asWord_self _

theorem run_st_ok (ι : Fin I) (c : Fin (2 * (h + 1))) (π : BitWord 1) (l : BitWord h) :
    RunSite V B I σ ha bset input L ι (.st c π) l := by
  have hc := c.isLt
  let s := bset (1+h) (stAddr h)
  let src := fun x => runStateSource V B h input ι ((stItemEquiv h).symm x)
  change routeOK s c (addrOf π l)
    (InR (ι,.st c π) l 2 Wx) (InR (ι,.st c π) l 3 Wx)
    (OutR (ι,.st c π) l 0 Wx) (OutR (ι,.st c π) l 1 Wx)
  apply routeOK_from_canonical s src c (by omega) (addrOf π l) _ _ _ _
  · intro h0
    have he : c = scol0 h := Fin.ext h0
    rw [he]
    exact run_st_zero V B I σ ha bset input ι π l
  · intro p hp
    let d : Fin (2 * (h+1)) := ⟨p, by omega⟩
    have he : colPred c = some d := by simp [colPred, hp, d]
    exact run_st_previous V B I σ ha bset input ι he π l
  · exact run_st_out_zero V B I σ ha bset input ι c π l
  · intro hlast
    have hnext : (c : ℕ) + 1 < 2 * (h+1) := by omega
    have hm : netMate I σ ((ι, Loc.st c π),1) ≠ none := by simp [netMate, locMate, colSucc, hnext]
    rw [run_out (W := Wx) V B I σ ha bset input hm rfl l]
    exact asWord_self _

end P1Net.AstraContract
