import P1Net.ContractProofTerminals

/-! Centre, table paths and outgoing terminal sites of the packed accepting run. -/

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
local notation "Wt" => tupWidth V B

theorem runCArc_code_last (route : Routes bset) (ι : Fin I) (k : V.K) (d : ℕ) (hd : d < 8) (l : BitWord h) :
    runCArc V B I σ bset input ι k (rcolLast h) (addrOf (code3 d) l) false =
      runContentDest V B I σ input ι k (typ d, laneEquiv h l) := by
  have H := runCArc_last V B I σ bset input route ι k (typ d, laneEquiv h l)
  simpa only [item_addr, typ_val hd, Equiv.symm_apply_apply] using H

theorem runSArc_false_last (route : Routes bset) (ι : Fin I) (l : BitWord h) :
    runSArc V B I bset input ι (scolLast h) (addrOf (code1 false) l) false =
      runBoundary V B h input (((ι : ℕ) + 1) * 2 ^ h) (laneEquiv h l) := by
  have H := runSArc_last V B I bset input route ι (0, laneEquiv h l)
  simpa only [state_addr_zero, Equiv.symm_apply_apply, runStateDest, ↓reduceIte] using H

theorem runSArc_true_last (route : Routes bset) (ι : Fin I) (l : BitWord h) :
    runSArc V B I bset input ι (scolLast h) (addrOf (code1 true) l) false =
      runStateAt V B input ((ι : ℕ) * 2 ^ h + laneEquiv h l) := by
  have H := runSArc_last V B I bset input route ι (1, laneEquiv h l)
  simpa only [state_addr_one, Equiv.symm_apply_apply, runStateDest, if_neg (show (1 : Fin 2) ≠ 0 by decide)] using H

theorem run_center_out (ι : Fin I) (l : BitWord h) :
    OutR (ι, .tabC) l 0 Wt = tupleWord V B (runStrings V B input ((ι : ℕ) * 2 ^ h + laneEquiv h l)) := by
  have hm : locMate (.tabC : Loc V.K h) 0 = some (.tabP (firstExt V.K), 0) := rfl
  rw [run_local_out (W := Wt) V B I σ ha bset input ι hm rfl l]
  exact asWord_self _

theorem run_center_ok (w : GoodGuess V B L I σ) (ι : Fin I) (l : BitWord h) :
    RunSite V B I σ ha bset (L.input w.val) L ι .tabC l := by
  let t := (ι : ℕ) * 2 ^ h + laneEquiv h l
  let d : LocalIn V B := runIn (L.input w.val) t
  have ht : t < I * 2 ^ h := lane_time_lt I ι (laneEquiv h l)
  have H := run_center V B I σ L w t ht
  refine ⟨d, ?_, fun _ => H.1, H.2⟩
  change slotOut V B I σ ha (runLabels V B I σ ha bset (L.input w.val)) (ι,.tabC) l 0 Wt =
    tupleWord V B (extData V B (runIn (B := B) (L.input w.val) t) (evolve (runIn (B := B) (L.input w.val) t)))
  rw [evolve_runIn]
  exact run_center_out V B I σ ha bset (L.input w.val) ι l

theorem run_path_in (ι : Fin I) (l : BitWord h) (c : Ext V.K) :
    InR (ι, .tabP c) l 0 Wt = tupleWord V B (runStrings V B input ((ι : ℕ) * 2 ^ h + laneEquiv h l)) := by
  cases hp : prevExt c with
  | none =>
    have hm : locMate (.tabP c : Loc V.K h) 0 = some (.tabC, 0) := by simp [locMate, hp]
    rw [run_local_in (W := Wt) V B I σ ha bset input ι hm rfl rfl rfl l]
    exact asWord_self _
  | some c' =>
    have hm : locMate (.tabP c : Loc V.K h) 0 = some (.tabP c', 1) := by simp [locMate, hp]
    rw [run_local_in (W := Wt) V B I σ ha bset input ι hm rfl rfl rfl l]
    simp only [runRaw, ↓reduceIte, asWord_self]

theorem run_path_external (hsk : skeleton V input B (I * 2 ^ h) = σ) (route : Routes bset)
    (ι : Fin I) (l : BitWord h) (c : Ext V.K) :
    (if Ext.isIn V c then InR (ι, .tabP c) l 2 Wx else OutR (ι, .tabP c) l 2 Wx) =
      runStrings V B input ((ι : ℕ) * 2 ^ h + laneEquiv h l) c := by
  cases c with
  | stIn =>
    have hm : locMate (.tabP .stIn : Loc V.K h) 2 = some (.st (scolLast h) (code1 true), 0) := rfl
    change InR (ι, .tabP .stIn) l 2 Wx = _
    rw [run_local_in (W := Wx) V B I σ ha bset input ι hm rfl rfl rfl l]
    change asWord Wx (runSArc V B I bset input ι (scolLast h) (addrOf (code1 true) l) false) = _
    rw [asWord_self]
    exact runSArc_true_last V B I bset input route ι l
  | cIn k δ =>
    have hm : locMate (.tabP (.cIn k δ) : Loc V.K h) 2 = some (.rt k (rcolLast h) (code3 (3 + δ)), 0) := rfl
    change InR (ι, .tabP (.cIn k δ)) l 2 Wx = _
    rw [run_local_in (W := Wx) V B I σ ha bset input ι hm rfl rfl rfl l]
    change asWord Wx (runCArc V B I σ bset input ι k (rcolLast h) (addrOf (code3 (3 + δ)) l) false) = _
    rw [asWord_self, runCArc_code_last V B I σ bset input route ι k (3 + δ) (by have := δ.isLt; omega) l]
    exact runContentDest_table V B I σ input hsk ι k _ δ
  | stOut =>
    have hm : locMate (.tabP .stOut : Loc V.K h) 2 = some (.st (scol0 h) (code1 true), 2) := rfl
    change OutR (ι, .tabP .stOut) l 2 Wx = _
    rw [run_local_out (W := Wx) V B I σ ha bset input ι hm rfl l]
    exact asWord_self _
  | cOut k δ =>
    have hm : locMate (.tabP (.cOut k δ) : Loc V.K h) 2 = some (.rt k (rcol0 h) (code3 (3 + δ)), 2) := rfl
    change OutR (ι, .tabP (.cOut k δ)) l 2 Wx = _
    rw [run_local_out (W := Wx) V B I σ ha bset input ι hm rfl l]
    exact asWord_self _

theorem run_path_ok (hsk : skeleton V input B (I * 2 ^ h) = σ) (route : Routes bset)
    (ι : Fin I) (l : BitWord h) (c : Ext V.K) : RunSite V B I σ ha bset input L ι (.tabP c) l := by
  have hin := run_path_in V B I σ ha bset input ι l c
  constructor
  · intro linked
    change OutR (ι, .tabP c) l 1 Wt = InR (ι, .tabP c) l 0 Wt
    rw [hin, run_out (W := Wt) V B I σ ha bset input linked rfl l]
    exact asWord_self _
  · have H := run_path_external V B I σ ha bset input hsk route ι l c
    change (if Ext.isIn V c then InR (ι, .tabP c) l 2 Wx = segment V B c (InR (ι, .tabP c) l 0 Wt)
      else OutR (ι, .tabP c) l 2 Wx = segment V B c (InR (ι, .tabP c) l 0 Wt))
    rw [hin, segment_tupleWord]
    cases he : Ext.isIn V c <;> simpa only [he, Bool.false_eq_true, ↓reduceIte] using H

theorem run_port_out_ok (route : Routes bset) (ι : Fin I) (l : BitWord h) (k : V.K) (δ : Fin 3) :
    RunSite V B I σ ha bset input L ι (.portOut k δ) l := by
  intro linked
  change OutR (ι, .portOut k δ) l 1 Wx = InR (ι, .portOut k δ) l 0 Wx
  have hm : locMate (.portOut k δ : Loc V.K h) 0 = some (.rt k (rcolLast h) (code3 δ), 0) := rfl
  rw [run_out (W := Wx) V B I σ ha bset input linked rfl l, run_local_in (W := Wx) V B I σ ha bset input ι hm rfl rfl rfl l]
  change asWord Wx (runHistory V B I σ input k (portBlock I σ ι k δ (laneEquiv h l)) (((ι : ℕ) + 1) * 2 ^ h)) =
    asWord Wx (runCArc V B I σ bset input ι k (rcolLast h) (addrOf (code3 δ) l) false)
  rw [asWord_self, asWord_self, runCArc_code_last V B I σ bset input route ι k δ (by have := δ.isLt; omega) l]
  exact (runContentDest_port V B I σ input ι k _ δ).symm

theorem run_eout_ok (route : Routes bset) (ι : Fin I) (l : BitWord h) :
    RunSite V B I σ ha bset input L ι .eOut l := by
  intro linked
  change OutR (ι, .eOut) l 1 Wx = InR (ι, .eOut) l 0 Wx
  have hm : locMate (.eOut : Loc V.K h) 0 = some (.st (scolLast h) (code1 false), 0) := rfl
  rw [run_out (W := Wx) V B I σ ha bset input linked rfl l, run_local_in (W := Wx) V B I σ ha bset input ι hm rfl rfl rfl l]
  change asWord Wx (runBoundary V B h input (((ι : ℕ) + 1) * 2 ^ h) (laneEquiv h l)) =
    asWord Wx (runSArc V B I bset input ι (scolLast h) (addrOf (code1 false) l) false)
  rw [asWord_self, asWord_self]
  exact (runSArc_false_last V B I bset input route ι l).symm

end P1Net.AstraContract
