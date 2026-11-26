import P1Net.ContractProofTerminals

/-! The inter-interval port links, boundary state links, and the first-pin law of the encoder. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open scoped Classical

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) (input : List Bool)
  {g : ℕ} (L : GuessLayout V g)

local notation "zR" => runLabels V B I σ ha bset input
local notation "Wx" => strWidth V B

theorem owned_portBlock {ι : Fin I} {k : V.K} {Z : ℤ} (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portBlock I σ ι k (portSlot I σ k ι (Z / 2 ^ h)) (portLane h Z) = Z := by
  obtain ⟨hl, hr⟩ := bounds_of_owns I σ ι k ho
  rw [← portType_slot I σ ι k ho]
  exact (portBlock_of_owned I σ ι k hl hr).2

theorem run_port_in_ok (w : Fin g → Bool) (ι : Fin I) (k : V.K) (δ : Fin 3) (l : BitWord h) :
    RunSite V B I σ ha bset (L.input w) L ι (.portIn k δ) l := by
  let j := laneEquiv h l
  let Q := portQ I σ k ι δ
  let Z := portBlock I σ ι k δ j
  let v : Fin I × Loc V.K h := (ι, .portIn k δ)
  let z := runLabels V B I σ ha bset (L.input w)
  have hQ : Z / 2 ^ h = Q := portBlock_div V I σ ι k δ j
  have hm : netMate I σ (v,1) = (prevOwner I σ k ι Q).map
      (fun i : Fin I => ((i, Loc.portOut k (portSlot I σ k i Q)),1)) := by
    have H := input_link I σ ι k (owns_portQ I σ k ι δ)
    rw [portSlot_portQ I σ k ι δ] at H
    exact H
  have hh : slotOut V B I σ ha z v l 0 Wx = runHistory V B I σ (L.input w) k Z ((ι : ℕ) * 2 ^ h) :=
    run_port_source_out V B I σ ha bset (L.input w) ι k δ l
  change (if netMate I σ (v,1) = none then
    ∃ p : Fin B → V.Γ, PinOK B L k Z p ∧ slotOut V B I σ ha z v l 0 Wx = encC V B p
    else slotOut V B I σ ha z v l 0 Wx = slotIn V B I σ ha z v l 1 Wx)
  cases hp : prevOwner I σ k ι Q with
  | none =>
    have hn : netMate I σ (v,1) = none := by simpa only [hp, Option.map_none] using hm
    rw [if_pos hn]
    refine ⟨initBlock (B := B) (L.input w) k Z, run_pin V B L w k Z, hh.trans ?_⟩
    exact runHistory_first V B I σ (L.input w) ι k Z (by simpa only [hQ] using hp)
  | some i =>
    let v' : Fin I × Loc V.K h := (i, .portOut k (portSlot I σ k i Q))
    have he : netMate I σ (v,1) = some (v',1) := by
      change netMate I σ ((ι, Loc.portIn k δ),1) = some ((i,.portOut k (portSlot I σ k i Q)),1)
      simpa only [hp, Option.map_some] using hm
    have hn : netMate I σ (v,1) ≠ none := by rw [he]; exact Option.some_ne_none _
    have hdisp : netDisp I σ (v,1) = 0 := by simp only [netDisp, he, disp1, v, v', add_zero]
    have hi : Owns I σ k i (Z / 2 ^ h) := by simpa only [hQ] using (prevOwner_spec hp).2.1
    have hz := owned_portBlock V I σ hi
    have hj : portLane h Z = j := (portBlock_type_lane I σ ι k δ δ.isLt j).2
    rw [hQ, hj] at hz
    rw [if_neg hn, hh, run_in (W := Wx) V B I σ ha bset (L.input w) he rfl l, hdisp, add_zero]
    change runHistory V B I σ (L.input w) k Z ((ι : ℕ) * 2 ^ h) =
      asWord Wx (runHistory V B I σ (L.input w) k (portBlock I σ i k (portSlot I σ k i Q) j)
        (((i : ℕ) + 1) * 2 ^ h))
    rw [asWord_self, hz]
    exact runHistory_prev V B I σ (L.input w) ι i k Z (by simpa only [hQ] using hp)

theorem run_ein_ok (ι : Fin I) (l : BitWord h) : RunSite V B I σ ha bset input L ι .eIn l := by
  let v : Fin I × Loc V.K h := (ι, .eIn)
  let j := laneEquiv h l
  change (if (ι : ℕ) = 0 then slotOut V B I σ ha zR v l 0 Wx =
    (if (j : ℕ) = 0 then encS V B V.initialState (fun _ => finOfInt B 0) else fun _ => false)
    else slotOut V B I σ ha zR v l 0 Wx = slotIn V B I σ ha zR v l 1 Wx)
  by_cases h0 : (ι : ℕ) = 0
  · rw [if_pos h0, run_state_source_out V B I σ ha bset input ι l, h0, Nat.zero_mul]
    exact runBoundary_initial V B h input j
  · let i : Fin I := ⟨(ι : ℕ) - 1, by have := ι.isLt; omega⟩
    let v' : Fin I × Loc V.K h := (i, .eOut)
    have hi : (i : ℕ) + 1 = ι := by dsimp only [i]; omega
    have hp : colPred ι = some i := by simp [colPred, show 0 < (ι : ℕ) by omega, i]
    have hm : netMate I σ (v, 1) = some (v', 1) := by simp [v, v', netMate, locMate, interMate, hp]
    have hd : netDisp I σ (v, 1) = 0 := by simp only [netDisp, hm, v, v', disp1, add_zero]
    rw [if_neg h0, run_state_source_out V B I σ ha bset input ι l,
      run_in (W := Wx) V B I σ ha bset input hm rfl l, hd, add_zero]
    change runBoundary V B h input ((ι : ℕ) * 2 ^ h) j = asWord Wx (runBoundary V B h input
      (((i : ℕ) + 1) * 2 ^ h) j)
    rw [asWord_self, hi]

/-- Pin readout requires no site-satisfaction hypothesis; it holds for the physical packed edges. -/
theorem run_owned_pin (ι : Fin I) (k : V.K) (Z : ℤ) (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portInput V B I σ ha zR ι k Z = runHistory V B I σ input k Z ((ι : ℕ) * 2 ^ h) := by
  let δ := portSlot I σ k ι (Z / 2 ^ h)
  let j := portLane h Z
  let l := (laneEquiv h).symm j
  have hv : ((typ δ : Fin 8) : ℕ) = (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  have hm : locMate (.portIn k δ : Loc V.K h) 0 = some (.rt k (rcol0 h) (code3 δ), 2) := rfl
  rw [portInput, portType_slot I σ ι k ho]
  change contentInput V B I σ ha zR ι k (typ δ,j) = _
  simp only [contentInput, hv]
  rw [slotIn_local V B I σ ha zR ι (locMate_symm hm) rfl rfl l Wx,
    run_port_source_out V B I σ ha bset input ι k δ l]
  change runHistory V B I σ input k (portBlock I σ ι k δ (laneEquiv h ((laneEquiv h).symm j))) _ = _
  rw [Equiv.apply_symm_apply, owned_portBlock V I σ ho]

theorem run_seedWord (k : V.K) (Z : ℤ) (ex : ∃ ι : Fin I, Owns I σ k ι (Z / 2 ^ h)) :
    seedWord V B I σ ha zR k Z = encC V B (initBlock (B := B) input k Z) := by
  rw [seedWord, dif_pos ex, run_owned_pin V B I σ ha bset input _ k Z (firstOwner_spec I σ k ex).1]
  exact runHistory_first V B I σ input _ k Z (firstOwner_prev I σ k ex)

end P1Net.AstraContract
