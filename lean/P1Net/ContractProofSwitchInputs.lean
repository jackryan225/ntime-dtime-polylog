import P1Net.ContractProofTerminals

/-! The source assumption for switch propagation is exactly the word on physical slot 2 of column zero. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) (input : List Bool)

local notation "zR" => runLabels V B I σ ha bset input
local notation "Wx" => strWidth V B

theorem run_content_port_input (ι : Fin I) (k : V.K) (δ : Fin 3) (j : Fin (2 ^ h)) :
    contentInput V B I σ ha zR ι k (typ δ, j) = runContentSource V B I σ input ι k (typ δ, j) := by
  have hδ : ((typ δ : Fin 8) : ℕ) = (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  have hm : locMate (.portIn k δ : Loc V.K h) 0 = some (.rt k (rcol0 h) (code3 δ), 2) := rfl
  simp only [contentInput, hδ]
  rw [slotIn_local V B I σ ha zR ι (locMate_symm hm) rfl rfl ((laneEquiv h).symm j) Wx,
    run_port_source_out V B I σ ha bset input ι k δ, Equiv.apply_symm_apply, runContentSource_port]

theorem run_content_table_input (ι : Fin I) (k : V.K) (δ : Fin 3) (j : Fin (2 ^ h)) :
    contentInput V B I σ ha zR ι k (typ (3 + δ), j) = runContentSource V B I σ input ι k (typ (3 + δ), j) := by
  have hd : ((typ (3 + δ) : Fin 8) : ℕ) = 3 + (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  have hm : locMate (.tabP (.cOut k δ) : Loc V.K h) 2 = some (.rt k (rcol0 h) (code3 (3 + δ)), 2) := rfl
  simp only [contentInput, hd]
  rw [run_local_in (W := Wx) V B I σ ha bset input ι (locMate_symm hm) rfl rfl rfl ((laneEquiv h).symm j),
    runContentSource_table]
  simp only [runRaw, Equiv.apply_symm_apply, if_neg (show (2 : Fin 4) ≠ 1 by decide),
    asWord_self, runStrings, extData]

theorem run_content_input (ι : Fin I) (k : V.K) (x : Fin 8 × Fin (2 ^ h)) :
    contentInput V B I σ ha zR ι k x = runContentSource V B I σ input ι k x := by
  obtain ⟨d,j⟩ := x
  by_cases h3 : (d : ℕ) < 3
  · let δ : Fin 3 := ⟨d, h3⟩
    have he : typ δ = d := Fin.ext (typ_val d.isLt)
    simpa only [he] using run_content_port_input V B I σ ha bset input ι k δ j
  · by_cases h6 : (d : ℕ) < 6
    · let δ : Fin 3 := ⟨(d : ℕ) - 3, by omega⟩
      have he : typ (3 + δ) = d := typ_window_eq d h3 h6
      simpa only [he] using run_content_table_input V B I σ ha bset input ι k δ j
    · rw [runContentSource_dummy V B I σ input ι k j d (by omega)]
      apply slotIn_unmated
      simp [netMate, locMate, colPred_col0, rtSrc, num3_code3 (d : ℕ) d.isLt, h3, h6, interMate]

theorem packed_content_item (π : BitWord 3) (l : BitWord h) :
    itemEquiv h (⟨num3 π, num3_lt π⟩, laneEquiv h l) = addrOf π l := by
  rw [item_addr, Equiv.symm_apply_apply, code3_num3]

theorem run_rt_zero (ι : Fin I) (k : V.K) (π : BitWord 3) (l : BitWord h) :
    slotIn V B I σ ha zR (ι,.rt k (rcol0 h) π) l 2 Wx =
      runContentSource V B I σ input ι k ((itemEquiv h).symm (addrOf π l)) := by
  have H := run_content_input V B I σ ha bset input ι k (⟨num3 π, num3_lt π⟩, laneEquiv h l)
  rw [← packed_content_item π l, Equiv.symm_apply_apply]
  simpa only [contentInput, Equiv.symm_apply_apply, code3_num3] using H

theorem run_st_zero (ι : Fin I) (π : BitWord 1) (l : BitWord h) :
    slotIn V B I σ ha zR (ι,.st (scol0 h) π) l 2 Wx =
      runStateSource V B h input ι ((stItemEquiv h).symm (addrOf π l)) := by
  let j := laneEquiv h l
  have p : π = code1 false ∨ π = code1 true := by revert π; decide
  rcases p with rfl | rfl
  · have hm : locMate (.eIn : Loc V.K h) 0 = some (.st (scol0 h) (code1 false), 2) := rfl
    have he : stItemEquiv h (0,j) = addrOf (code1 false) l := by
      simp only [state_addr_zero, j, Equiv.symm_apply_apply]
    rw [← he, Equiv.symm_apply_apply, slotIn_local V B I σ ha zR ι (locMate_symm hm) rfl rfl l Wx]
    exact run_state_source_out V B I σ ha bset input ι l
  · have hm : locMate (.tabP .stOut : Loc V.K h) 2 = some (.st (scol0 h) (code1 true), 2) := rfl
    have he : stItemEquiv h (1,j) = addrOf (code1 true) l := by
      simp only [state_addr_one, j, Equiv.symm_apply_apply]
    rw [← he, Equiv.symm_apply_apply, run_local_in (W := Wx) V B I σ ha bset input ι (locMate_symm hm) rfl rfl rfl l]
    exact (asWord_self _).trans (runStateAt_succ V B input ((ι : ℕ) * 2 ^ h + j)).symm

/-- The local switch predicate from the source, the previous physical arcs, and the prescribed outputs.
The last cross slot is unused by the factor. -/
theorem routeOK_from_canonical {m W : ℕ} [NeZero m] (s : Routing.Settings m)
    (src : Routing.Addr m → Fin W → Bool) (c : ℕ) (hc : c < 2 * m) (x : Routing.Addr m)
    (i₂ i₃ o₀ o₁ : Fin W → Bool)
    (h0 : c = 0 → i₂ = src x)
    (hprev : ∀ p, c = p + 1 → i₂ = canonicalArc s src p x false ∧
      i₃ = canonicalArc s src p (x + Routing.flip m p) true)
    (hout : o₀ = canonicalArc s src c x false)
    (hcross : c + 1 ≠ 2 * m → o₁ = canonicalArc s src c x true) :
    routeOK s c x i₂ i₃ o₀ o₁ := by
  have hi : selected s c x i₂ i₃ = prefixWord s src c x := by
    cases c with
    | zero => exact h0 rfl
    | succ p =>
      obtain ⟨h₂,h₃⟩ := hprev p rfl
      rw [h₂, h₃]
      exact canonical_step s src p hc x
  change sends s c x (selected s c x i₂ i₃) o₀ o₁
  rw [hi, hout]
  have H := canonical_sends s src c x
  by_cases hl : c + 1 = 2 * m
  · simpa only [sends, if_pos hl] using H
  · rw [hcross hl]
    exact H

theorem colLast_of_no_succ {n : ℕ} {c : Fin (2 * (n + 1))} (hp : colSucc c = none) : c = colLast n := by
  have hh : ¬ (c : ℕ) + 1 < 2 * (n + 1) := by
    intro hc
    simp only [colSucc, dif_pos hc] at hp
    cases hp
  apply Fin.ext
  change (c : ℕ) = 2 * (n + 1) - 1
  have := c.isLt
  omega

end P1Net.AstraContract
