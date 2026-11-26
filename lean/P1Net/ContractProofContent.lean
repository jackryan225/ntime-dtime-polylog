import P1Net.ContractProofWords
import P1Net.ContractProofAccess
import P1Net.GlueRouting

/-! Decoding actual content wires at the two ends of a routed permutation. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ}

theorem typeEquiv_code (t : Fin 8) : typeEquiv (code3 t) = t := by
  revert t
  decide

theorem item_addr (t : Fin 8) (j : Fin (2 ^ h)) :
    itemEquiv h (t, j) = addrOf (code3 t) ((laneEquiv h).symm j) := by
  change addrOf (typeEquiv.symm t) ((laneEquiv h).symm j) = _
  have e : typeEquiv.symm t = code3 t := by
    apply typeEquiv.injective
    rw [Equiv.apply_symm_apply, typeEquiv_code]
  rw [e]

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

noncomputable def contentInput (z : Labels V B I σ ha) (ι : Fin I) (k : V.K)
    (x : Fin 8 × Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  slotIn V B I σ ha z (ι, .rt k (rcol0 h) (code3 x.1)) ((laneEquiv h).symm x.2) 2 (strWidth V B)

noncomputable def contentOutput (z : Labels V B I σ ha) (ι : Fin I) (k : V.K)
    (y : Fin 8 × Fin (2 ^ h)) : Fin (strWidth V B) → Bool :=
  slotOut V B I σ ha z (ι, .rt k (rcolLast h) (code3 y.1)) ((laneEquiv h).symm y.2) 0 (strWidth V B)

variable (z : RoutedGood V B L I σ ha bset) (ι : Fin I) (k : V.K)

theorem rt_at_input (s : Routing.Settings (3 + h)) (x : Fin 8 × Fin (2 ^ h)) :
    rtPos V B I σ ha z.val ι k s 0 (itemEquiv h x) = contentInput V B I σ ha z.val ι k x := by
  obtain ⟨t, j⟩ := x
  have h0 : 0 < 2 * (h + 3) := by omega
  rw [item_addr]
  simp only [rtPos, dif_pos h0, ↓reduceIte, addrSplit_addrOf] <;> rfl

theorem rt_at_output (y : Fin 8 × Fin (2 ^ h)) :
    contentOutput V B I σ ha z.val ι k y =
      rtPos V B I σ ha z.val ι k (bset (3 + h) (accAddr I σ ι k)) (2 * (h + 3) - 1)
        (itemEquiv h y) := by
  obtain ⟨t, j⟩ := y
  have hn : 2 * (h + 3) - 1 < 2 * (h + 3) := by omega
  have hl : ((rcolLast h : Fin (2 * (h + 3))) : ℕ) + 1 = 2 * (3 + h) := by
    change 2 * (h + 3) - 1 + 1 = 2 * (3 + h)
    omega
  have hr := rt_routeOK V B L I σ ha bset z.val z.property ι k
    (rcolLast h) (code3 t) ((laneEquiv h).symm j)
  simp only [routeOK, if_pos hl] at hr
  rw [item_addr]
  simp only [rtPos, dif_pos hn, addrSplit_addrOf]
  exact hr

/-- Output item `y` receives the physical input word at the inverse access permutation of `y`. -/
theorem content_delivery
    (hr : Routing.route (bset (3 + h) (accAddr I σ ι k)) = accAddr I σ ι k)
    (y : Fin 8 × Fin (2 ^ h)) :
    contentOutput V B I σ ha z.val ι k y =
      contentInput V B I σ ha z.val ι k ((accPerm I σ ι k).symm y) := by
  let x := (accPerm I σ ι k).symm y
  have haddr : accAddr I σ ι k (itemEquiv h x) = itemEquiv h y := by
    simp only [accAddr, Equiv.permCongr_apply, Equiv.symm_apply_apply, x, Equiv.apply_symm_apply]
  have e := rt_route V B L I σ ha bset z.val z.property ι k (itemEquiv h x)
  have hc : Routing.routeUpTo (bset (3 + h) (accAddr I σ ι k)) (2 * (h + 3) - 1) = accAddr I σ ι k := by
    rw [show h + 3 = 3 + h by omega]
    exact hr
  rw [hc, haddr] at e
  exact (rt_at_output V B L I σ ha bset z ι k y).trans
    (e.trans (rt_at_input V B L I σ ha bset z ι k _ x))

theorem input_from_port (δ : Fin 3) (j : Fin (2 ^ h)) :
    contentInput V B I σ ha z.val ι k (typ δ, j) =
      slotOut V B I σ ha z.val (ι, .portIn k δ) ((laneEquiv h).symm j) 0 (strWidth V B) := by
  have ht : ((typ δ : Fin 8) : ℕ) = (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  simp only [contentInput, ht]
  have hm : locMate (.portIn k δ : Loc V.K h) 0 = some (.rt k (rcol0 h) (code3 δ), 2) := by
    simp only [locMate, ↓reduceIte]
  exact slotIn_local V B I σ ha z.val ι (locMate_symm hm) rfl rfl _ _

theorem output_to_port (δ : Fin 3) (j : Fin (2 ^ h)) :
    contentOutput V B I σ ha z.val ι k (typ δ, j) =
      slotIn V B I σ ha z.val (ι, .portOut k δ) ((laneEquiv h).symm j) 0 (strWidth V B) := by
  have ht : ((typ δ : Fin 8) : ℕ) = (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  simp only [contentOutput, ht]
  symm
  have hm : locMate (.portOut k δ : Loc V.K h) 0 = some (.rt k (rcolLast h) (code3 δ), 0) := by
    simp only [locMate, ↓reduceIte]
  exact slotIn_local V B I σ ha z.val ι hm rfl rfl _ _

theorem input_from_table (δ : Fin 3) (j : Fin (2 ^ h)) :
    let d := centerData V B L I σ ha bset z ι ((laneEquiv h).symm j)
    contentInput V B I σ ha z.val ι k (typ (3 + δ), j) = encC V B ((evolve d).blocks k δ) := by
  have ht : ((typ (3 + δ) : Fin 8) : ℕ) = 3 + (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  have hm : locMate (.tabP (.cOut k δ) : Loc V.K h) 2 = some (.rt k (rcol0 h) (code3 (3 + δ)), 2) := by
    simp [locMate, extAttach]
  simp only [contentInput, ht]
  exact (slotIn_local V B I σ ha z.val ι (locMate_symm hm) rfl rfl _ _).trans
    (external_eq V B L I σ ha bset z ι ((laneEquiv h).symm j) (.cOut k δ))

theorem output_to_table (δ : Fin 3) (j : Fin (2 ^ h)) :
    let d := centerData V B L I σ ha bset z ι ((laneEquiv h).symm j)
    contentOutput V B I σ ha z.val ι k (typ (3 + δ), j) = encC V B (d.blocks k δ) := by
  have ht : ((typ (3 + δ) : Fin 8) : ℕ) = 3 + (δ : ℕ) := typ_val (by have := δ.isLt; omega)
  have hm : locMate (.tabP (.cIn k δ) : Loc V.K h) 2 = some (.rt k (rcolLast h) (code3 (3 + δ)), 0) := by
    simp [locMate, extAttach]
  simp only [contentOutput, ht]
  exact (slotIn_local V B I σ ha z.val ι hm rfl rfl _ _).symm.trans
    (external_eq V B L I σ ha bset z ι ((laneEquiv h).symm j) (.cIn k δ))

theorem input_dummy (t : Fin 8) (ht : 6 ≤ (t : ℕ)) (j : Fin (2 ^ h)) :
    contentInput V B I σ ha z.val ι k (t, j) = fun _ => false := by
  apply slotIn_unmated
  have h3 : ¬ (t : ℕ) < 3 := by omega
  have h6 : ¬ (t : ℕ) < 6 := by omega
  simp [netMate, locMate, colPred_col0, rtSrc, num3_code3 (t : ℕ) t.isLt, h3, h6, interMate]

end P1Net.AstraContract
