import P1Net.ContractProofPorts

/-! From a physical labelling to the last-access equation at every table input. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : RoutedGood V B L I σ ha bset)

noncomputable def tableAt (t : ℕ) : LocalIn V B :=
  let i : Fin (I * 2 ^ h) := if ht : t < I * 2 ^ h then ⟨t, ht⟩ else 0
  let p := (intervalEquiv I h).symm i
  centerData V B L I σ ha bset z p.1 p.2

theorem tableAt_lane (ι : Fin I) (j : Fin (2 ^ h)) :
    tableAt V B L I σ ha bset z ((ι : ℕ) * 2 ^ h + j) =
      centerData V B L I σ ha bset z ι ((laneEquiv h).symm j) := by
  let l := (laneEquiv h).symm j
  have hv : (intervalEquiv I h (ι, l) : ℕ) = (ι : ℕ) * 2 ^ h + j := by
    simp only [intervalEquiv_val, l, Equiv.apply_symm_apply]
  have ht : (ι : ℕ) * 2 ^ h + j < I * 2 ^ h := hv ▸ (intervalEquiv I h (ι, l)).isLt
  have hi : (⟨(ι : ℕ) * 2 ^ h + j, ht⟩ : Fin (I * 2 ^ h)) = intervalEquiv I h (ι, l) :=
    Fin.ext hv.symm
  simp only [tableAt, dif_pos ht, hi, Equiv.symm_apply_apply, l]

/-- Encoded contents after interval `t`, for each block in that interval's window. -/
noncomputable def writeWord (k : V.K) (t : ℕ) (Z : ℤ) : Fin (strWidth V B) → Bool :=
  encC V B ((evolve (tableAt V B L I σ ha bset z t)).blocks k (slotOf σ k t Z))

variable (ι : Fin I) (k : V.K)

theorem input_as_source (x : Fin 8 × Fin (2 ^ h)) :
    contentInput V B I σ ha z.val ι k x =
      contentSource I σ ι k (portInput V B I σ ha z.val ι k)
        (writeWord V B L I σ ha bset z k) (fun _ => false) x := by
  obtain ⟨t, j⟩ := x
  by_cases h3 : (t : ℕ) < 3
  · obtain ⟨ht, hj⟩ := portBlock_type_lane I σ ι k t h3 j
    have htyp : typ (t : ℕ) = t := Fin.ext (typ_val t.isLt)
    simp only [contentSource, if_pos h3, itemBlock, portInput, ht, hj, htyp]
  · by_cases h6 : (t : ℕ) < 6
    · let δ : Fin 3 := ⟨(t : ℕ) - 3, by omega⟩
      have ht : typ (3 + δ) = t := typ_window_eq t h3 h6
      have hz : itemBlock I σ ι k t j = slotBlock σ k ((ι : ℕ) * 2 ^ h + j) δ := by
        simp only [itemBlock, if_neg h3, slotBlock, laneBeta, δ]
      have he := input_from_table V B L I σ ha bset z ι k δ j
      rw [ht] at he
      simpa only [contentSource, if_neg h3, if_pos h6, writeWord, hz, slotOf_slotBlock,
        tableAt_lane] using (show contentInput V B I σ ha z.val ι k (t, j) =
          encC V B ((evolve (centerData V B L I σ ha bset z ι ((laneEquiv h).symm j))).blocks k δ)
          from he)
    · simpa only [contentSource, if_neg h3, if_neg h6] using
        input_dummy V B L I σ ha bset z ι k t (by omega) j

theorem physical_owner_out (Z : ℤ) (ho : Owns I σ k ι (Z / 2 ^ h))
    (hr : Routing.route (bset (3 + h) (accAddr I σ ι k)) = accAddr I σ ι k) :
    portOutput V B I σ ha z.val ι k Z =
      match lastAcc I σ ι k Z with
      | none => portInput V B I σ ha z.val ι k Z
      | some j => writeWord V B L I σ ha bset z k ((ι : ℕ) * 2 ^ h + j) Z := by
  obtain ⟨hl, hh⟩ := bounds_of_owns I σ ι k ho
  rw [portOutput, content_delivery V B L I σ ha bset z ι k hr,
    input_as_source V B L I σ ha bset z ι k]
  rw [delivered_port I σ ι k _ _ _ hl hh]
  cases lastAcc I σ ι k Z <;> rfl

theorem physical_port_values
    (route : ∀ (i : Fin I) (k' : V.K),
      Routing.route (bset (3 + h) (accAddr I σ i k')) = accAddr I σ i k')
    (Z : ℤ) (ho : Owns I σ k ι (Z / 2 ^ h)) :
    let val := valueAt σ k Z (seedWord V B I σ ha z.val k Z)
      (fun t => writeWord V B L I σ ha bset z k t Z)
    portInput V B I σ ha z.val ι k Z = val ((ι : ℕ) * 2 ^ h) ∧
      portOutput V B I σ ha z.val ι k Z = val (((ι : ℕ) + 1) * 2 ^ h) :=
  port_values_unique I σ k Z _ _
    (fun i => portInput V B I σ ha z.val i k Z) (fun i => portOutput V B I σ ha z.val i k Z)
    (fun i hi => physical_owner_in V B L I σ ha bset z i k Z hi)
    (fun i hi => physical_owner_out V B L I σ ha bset z i k Z hi (route i k)) ι ho

/-- The content constraint of a real table, expressed in the global time of the access network. -/
theorem table_input_history (j : Fin (2 ^ h)) (δ : Fin 3)
    (route : ∀ (i : Fin I) (k' : V.K),
      Routing.route (bset (3 + h) (accAddr I σ i k')) = accAddr I σ i k') :
    let t := (ι : ℕ) * 2 ^ h + j
    let Z := slotBlock σ k t δ
    encC V B ((tableAt V B L I σ ha bset z t).blocks k δ) =
      valueAt σ k Z (seedWord V B I σ ha z.val k Z)
        (fun u => writeWord V B L I σ ha bset z k u Z) t := by
  let t : ℕ := (ι : ℕ) * 2 ^ h + j
  let Z := slotBlock σ k t δ
  have hz : Acc I σ ι k j Z := acc_slot I σ ι k j δ δ.isLt
  have hs : slotAt I σ ι k j Z = (δ : ℕ) := slotAt_slot I σ ι k j δ δ.isLt
  have hown : Owns I σ k ι (Z / 2 ^ h) := by
    obtain ⟨hl, hr⟩ := window_in_owned I σ ι k j hz
    have hN : (0 : ℤ) < 2 ^ h := by positivity
    have hh : Z / 2 ^ h < bigQ I σ k ι + 2 := (Int.ediv_lt_iff_lt_mul hN).2 hr
    exact ⟨(Int.le_ediv_iff_mul_le hN).2 hl, by omega⟩
  have hin := (physical_port_values V B L I σ ha bset z ι k route Z hown).1
  have hd := delivered_window I σ ι k (portInput V B I σ ha z.val ι k)
    (writeWord V B L I σ ha bset z k) (fun _ => false) hz
  rw [hs] at hd
  have wire := (output_to_table V B L I σ ha bset z ι k δ j).symm.trans
    ((content_delivery V B L I σ ha bset z ι k (route ι k) (typ (3 + δ), j)).trans
      (input_as_source V B L I σ ha bset z ι k _))
  change encC V B ((tableAt V B L I σ ha bset z ((ι : ℕ) * 2 ^ h + j)).blocks k δ) = _
  rw [tableAt_lane, wire, hd, valueAt_lane I σ ι k Z]
  cases prevAcc I σ ι k Z j with
  | none => exact hin
  | some u => rfl

end P1Net.AstraContract
