import P1Net.ContractProofHistory

/-! What the contents arriving at a table or outgoing port say about the block history. -/

namespace P1Net.AstraContract

variable {K : Type} [Fintype K] [DecidableEq K] {P : Type*} {h : ℕ}
  (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

theorem accPerm_symm_apply (y : Fin 8 × Fin (2 ^ h)) :
    (accPerm I σ ι k).symm y = accPrev I σ ι k y := by
  let x := (accPerm I σ ι k).symm y
  have hx : accNext I σ ι k x = y := (accPerm I σ ι k).apply_symm_apply y
  exact (accPrev_accNext I σ ι k x).symm.trans (congrArg (accPrev I σ ι k) hx)

variable (port : ℤ → P) (write : ℕ → ℤ → P) (dummy : P)

/-- The word entering the first column at an item, indexed by its type and numerical lane. -/
def contentSource (x : Fin 8 × Fin (2 ^ h)) : P :=
  let Z := itemBlock I σ ι k x.1 x.2
  if (x.1 : ℕ) < 3 then port Z
  else if (x.1 : ℕ) < 6 then write ((ι : ℕ) * 2 ^ h + x.2) Z else dummy

theorem source_window {j : Fin (2 ^ h)} {Z : ℤ} (ha : Acc I σ ι k j Z) :
    contentSource I σ ι k port write dummy (typ (3 + slotAt I σ ι k j Z), j) =
      write ((ι : ℕ) * 2 ^ h + j) Z := by
  have hs := slotAt_lt I σ ι k ha
  have hv : ((typ (3 + slotAt I σ ι k j Z) : Fin 8) : ℕ) = 3 + slotAt I σ ι k j Z :=
    typ_val (by omega)
  simp only [contentSource, hv, if_neg (show ¬3 + slotAt I σ ι k j Z < 3 by omega),
    if_pos (show 3 + slotAt I σ ι k j Z < 6 by omega), itemBlock_window I σ ι k ha]

theorem source_port {Z : ℤ} (hlo : (bigQ I σ k ι - 1) * 2 ^ h ≤ Z)
    (hhi : Z < (bigQ I σ k ι + 2) * 2 ^ h) :
    contentSource I σ ι k port write dummy (typ (portType I σ ι k Z), portLane h Z) = port Z := by
  have hs := (portBlock_of_owned I σ ι k hlo hhi).1
  have hv : ((typ (portType I σ ι k Z) : Fin 8) : ℕ) = portType I σ ι k Z := typ_val (by omega)
  simp only [contentSource, hv, if_pos hs, itemBlock_port I σ ι k hlo hhi]

/-- Read the source delivered by the inverse permutation to a table input. -/
theorem delivered_window {j : Fin (2 ^ h)} {Z : ℤ} (ha : Acc I σ ι k j Z) :
    contentSource I σ ι k port write dummy
        ((accPerm I σ ι k).symm (typ (3 + slotAt I σ ι k j Z), j)) =
      match prevAcc I σ ι k Z j with
      | some u => write ((ι : ℕ) * 2 ^ h + u) Z
      | none => port Z := by
  rw [accPerm_symm_apply, accPrev_window I σ ι k ha]
  cases hp : prevAcc I σ ι k Z j with
  | some u => exact source_window I σ ι k port write dummy (prevAcc_spec hp).2.1
  | none =>
    obtain ⟨hlo, hhi⟩ := window_in_owned I σ ι k j ha
    exact source_port I σ ι k port write dummy hlo hhi

/-- Read the source delivered by the inverse permutation to an outgoing port. -/
theorem delivered_port {Z : ℤ} (hlo : (bigQ I σ k ι - 1) * 2 ^ h ≤ Z)
    (hhi : Z < (bigQ I σ k ι + 2) * 2 ^ h) :
    contentSource I σ ι k port write dummy
        ((accPerm I σ ι k).symm (typ (portType I σ ι k Z), portLane h Z)) =
      match lastAcc I σ ι k Z with
      | some u => write ((ι : ℕ) * 2 ^ h + u) Z
      | none => port Z := by
  rw [accPerm_symm_apply, accPrev_port I σ ι k hlo hhi]
  cases hp : lastAcc I σ ι k Z with
  | some u => exact source_window I σ ι k port write dummy (lastAcc_spec hp).1
  | none => exact source_port I σ ι k port write dummy hlo hhi

theorem bounds_of_owns {Z : ℤ} (ho : Owns I σ k ι (Z / 2 ^ h)) :
    (bigQ I σ k ι - 1) * 2 ^ h ≤ Z ∧ Z < (bigQ I σ k ι + 2) * 2 ^ h := by
  have hN : (0 : ℤ) < 2 ^ h := by positivity
  obtain ⟨hl, hr⟩ := ho
  exact ⟨(Int.le_ediv_iff_mul_le hN).1 hl, (Int.ediv_lt_iff_lt_mul hN).1 (by omega)⟩

theorem delivered_dummy (t : Fin 8) (j : Fin (2 ^ h)) (ht : 6 ≤ (t : ℕ)) :
    contentSource I σ ι k port write dummy ((accPerm I σ ι k).symm (t, j)) = dummy := by
  have h3 : ¬ (t : ℕ) < 3 := by omega
  have h6 : ¬ (t : ℕ) < 6 := by omega
  rw [accPerm_symm_apply]
  simp only [accPrev, h3, h6, if_false, contentSource]

section OwnerInduction

variable (Z : ℤ) (initial : P) (updates : ℕ → P) (pin pout : Fin I → P)

/-- Given the pin at the first owner, the intervening owners and tables force both port values.
Only values at owners of the chosen block are constrained. -/
theorem port_values_unique
    (hin : ∀ i : Fin I, Owns I σ k i (Z / 2 ^ h) →
      pin i = match prevOwner I σ k i (Z / 2 ^ h) with
        | none => initial
        | some p => pout p)
    (hout : ∀ i : Fin I, Owns I σ k i (Z / 2 ^ h) →
      pout i = match lastAcc I σ i k Z with
        | none => pin i
        | some j => updates ((i : ℕ) * 2 ^ h + j)) :
    ∀ i : Fin I, Owns I σ k i (Z / 2 ^ h) →
      pin i = valueAt σ k Z initial updates ((i : ℕ) * 2 ^ h) ∧
      pout i = valueAt σ k Z initial updates (((i : ℕ) + 1) * 2 ^ h) := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro ho
    have hi : pin i = valueAt σ k Z initial updates ((i : ℕ) * 2 ^ h) := by
      rw [hin i ho, valueAt_owner I σ i k Z initial updates]
      cases hp : prevOwner I σ k i (Z / 2 ^ h) with
      | none => rfl
      | some j =>
        obtain ⟨hlt, hj, _⟩ := prevOwner_spec hp
        exact (ih j hlt hj).2
    refine ⟨hi, ?_⟩
    rw [hout i ho, valueAt_end I σ i k Z initial updates]
    cases lastAcc I σ i k Z with
    | none => exact hi
    | some j => rfl

end OwnerInduction

end P1Net.AstraContract
