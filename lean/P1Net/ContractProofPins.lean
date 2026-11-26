import P1Net.ContractProofMemory

/-! Reconstruct one common guess from the first ports and the free unowned bits. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open scoped Classical

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : RoutedGood V B L I σ ha bset)

abbrev UnownedBits := {j : Fin g // UnownedCell V B L I σ j} → Bool

theorem hasPort_iff (j : Fin g) :
    HasPort V B L I σ j ↔ ∃ i : Fin I,
      Owns I σ (L.cellOf j).1 i ((L.cellOf j).2 / (B : ℤ) / (2 ^ h : ℤ)) := by
  simp only [HasPort, Nat.cast_pow, Nat.cast_ofNat]

/-- The decoded first pin. Only an owned block has a pin. -/
noncomputable def seedBlock (k : V.K) (Z : ℤ) : Fin B → V.Γ :=
  if ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h) then
    Classical.choose (seed_pin V B L I σ ha bset z k Z ex)
  else fun _ => default

theorem seedBlock_spec (k : V.K) (Z : ℤ) (ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) :
    PinOK B L k Z (seedBlock V B L I σ ha bset z k Z) ∧
      seedWord V B I σ ha z.val k Z = encC V B (seedBlock V B L I σ ha bset z k Z) := by
  simp only [seedBlock, dif_pos ex]
  exact Classical.choose_spec (seed_pin V B L I σ ha bset z k Z ex)

noncomputable def bitFromPort (j : Fin g) : Bool :=
  symInv (M := V) (seedBlock V B L I σ ha bset z (L.cellOf j).1 ((L.cellOf j).2 / B)
    (finOfInt B ((L.cellOf j).2 % B)))

/-- A total guess, with one arbitrary bit exactly where the routed network has no port. -/
noncomputable def completedGuess (free : UnownedBits V B L I σ) (j : Fin g) : Bool :=
  if ho : HasPort V B L I σ j then bitFromPort V B L I σ ha bset z j else free ⟨j, ho⟩

theorem completedGuess_unowned (free : UnownedBits V B L I σ)
    (j : {j : Fin g // UnownedCell V B L I σ j}) :
    completedGuess V B L I σ ha bset z free j = free j := by
  simp only [completedGuess, dif_neg j.property]

/-- Every decoded first pin, including blocks with no accessed cell, is the actual initial block
of the same completed guess. -/
theorem seedBlock_initial (free : UnownedBits V B L I σ) (k : V.K) (Z : ℤ)
    (ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) :
    seedBlock V B L I σ ha bset z k Z =
      initBlock (B := B) (L.input (completedGuess V B L I σ ha bset z free)) k Z := by
  let w := completedGuess V B L I σ ha bset z free
  funext o
  let c : ℤ := Z * B + o
  have po := (seedBlock_spec V B L I σ ha bset z k Z ex).1 o
  change seedBlock V B L I σ ha bset z k Z o = (absRun V (L.input w) 0).cells k c
  cases hg : L.guessAt k c with
  | none => exact (po.2 hg).trans (L.init_none w k c hg).symm
  | some j =>
    have hcell : L.cellOf j = (k, c) := by
      obtain ⟨hk, hc⟩ := L.guessAt_inj _ _ _ _ j (L.guessAt_cellOf j) hg
      exact Prod.ext hk hc
    have hB : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
    have h0 : (0 : ℤ) ≤ (o : ℤ) := by positivity
    have h1 : (o : ℤ) < B := by exact_mod_cast o.isLt
    have hdiv : c / B = Z := ediv_eq_of_bounds hB (by dsimp only [c]; linarith)
      (by dsimp only [c]; linarith)
    have hmod : c % B = (o : ℤ) := by
      dsimp only [c]
      rw [add_comm, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt h0 h1
    have ho : HasPort V B L I σ j := by
      rw [hasPort_iff, hcell]
      simpa only [hdiv] using ex
    obtain ⟨bit, hbit⟩ := po.1 j hg
    have hw : w j = bit := by
      simp only [w, completedGuess, dif_pos ho, bitFromPort, hcell, hdiv, hmod, finOfInt_coe, hbit, symInv_sym]
    rw [L.init_some w k c j hg, hw]
    exact hbit

/-- The content field of `P1Net.Valid` for the tables extracted from a satisfying routed
labelling. This statement uses the access network's own `wired`. -/
theorem table_content_valid
    (route : ∀ (m : ℕ) [NeZero m] (π : Equiv.Perm (Routing.Addr m)), Routing.route (bset m π) = π)
    (free : UnownedBits V B L I σ) (t : ℕ) (ht : t < I * 2 ^ h) (k : V.K) (δ : Fin 3) :
    (tableAt V B L I σ ha bset z t).blocks k δ =
      wired σ (L.input (completedGuess V B L I σ ha bset z free))
        (fun u => evolve (tableAt V B L I σ ha bset z u)) t k δ := by
  let Z := slotBlock σ k t δ
  let ι : Fin I := ⟨t / 2 ^ h, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).2 ht⟩
  let j : Fin (2 ^ h) := ⟨t % 2 ^ h, Nat.mod_lt _ (Nat.two_pow_pos h)⟩
  have ht' : (ι : ℕ) * 2 ^ h + j = t := Nat.div_add_mod' _ _
  have ho : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h) :=
    ⟨ι, owns_at_time I σ k Z ht (slot_inWindow σ k t δ)⟩
  have e : encC V B ((tableAt V B L I σ ha bset z t).blocks k δ) =
      valueAt σ k Z (seedWord V B I σ ha z.val k Z) (fun u => writeWord V B L I σ ha bset z k u Z) t := by
    simpa only [ht', Z] using table_input_history V B L I σ ha bset z ι k j δ (fun i k' => route _ _)
  rw [(seedBlock_spec V B L I σ ha bset z k Z ho).2, seedBlock_initial V B L I σ ha bset z free k Z ho] at e
  apply encC_injective V B
  simp only [wired]
  cases hp : prevAccess σ k (slotBlock σ k t δ) t <;> simpa only [valueAt, Z, hp, writeWord] using e

end P1Net.AstraContract
