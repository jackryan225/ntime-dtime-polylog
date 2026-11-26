import P1Net.Reduce

/-! The cardinality reduction for the routed contraction. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open scoped Classical

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

/-- Some big interval has an incoming port for the big block of this guess cell. -/
abbrev HasPort (j : Fin g) : Prop :=
  ∃ ι : Fin I, Owns I σ (L.cellOf j).1 ι ((L.cellOf j).2 / (B : ℤ) / ((2 ^ h : ℕ) : ℤ))

/-- The first port records these bits even though no table reads their small block. -/
abbrev ExtraCell := {j : Fin g // ¬ Seen B σ L j ∧ HasPort V B L I σ j}

theorem seen_hasPort {j : Fin g} (hs : Seen B σ L j) : HasPort V B L I σ j := by
  obtain ⟨ι, hι, ho⟩ := ownedGuess_of_seen (B := B) L σ (Nat.two_pow_pos h) rfl hs
  exact ⟨⟨ι, hι⟩, (owns_iff_ownsDir I σ _ ι _).2 ho⟩

/-- Partition the unseen cells before taking cardinalities, including when either part is empty. -/
noncomputable def splitUnseen :
    {j : Fin g // ¬ Seen B σ L j} ≃
      {j : Fin g // UnownedCell V B L I σ j} ⊕ ExtraCell V B L I σ where
  toFun x := if hp : HasPort V B L I σ x.1 then Sum.inr ⟨x.1, x.2, hp⟩ else Sum.inl ⟨x.1, hp⟩
  invFun := Sum.elim
    (fun j => ⟨j.1, fun hs => j.2 (seen_hasPort V B L I σ hs)⟩)
    (fun j => ⟨j.1, j.2.1⟩)
  left_inv x := by
    dsimp only
    split <;> rfl
  right_inv x := by
    rcases x with ⟨j, hj⟩ | ⟨j, hs, hp⟩
    · change (if h' : HasPort V B L I σ j then _ else _) = _
      rw [dif_neg hj]
      rfl
    · change (if h' : HasPort V B L I σ j then _ else _) = _
      rw [dif_pos hp]
      rfl

theorem unseen_eq_unowned_add_extra :
    unseenCount B σ L = uOwned V B L I σ + Fintype.card (ExtraCell V B L I σ) := by
  simpa only [unseenCount, uOwned, Fintype.card_sum] using
    Fintype.card_congr (splitUnseen V B L I σ)

/-- A routed labelling that satisfies the local predicates, before site scalars. -/
abbrev RoutedGood :=
  {z : (e : (rnState V B I σ ha).network.Edge) → (rnState V B I σ ha).network.Payload e //
    ∀ u, rnSiteOK V B L I σ ha bset u
      (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u)}

abbrev AccessGood :=
  {z : (e : (net B σ).Edge) → (net B σ).Payload e // GoodZ L σ z}

theorem routed_contract_card (R : Type*) [CommRing R] :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha bset R) =
      (2 : R) ^ uOwned V B L I σ * (Fintype.card (RoutedGood V B L I σ ha bset) : R) := by
  rw [contract_rnFactors, Fintype.card_subtype]

theorem access_contract_card (R : Type*) [CommRing R] :
    contract (net B σ) (fac B σ L R) =
      (2 : R) ^ unseenCount B σ L * (Fintype.card (AccessGood V B L I σ) : R) := by
  rw [contract_net B σ L R, Fintype.card_subtype]
  congr 3
  exact Finset.filter_congr fun z _ => Iff.rfl

/-- The geometric equivalence suffices over every coefficient ring. -/
theorem count_of_equiv (R : Type*) [CommRing R]
    (e : RoutedGood V B L I σ ha bset ≃ AccessGood V B L I σ × (ExtraCell V B L I σ → Bool)) :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
        MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧
          skeleton V (L.input w) B (I * 2 ^ h) = σ).card : R) := by
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool] at hc
  rw [routed_contract_card, ← contract_eq_count (B := B) L σ R, access_contract_card,
    hc, unseen_eq_unowned_add_extra, pow_add]
  push_cast
  ring

/-- The second guess bit of `withGuess` is owned and unseen in the stationary two-lane example. -/
theorem stationary_extra (M : FiniteMultiTapeMachine) :
    Nonempty (ExtraCell (h := 1) M 1 (withGuessLayout (M := M) [] 2) 1 (fun _ _ => 1)) := by
  let τ : Fin (1 * 2 ^ 1) → M.K → Fin 3 := fun _ _ => 1
  have hβ (k : M.K) : ∀ t, betaOf τ k t = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [betaOf, ih]
      split <;> rfl
  refine ⟨⟨(1 : Fin 2), ?_, ?_⟩⟩
  · rintro ⟨i, δ, he⟩
    change (3 : ℤ) / 1 = slotBlock τ M.inputTape i δ at he
    rw [Int.ediv_one, slotBlock, hβ] at he
    have hδ := δ.isLt
    omega
  · refine ⟨(0 : Fin 1), ?_⟩
    change Owns 1 τ M.inputTape (0 : ℕ) ((3 : ℤ) / 1 / 2)
    simp only [Owns, bigQ, hβ] <;> decide

end P1Net.AstraContract
