import P1Net.ContractProofDecode

/-! The inverse laws needed of a constructor for physical labellings. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open scoped Classical

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

/-- Agreement at every first pin suffices for recovery of the original guess after completion. -/
theorem completedGuess_eq_of_seedWords (z : RoutedGood V B L I σ ha bset) (w : Fin g → Bool)
    (pins : ∀ k Z, (∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) →
      seedWord V B I σ ha z.val k Z = encC V B (initBlock (B := B) (L.input w) k Z)) :
    completedGuess V B L I σ ha bset z (fun j => w j) = w := by
  funext j
  by_cases ho : HasPort V B L I σ j
  · let k := (L.cellOf j).1
    let c := (L.cellOf j).2
    let Z := c / B
    have ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h) := (hasPort_iff V B L I σ j).1 ho
    have he : seedBlock V B L I σ ha bset z k Z = initBlock (B := B) (L.input w) k Z :=
      encC_injective V B ((seedBlock_spec V B L I σ ha bset z k Z ex).2.symm.trans (pins k Z ex))
    have hB : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
    have hc : Z * B + ((finOfInt B (c % B) : Fin B) : ℤ) = c := by
      rw [finOfInt_val B (Int.emod_nonneg _ hB.ne') (Int.emod_lt_of_pos _ hB)]
      exact Int.ediv_mul_add_emod _ _
    rw [completedGuess, dif_pos ho]
    change symInv (seedBlock V B L I σ ha bset z k Z (finOfInt B (c % B))) = w j
    rw [he]
    change symInv ((absRun V (L.input w) 0).cells k (Z * B + ((finOfInt B (c % B) : Fin B) : ℤ))) = w j
    rw [hc, L.init_some w k c j (L.guessAt_cellOf j), symInv_sym]
  · simp only [completedGuess, dif_neg ho]

abbrev GoodGuess := {w : Fin g → Bool // GoodW (B := B) L σ w}

noncomputable def equivOfEncoder (route : Routes bset)
    (encode : GoodGuess V B L I σ → RoutedGood V B L I σ ha bset)
    (pins : ∀ (w : GoodGuess V B L I σ) k Z, (∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) →
      seedWord V B I σ ha (encode w).val k Z = encC V B (initBlock (B := B) (L.input w.val) k Z))
    (recover : ∀ (z : RoutedGood V B L I σ ha bset) (b : UnownedBits V B L I σ),
      encode ⟨completedGuess V B L I σ ha bset z b, completed_good V B L I σ ha bset z route b⟩ = z) :
    GoodGuess V B L I σ ≃ RoutedGood V B L I σ ha bset × UnownedBits V B L I σ where
  toFun w := (encode w, fun j => w.val j)
  invFun p := ⟨completedGuess V B L I σ ha bset p.1 p.2, completed_good V B L I σ ha bset p.1 route p.2⟩
  left_inv w := Subtype.ext (completedGuess_eq_of_seedWords V B L I σ ha bset (encode w) w.val (pins w))
  right_inv p := Prod.ext (recover p.1 p.2)
    (funext (completedGuess_unowned V B L I σ ha bset p.1 p.2))

theorem count_of_completion (R : Type*) [CommRing R]
    (e : GoodGuess V B L I σ ≃ RoutedGood V B L I σ ha bset × UnownedBits V B L I σ) :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
        MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧
          skeleton V (L.input w) B (I * 2 ^ h) = σ).card : R) := by
  have hc : Fintype.card (GoodGuess V B L I σ) =
      Fintype.card (RoutedGood V B L I σ ha bset) * 2 ^ uOwned V B L I σ := by
    simpa only [Fintype.card_prod, UnownedBits, Fintype.card_fun, Fintype.card_bool, uOwned] using
      Fintype.card_congr e
  have hg : Fintype.card (GoodGuess V B L I σ) = (Finset.univ.filter (GoodW (B := B) L σ)).card :=
    Fintype.card_subtype _
  rw [routed_contract_card, mul_comm]
  have h2 := congrArg (fun n : ℕ => (n : R)) (hg.symm.trans hc)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h2
  convert h2.symm using 3
  all_goals (ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Iff.rfl)

end P1Net.AstraContract
