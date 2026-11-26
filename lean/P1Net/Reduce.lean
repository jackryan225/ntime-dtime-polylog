import P1Net.Owners

/-!
# P4 for the routed network, reduced to a bijection of finite sets

Lane P1-lean-net (2026-11-25, restart). Two steps of the glue that need nothing about runs:
* `contract_rnFactors`: the contraction is `2 ^ uOwned` times the number of edge labellings at which every site
  predicate `rnSiteOK` holds (any commutative ring; no power of two is cancelled).
* `contractEqCount_of_equiv`: `ContractEqCount` follows from an equivalence
  `{z // all rnSiteOK} × ({j // UnownedCell j} → Bool) ≃ {w // accepts within I 2^h B ∧ skeleton = σ}`
  given for every `bset` that routes every permutation.
So the rest of P4 is the bijection: a labelling with all predicates true is the run of one guess, read off at the
owned guess cells; the unowned guess cells are free.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ}

section Factors

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

/-- The edge labellings of `N_{x,σ}` at which every site predicate holds. -/
abbrev RnOK (z : (e : (rnState V B I σ ha).network.Edge) → (rnState V B I σ ha).network.Payload e) : Prop :=
  ∀ u, rnSiteOK V B L I σ ha bset u
    (edgeAssignment (rnState V B I σ ha).network.src (rnState V B I σ ha).network.dst z u)

/-- The good guesses: the run accepts within `I 2^h B` steps and has skeleton `σ`. -/
abbrev RnGood (w : Fin g → Bool) : Prop :=
  MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧ skeleton V (L.input w) B (I * 2 ^ h) = σ

open scoped Classical in
/-- **The scalar.** Contraction of `rnFactors` = `2 ^ uOwned` · #(labellings with every site predicate true). -/
theorem contract_rnFactors (R : Type*) [CommRing R] :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha bset R) =
      (2 : R) ^ uOwned V B L I σ *
        ((Finset.univ.filter fun z => RnOK V B L I σ ha bset z).card : R) := by
  have e := contract_scaled_indicator (R := R) (rnState V B I σ ha).network
    (fun u => if u = scalarSite V B I σ ha then (2 : R) ^ uOwned V B L I σ else 1)
    (fun u z => rnSiteOK V B L I σ ha bset u z)
  refine e.trans ?_
  congr 1
  · refine (Finset.prod_eq_single (scalarSite V B I σ ha) ?_ ?_).trans ?_
    · intro b _ hb
      exact if_neg hb
    · intro hs
      exact absurd (Finset.mem_univ _) hs
    · exact if_pos rfl

open scoped Classical in
/-- **Reduction of P4 to a bijection.** -/
theorem contractEqCount_of_equiv (R : Type*) [CommRing R]
    (hE : (∀ (m : ℕ) [NeZero m] (π : Equiv.Perm (Routing.Addr m)), Routing.route (bset m π) = π) →
      Nonempty ({z // RnOK V B L I σ ha bset z} × ({j : Fin g // UnownedCell V B L I σ j} → Bool) ≃
        {w : Fin g → Bool // RnGood V B L I σ w})) :
    ContractEqCount V B L I σ ha bset R := by
  intro hb
  obtain ⟨E⟩ := hE hb
  have hc := Fintype.card_congr E
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool] at hc
  have hu : Fintype.card {j : Fin g // UnownedCell V B L I σ j} = uOwned V B L I σ := by
    unfold uOwned
    congr
  rw [hu, Fintype.card_subtype, Fintype.card_subtype] at hc
  rw [contract_rnFactors, mul_comm]
  have hc' := congrArg (fun n : ℕ => (n : R)) hc
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc'
  convert hc' using 3

end Factors

end P1Net
