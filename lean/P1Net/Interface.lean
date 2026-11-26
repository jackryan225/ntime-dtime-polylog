import P1Net.Owners
import P1Net.Size
import P1Benes.NetBridge
import P1Int.Expander

/-!
# Lane net: the interface for P5, P8, P9 and P11

Lane P1-lean-net (2026-11-25, restart).
* `rnStateOf S`: the routed lane network at the base degree `2 ^ S.degreeExponent 0` of an OpenAI block schedule `S`
  (the degree input `4 ≤ 2 ^ S.degreeExponent 0` is `P1Int.four_le_baseDegree`, lane integration).
* `contract_rn_eq_count`: P4 with the canonical Beneš settings of lane P2 (`P1Benes.NetBridge.bset`); the routing
  hypothesis of `ContractEqCount` is discharged by `P1Benes.NetBridge.route_bset`.
* `sum_rn_contract`: every run has exactly one skeleton, so the sum over all skeleton candidates is the number of
  accepting guesses.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel

variable {h : ℕ}

section Factors

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {a : ℕ} (ha : 4 ≤ 2 ^ a)

/-- The routed lane network at the base degree of a block schedule `S` (PLAN P3: `State (S.degreeExponent 0) h`). -/
noncomputable abbrev rnStateOf {k : Type*} [Field k] (S : BlockSchedule k) (σ : Fin (I * 2 ^ h) → V.K → Fin 3) :
    State (S.degreeExponent 0) h :=
  rnState V B I σ (P1Int.four_le_baseDegree S)

open scoped Classical in
/-- **P4 with the canonical Beneš settings** (lane P2): the routing hypothesis of `ContractEqCount` holds. -/
theorem contract_rn_eq_count (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (R : Type*) [CommRing R]
    (hP4 : ContractEqCount V B L I σ ha P1Benes.NetBridge.bset R) :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha P1Benes.NetBridge.bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
          MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧
            skeleton V (L.input w) B (I * 2 ^ h) = σ).card : R) :=
  hP4 fun m _ π => P1Benes.NetBridge.route_bset m π

open scoped Classical in
/-- **Every run has exactly one skeleton**: the sum of the routed contractions over all skeleton candidates is the
number of accepting guesses. -/
theorem sum_rn_contract (R : Type*) [CommRing R]
    (hP4 : ∀ σ : Fin (I * 2 ^ h) → V.K → Fin 3, ContractEqCount V B L I σ ha P1Benes.NetBridge.bset R) :
    ∑ σ : Fin (I * 2 ^ h) → V.K → Fin 3,
        contract (rnState V B I σ ha).network (rnFactors V B L I σ ha P1Benes.NetBridge.bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
          MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B)).card : R) := by
  rw [Finset.sum_congr rfl fun σ _ => contract_rn_eq_count V B L I ha σ R (hP4 σ), ← Nat.cast_sum]
  congr 1
  exact sum_card_skeleton _ _

end Factors

end P1Net
