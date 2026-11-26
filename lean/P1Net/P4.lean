import P1Net.Interface
import P1Net.ContractProofMain

/-!
# P4 for the routed network, unconditional (lane P1-lean-net, 2026-11-25)

`P1Net.contractEqCount_holds` (files `ContractProof*.lean`, written by the Astra prover P1-astra-contract, compiled and
audited by lane net) proves `ContractEqCount` for every `bset`. With the canonical Beneš settings of lane P2
(`P1Benes.NetBridge.bset`) the routing hypothesis is discharged, so:
* `rn_contract_eq_count`: the contraction of `N_{x,σ}` is the number of guesses whose run accepts within `I 2^h B` steps
  with skeleton `σ` (any commutative ring);
* `rn_sum_contract`: the sum over all skeleton candidates is the number of accepting guesses.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {a : ℕ} (ha : 4 ≤ 2 ^ a)

open scoped Classical in
/-- **P4, unconditional.** -/
theorem rn_contract_eq_count (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (R : Type*) [CommRing R] :
    contract (rnState V B I σ ha).network (rnFactors V B L I σ ha P1Benes.NetBridge.bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
          MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B) ∧
            skeleton V (L.input w) B (I * 2 ^ h) = σ).card : R) :=
  contract_rn_eq_count V B L I ha σ R (contractEqCount_holds V B L I σ ha P1Benes.NetBridge.bset R)

open scoped Classical in
/-- **Every run has exactly one skeleton**, unconditional. -/
theorem rn_sum_contract (R : Type*) [CommRing R] :
    ∑ σ : Fin (I * 2 ^ h) → V.K → Fin 3,
        contract (rnState V B I σ ha).network (rnFactors V B L I σ ha P1Benes.NetBridge.bset R) =
      ((Finset.univ.filter fun w : Fin g → Bool =>
          MultiTapeHaltsIn V (L.input w) true (I * 2 ^ h * B)).card : R) :=
  sum_rn_contract V B L I ha R fun σ => contractEqCount_holds V B L I σ ha P1Benes.NetBridge.bset R

end P1Net
