import P1Net.ContractProofEncoder
import P1Net.ContractProofUniqueness

/-! The original routed-network contraction, with its owned-block scalar. -/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open AstraContract

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

theorem AstraContract.encodeRun_recover (route : Routes bset)
    (z : RoutedGood V B L I σ ha bset) (b : UnownedBits V B L I σ) :
    encodeRun V B I σ ha bset L route
      ⟨completedGuess V B L I σ ha bset z b, completed_good V B L I σ ha bset z route b⟩ = z := by
  let w : GoodGuess V B L I σ :=
    ⟨completedGuess V B L I σ ha bset z b, completed_good V B L I σ ha bset z route b⟩
  let q := encodeRun V B I σ ha bset L route w
  have hp := encodeRun_pins V B I σ ha bset L route w
  have hw := completedGuess_eq_of_seedWords V B L I σ ha bset q w.val hp
  exact same_labels_of_completion V B L I σ ha bset q z route (fun j => w.val j) b hw

variable (R : Type*) [CommRing R]

theorem contractEqCount_holds : ContractEqCount V B L I σ ha bset R := by
  intro route
  apply count_of_completion V B L I σ ha bset R
  exact equivOfEncoder V B L I σ ha bset route (encodeRun V B I σ ha bset L route)
    (encodeRun_pins V B I σ ha bset L route) (encodeRun_recover V B L I σ ha bset route)

end P1Net
