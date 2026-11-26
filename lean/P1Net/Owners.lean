import P1Net.Count
import P1Net.Factors

/-!
# Owners: one notion of ownership for the routed network and for the directory check C14

Lane P1-lean-net (2026-11-25, restart). Before the restart `P1Net.Owns` had two definitions (`StateGraph.lean`
and `Count.lean`), so no file could import both. Ruling: `P1Net.Owns` is the interval form of `StateGraph.lean`
(used by the routed network: owner links, `nextOwner`, `uOwned`); the directory form of `Count.lean` is now
`P1Net.OwnsDir`. This file proves that the two forms agree when big intervals have `N = 2 ^ h` small intervals,
and that the routed scalar exponent `uOwned` equals `unownedCount` (so check C14 can use either).

* `owns_iff_ownsDir`: `Owns I σ k ι Q ↔ OwnsDir σ (2 ^ h) ι k Q`.
* `unownedCell_iff`: `UnownedCell V B L I σ j ↔ ¬ OwnedGuess L σ (2 ^ h) I j`.
* `uOwned_eq_unownedCount`: `uOwned V B L I σ = unownedCount L σ (2 ^ h) I`.
* `uOwned_eq_zero_iff`: the directory form of C14 for the routed scalar.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-- The interval form and the directory form of ownership agree (`N = 2 ^ h`). -/
theorem owns_iff_ownsDir (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (k : K) (ι : ℕ) (Q : ℤ) :
    Owns I σ k ι Q ↔ OwnsDir σ (2 ^ h) ι k Q := by
  unfold Owns OwnsDir bigQ
  generalize betaOf σ k (ι * 2 ^ h) / ((2 ^ h : ℕ) : ℤ) = q
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨finOfInt 3 (Q - q + 1), ?_⟩
    have := finOfInt_val 3 (z := Q - q + 1) (by omega) (by omega)
    omega
  · rintro ⟨δ, rfl⟩
    have := δ.isLt
    constructor <;> omega

section Factors

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3)

omit [NeZero B] [NeZero I] in
theorem unownedCell_iff (j : Fin g) :
    UnownedCell V B L I σ j ↔ ¬ OwnedGuess (B := B) L σ (2 ^ h) I j := by
  unfold UnownedCell OwnedGuess
  apply not_congr
  constructor
  · rintro ⟨ι, hι⟩
    exact ⟨ι, ι.isLt, (owns_iff_ownsDir I σ _ ι _).1 hι⟩
  · rintro ⟨ι, hιI, hι⟩
    exact ⟨⟨ι, hιI⟩, (owns_iff_ownsDir I σ _ ι _).2 hι⟩

/-- The routed scalar exponent is copy B's `unownedCount` with `N = 2 ^ h`. -/
theorem uOwned_eq_unownedCount :
    uOwned V B L I σ = unownedCount (B := B) L σ (2 ^ h) I := by
  classical
  unfold uOwned unownedCount
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun j => unownedCell_iff V B L I σ j)

/-- **C14, routed form.** `uOwned = 0` iff every guess cell lies in a big block `q - 1, q, q + 1` around the
directory entry `q = betaOf σ k (ι 2^h) / 2^h` of some big interval `ι < I`. -/
theorem uOwned_eq_zero_iff :
    uOwned V B L I σ = 0 ↔
      ∀ j : Fin g, ∃ ι < I, ∃ δ : Fin 3,
        (L.cellOf j).2 / B / ((2 ^ h : ℕ) : ℤ) =
          betaOf σ (L.cellOf j).1 (ι * 2 ^ h) / ((2 ^ h : ℕ) : ℤ) + δ - 1 := by
  rw [uOwned_eq_unownedCount]
  exact unownedCount_eq_zero_iff L σ (2 ^ h) I

end Factors

end P1Net
