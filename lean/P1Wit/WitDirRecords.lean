import P1Wit.WitTuple
import P1Wit.WitSiteOrder
import P1Net.Skeleton

namespace P1Wit.SolWitfill

variable {D : Dims}

/-- Skeleton trits in tape-number order. -/
def skeletonOfTapes {K : Type} (ρ : K ≃ Fin D.r) :
    (Fin (D.I * D.N) → K → Fin 3) ↪ Skeleton D where
  toFun σ i k := σ i (ρ.symm k)
  inj' := by
    intro σ τ h
    funext i k
    have e := congrFun (congrFun h i) (ρ k)
    simpa only [Function.Embedding.coeFn_mk, Equiv.symm_apply_apply] using e

/-- The big blocks of tape `k` owned by interval `i`. -/
def directoryOwns (σ : Skeleton D) (k : Fin D.r) (i : Fin D.I) (Q : ℤ) : Prop :=
  let q := P1Net.betaOf σ k (i.val * D.N) / (D.N : ℤ)
  q - 1 ≤ Q ∧ Q ≤ q + 1

instance (σ : Skeleton D) (k : Fin D.r) (i : Fin D.I) (Q : ℤ) :
    Decidable (directoryOwns σ k i Q) := by unfold directoryOwns; infer_instance

/-- Build the true directory from its trits and the numbered guess blocks. -/
def directoryOfSkeleton (σ : Skeleton D) (guessTape : Fin D.r) (block : Fin D.nGB → ℤ)
    (start_fits : ∀ (i : Fin D.I) (k : Fin D.r), zigzag (P1Net.betaOf σ k (i.val * D.N)) < 2 ^ D.bigW) :
    Directory D :=
  let coord := (P1Wit.ord D.I D.r).symm
  let dirCoord := (P1Wit.ord (D.I * D.r) 3).symm
  let port := fun (i : Fin D.I) (k : Fin D.r) (δ : Fin 3) =>
    P1Net.betaOf σ k (i.val * D.N) / (D.N : ℤ) - 1 + (δ.val : ℤ)
  { start := fun j => P1Net.betaOf σ (coord j).2 ((coord j).1.val * D.N)
    start_fits := fun j => start_fits (coord j).1 (coord j).2
    prevOwn := fun j =>
      let p := coord (dirCoord j).1
      let Q := port p.1 p.2 (dirCoord j).2
      let owners := Finset.univ.filter (fun i : Fin D.I => i < p.1 ∧ directoryOwns σ p.2 i Q)
      if h : owners.Nonempty then some (owners.max' h) else none
    nextOwn := fun j =>
      let p := coord (dirCoord j).1
      let Q := port p.1 p.2 (dirCoord j).2
      let owners := Finset.univ.filter (fun i : Fin D.I => p.1 < i ∧ directoryOwns σ p.2 i Q)
      if h : owners.Nonempty then some (owners.min' h) else none
    guess := fun j =>
      let owners := Finset.univ.filter (fun i : Fin D.I => directoryOwns σ guessTape i (block j))
      if h : owners.Nonempty then some (owners.min' h) else none }

end P1Wit.SolWitfill
