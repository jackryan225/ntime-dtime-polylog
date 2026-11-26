import P1P5.Factor0Target
import P1ChkDir.C4
import P1Wit.WitTuple

namespace P1SolF0R.SolReader

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3)

/-- A nonzero previous-owner record is exactly the port-in link test. -/
theorem portIn_link (ι : Fin I) (k : K) (δ : Fin 3) :
    netMate I σ ((ι, .portIn k δ), 1) ≠ none ↔
      P1ChkDir.ownToN (prevOwner I σ k ι (portQ I σ k ι δ)) ≠ 0 := by
  have hn : (1 : Fin 4) ≠ 0 := by decide
  cases hp : prevOwner I σ k ι (portQ I σ k ι δ) <;>
    simp [netMate, locMate, interMate, hn, hp, P1ChkDir.ownToN, P1Wit.optCode]

/-- A nonzero next-owner record is exactly the port-out link test. -/
theorem portOut_link (ι : Fin I) (k : K) (δ : Fin 3) :
    netMate I σ ((ι, .portOut k δ), 1) ≠ none ↔
      P1ChkDir.ownToN (nextOwner I σ k ι (portQ I σ k ι δ)) ≠ 0 := by
  have hn : (1 : Fin 4) ≠ 0 := by decide
  cases hp : nextOwner I σ k ι (portQ I σ k ι δ) <;>
    simp [netMate, locMate, interMate, hn, hp, P1ChkDir.ownToN, P1Wit.optCode]

theorem path_link (ι : Fin I) (c : Ext K) :
    netMate I σ ((ι, .tabP c), 1) ≠ none ↔ (extIdx K c).val + 1 < Fintype.card (Ext K) := by
  have hn : (1 : Fin 4) ≠ 0 := by decide
  by_cases hc : (extIdx K c).val + 1 < Fintype.card (Ext K) <;>
    simp [netMate, locMate, interMate, hn, nextExt, hc]

theorem end_link (ι : Fin I) :
    netMate I σ ((ι, .eOut), 1) ≠ none ↔ ι.val + 1 < I := by
  have hn : (1 : Fin 4) ≠ 0 := by decide
  simp only [netMate, locMate, hn, if_false, interMate, if_true, colSucc]
  split <;> simp_all

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.portIn_link
