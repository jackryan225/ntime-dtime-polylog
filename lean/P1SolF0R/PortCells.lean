import P1SolF0R.RouteInput
import P1SolF0R.Pins

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1Net
open scoped P1ChkFinal.AstraC10

/-- Lane count, block size, zigzag start, port type, lane, and cell offset. -/
abbrev PortCellArgs := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The signed input cell as a difference of natural numbers. -/
def portCell (p : PortCellArgs) : ℕ × ℕ :=
  let lanes := p.1
  let B := p.2.1
  let q := (startParts (lanes, p.2.2.1)).1
  let δ := p.2.2.2.1
  let lane := p.2.2.2.2.1
  let j := p.2.2.2.2.2
  (((q.1 + δ) * lanes + lane) * B + j, (q.2 + 1) * lanes * B)

attribute [local fun_prop] startParts_poly

theorem portCell_poly : Poly portCell := by
  unfold portCell
  fun_prop

theorem portCell_eq (N B raw δ lane j : ℕ) (hN : 0 < N) :
    let p := portCell (N, B, raw, δ, lane, j)
    (p.1 : ℤ) - (p.2 : ℤ) =
      ((unzigzag raw / (N : ℤ) - 1 + δ) * (N : ℤ) + lane) * B + j := by
  have hq := (startParts_eq N raw hN).1
  rw [hq]
  simp only [portCell]
  push_cast
  ring

theorem portCell_genuine {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)
    (B raw δ lane j : ℕ) (hraw : raw = zigzag (betaOf σ k (ι.val * 2 ^ h))) :
    let p := portCell (2 ^ h, B, raw, δ, lane, j)
    (p.1 : ℤ) - (p.2 : ℤ) = portBlock I σ ι k δ lane * B + j := by
  dsimp only
  rw [portCell_eq _ _ _ _ _ _ (Nat.two_pow_pos h), hraw, unzigzag_zigzag]
  unfold portBlock bigQ
  push_cast
  rfl

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.portCell_genuine
