import P1SolF0R.PortCells
import P1SolFactor.OwnerTargets

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1Wit P1SolFactor.Owner P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

noncomputable section

/-- The block clock and input-tape flag, followed by guess length, lane count,
start code, port type, and lane number. -/
abbrev PinContext := (Tally × Bool) × (ℕ × ℕ × ℕ × ℕ × ℕ)

private def pinAtOffset (M : FiniteMultiTapeMachine) (p : PinContext × ℕ) : PinQuery :=
  let q := p.1.2
  let signed := portCell (q.2.1, p.1.1.1.length, q.2.2.1, q.2.2.2.1, q.2.2.2.2, p.2)
  pinQuery M (p.1.1.2, q.1, signed.1, signed.2)

private theorem pinAtOffset_poly (M : FiniteMultiTapeMachine) : Poly (pinAtOffset M) := by
  have hp : Poly (fun p : PinContext × ℕ =>
      portCell (p.1.2.2.1, p.1.1.1.length, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2, p.2)) :=
    (show Poly (fun p : PinContext × ℕ =>
      (p.1.2.2.1, p.1.1.1.length, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2, p.2)) from
        by fun_prop).compose portCell_poly
  have hq : Poly (fun p : PinContext × ℕ => (p.1.1.2, p.1.2.1)) := by fun_prop
  have h : Poly (fun p : (Bool × ℕ) × (ℕ × ℕ) => (p.1.1, p.1.2, p.2)) := by fun_prop
  exact ((hq.pair hp).compose h).compose (pinQuery_poly M)

def pinColumn (M : FiniteMultiTapeMachine) (p : PinContext) : List PinQuery :=
  (List.range p.1.1.length).map fun j => pinAtOffset M (p, j)

theorem pinColumn_poly (M : FiniteMultiTapeMachine) : Poly (pinColumn M) := by
  have hr : Poly (fun p : PinContext => List.range p.1.1.length) := by
    exact ((show Poly (fun p : PinContext => p.1.1) from by fun_prop).compose range_length_poly)
  exact poly_mapWith hr (pinAtOffset_poly M)

theorem pinColumn_length (M : FiniteMultiTapeMachine) (p : PinContext) :
    (pinColumn M p).length = p.1.1.length := by
  simp only [pinColumn, List.length_map, List.length_range]

theorem pinColumn_queries (M : FiniteMultiTapeMachine) (p : PinContext) (q : PinQuery)
    (h : q ∈ pinColumn M p) : ∃ args, q = pinQuery M args := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
  unfold pinAtOffset
  exact ⟨_, rfl⟩

private def allowedSymbol (M : FiniteMultiTapeMachine) (g : ℕ) (x : List Bool)
    (k : M.K) (c : ℤ) : Option M.Γ :=
  let L := withGuessLayout (M := M) x g
  if (L.guessAt k c).isSome then none else some (L.base k c)

/-- Resolving a complete pin column gives the exact pin header on a genuine input. -/
theorem pinColumn_header (M : FiniteMultiTapeMachine) (B g : ℕ)
    {I h : ℕ} (σ : Fin (I * 2 ^ h) → M.K → Fin 3) (ι : Fin I) (k : M.K)
    (δ lane raw : ℕ) (x : List Bool) (hraw : raw = zigzag (betaOf σ k (ι.val * 2 ^ h))) :
    let ps := pinColumn M ((tally B, decide (k = M.inputTape)), (g, 2 ^ h, raw, δ, lane))
    tally 3 :: ps.map (fun q => tally (resolvePin M q (P1Batch.fetch x (pinReq q)))) =
      ruleCode M (.pins (List.ofFn fun j : Fin B =>
        allowedSymbol M g x k (portBlock I σ ι k δ lane * B + j.val))) := by
  simp only [ruleCode, pinColumn, tally_length, List.map_map, List.map_ofFn, Function.comp_def]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro j hj hj'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, pinAtOffset, tally_length]
    let p := portCell (2 ^ h, B, raw, δ, lane, j)
    have hs := portCell_genuine σ ι k B raw δ lane j hraw
    dsimp only at hs
    have hf := resolvePin_eq M x g p.1 p.2 k
    dsimp only at hf
    change tally (resolvePin M (pinQuery M (decide (k = M.inputTape), g, p.1, p.2))
      (P1Batch.fetch x (pinReq (pinQuery M (decide (k = M.inputTape), g, p.1, p.2))))) = _
    rw [hf]
    rw [show (p.1 : ℤ) - (p.2 : ℤ) = portBlock I σ ι k δ lane * B + j from hs]
    dsimp only [allowedSymbol]
    by_cases hh : ((withGuessLayout (M := M) x g).guessAt k
        (portBlock I σ ι k δ lane * B + j)).isSome = true <;>
      simp only [hh, ite_true, ite_false, Bool.false_eq_true, Option.elim_none, Option.elim_some,
        symbolCode]

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.pinColumn_header
