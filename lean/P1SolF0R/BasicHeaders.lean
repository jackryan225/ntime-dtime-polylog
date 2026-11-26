import P1SolF0R.Chunk
import P1SolF0R.Output
import P1SolFactor.FactorTableData

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Net P1SolFactor P1SolFactor.Owner P1ChkFinal.AstraC10
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

def bitTally (b : Bool) : Tally := tally (if b then 1 else 0)

theorem bitTally_poly : Poly bitTally := (Easy.finite _).poly

/-- The header of a table site, including the trits in the factor tester's tape order. -/
def tableHeader (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (p : Tally × Bool × List Bool × ℕ) : Header :=
  tally 1 :: p.1 :: bitTally p.2.1 :: List.ofFn fun j : Fin (Fintype.card V.K) =>
    tally (min (tritInChunk (Fintype.card V.K) (p.2.2.1, p.2.2.2, tape ((kIdx V.K).symm j))) 3)

theorem tableHeader_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) :
    Poly (tableHeader V tape) := by
  have htrits : Poly (fun p : Tally × Bool × List Bool × ℕ =>
      List.ofFn fun j : Fin (Fintype.card V.K) =>
        tally (min (tritInChunk (Fintype.card V.K) (p.2.2.1, p.2.2.2, tape ((kIdx V.K).symm j))) 3)) := by
    apply poly_fixedTab
    intro j
    have h := (show Poly (fun p : Tally × Bool × List Bool × ℕ => (p.2.2.1, p.2.2.2, tape ((kIdx V.K).symm j)))
      from by fun_prop).compose (tritInChunk_poly (Fintype.card V.K))
    exact P1ProgEng.SolKWR.poly_tallyMin h (Code.Poly.const 3) (Dom.const _ 3)
  have hl := (show Poly (fun p : Tally × Bool × List Bool × ℕ => p.2.1) from by fun_prop).compose bitTally_poly
  have h1 := (hl.pair htrits).compose Poly.cons
  have h2 := (Easy.fst.poly.pair h1).compose Poly.cons
  exact ((Code.Poly.const (tally 1)).pair h2).compose Poly.cons

theorem tableHeader_eq (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (B : ℕ) (last : Bool) (block : List Bool) (lane : ℕ) (s : V.K → Fin 3)
    (hs : ∀ k, tritInChunk (Fintype.card V.K) (block, lane, tape k) = (s k).val) :
    tableHeader V tape (tally B, last, block, lane) =
      ruleCode V (.table B last (List.ofFn fun j => s ((kIdx V.K).symm j))) := by
  simp only [tableHeader, ruleCode, bitTally, hs, List.map_ofFn, List.cons_append, List.nil_append,
    Function.comp_def]
  congr 3
  apply congrArg List.ofFn
  funext j
  have h := (s ((kIdx V.K).symm j)).isLt
  rw [min_eq_left h.le]

/-- The two possible path headers can be tabulated once for the fixed machine. -/
def pathHeader (V : FiniteMultiTapeMachine) (p : ℕ × Bool) : Header :=
  let headers := List.ofFn fun i : Fin (Fintype.card (Ext V.K)) =>
    let c := (extIdx V.K).symm i
    (ruleCode V (.path false c), ruleCode V (.path true c))
  let h := readAt ([], []) headers p.1
  bif p.2 then h.2 else h.1

theorem pathHeader_poly (V : FiniteMultiTapeMachine) : Poly (pathHeader V) := by
  unfold pathHeader
  fun_prop

theorem pathHeader_eq (V : FiniteMultiTapeMachine) (c : Ext V.K) (linked : Bool) :
    pathHeader V ((extIdx V.K c).val, linked) = ruleCode V (.path linked c) := by
  simp only [pathHeader, readAt_ofFn, Equiv.symm_apply_apply]
  cases linked <;> rfl

/-- The fixed initial state header, with the offset of each tape set to zero. -/
def initHeader (V : FiniteMultiTapeMachine) (B : Tally) : Header :=
  tally 6 :: (P1SolFactor.SolFactor.stateWord V
    (B, (⟨V.initialState⟩, List.replicate (Fintype.card V.K) (tally 0)))).map bitTally

theorem initHeader_poly (V : FiniteMultiTapeMachine) : Poly (initHeader V) := by
  have hs := ((Poly.identity : Poly (id : Tally → Tally)).pair
    (Code.Poly.const (⟨V.initialState⟩, List.replicate (Fintype.card V.K) (tally 0)))).compose
      (P1SolFactor.SolFactor.stateWord_poly V)
  exact ((Code.Poly.const (tally 6)).pair (hs.compose (Poly.maps _ bitTally_poly))).compose Poly.cons

theorem initHeader_eq (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] :
    initHeader V (tally B) =
      ruleCode V (.fixed (List.ofFn (encS V B V.initialState (fun _ => finOfInt B 0)))) := by
  have hzero : (finOfInt B 0).val = 0 := by simp only [finOfInt, Int.toNat_zero, Nat.zero_mod]
  have h := P1SolFactor.SolFactor.stateWord_encS V B V.initialState (fun _ => finOfInt B 0)
  simp only [hzero, List.ofFn_const] at h
  simp only [initHeader, h, ruleCode]
  rfl

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.tableHeader_eq
#print axioms P1SolF0R.SolReader.initHeader_eq
