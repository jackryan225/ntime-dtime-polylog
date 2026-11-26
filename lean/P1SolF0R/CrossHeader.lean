import P1P5.Factor0Target
import P1SolFactor.CrossPoly
import P1SolFactor.PolyWords
import P1SolC10SA.Primitives

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1SolFactor P1SolFactor.Owner
open scoped P1ChkFinal.AstraC10

abbrev CrossIn := (Tally × (List Tally × List Tally)) × (Tally × Tally)

/-- Package the two switch choices as the route header. The final column has one output arc. -/
def routeCode (p : Bool × (Bool × Bool)) : List Tally :=
  [tally 5, tally (if p.1 then 1 else 0), tally (if p.2.1 then 0 else if p.2.2 then 2 else 1)]

theorem routeCode_poly : Poly routeCode := (Easy.finite _).poly

/-- Either member of a switch pair may be supplied as the address. -/
def routeHeader (cross : CrossIn → Bool)
    (p : (Tally × (List Tally × List Tally)) × (Tally × Tally)) : List Tally :=
  let column := p.2.1
  let n := p.1.1
  let incoming := bif column.isEmpty then false else
    cross (p.1, (P1SolFactor.SolPolyWords.decT column, p.2.2))
  let last := decide (column.length + 1 = 2 * (n.length + 1))
  let outgoing := cross (p.1, (column, p.2.2))
  routeCode (incoming, last, outgoing)

theorem routeHeader_poly {cross : CrossIn → Bool} (hc : Poly cross) :
    Poly (routeHeader cross) := by
  have col : Poly (fun p : CrossIn => p.2.1.length + 1) := by fun_prop
  have n : Poly (fun p : CrossIn => 2 * (p.1.1.length + 1)) := by fun_prop
  have hl := P1SolC10SA.SolShrink.eqOn_poly col n
  have he : Poly (fun p : CrossIn => p.2.1.isEmpty) :=
    (show Poly (fun p : CrossIn => p.2.1) from by fun_prop).compose (Carry.vacant Unit).poly
  have hin : Poly (fun p : CrossIn => cross (p.1, (P1SolFactor.SolPolyWords.decT p.2.1, p.2.2))) :=
    (show Poly (fun p : CrossIn => (p.1, (P1SolFactor.SolPolyWords.decT p.2.1, p.2.2))) from by fun_prop).compose hc
  have hout : Poly (fun p : CrossIn => cross (p.1, (p.2.1, p.2.2))) :=
    (show Poly (fun p : CrossIn => (p.1, (p.2.1, p.2.2))) from by fun_prop).compose hc
  exact ((he.choose (Code.Poly.const false) hin).pair (hl.pair hout)).compose routeCode_poly

theorem routeHeader_eq (cross : CrossIn → Bool)
    (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
      cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
        (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)
    (V : FiniteMultiTapeMachine) (n column : ℕ) (π : Equiv.Perm (P1Net.Routing.Addr (n + 1)))
    (r : P1Net.Routing.Addr (n + 1)) :
    let p := (P1Benes.label n).permCongr π
    let s := P1Benes.NetBridge.bset (n + 1) π
    let j := (P1Benes.label n r).val
    routeHeader cross ((tally n, ((P1Benes.Tab.tabOf p).map tally, (P1Benes.Tab.tabOf p.symm).map tally)),
        (tally column, tally j)) =
      ruleCode V (.route (routeInChoice s column r) (routeOutChoice s column r)) := by
  have hEmpty : (tally column).isEmpty = decide (column = 0) := by
    cases column
    · rfl
    · rw [tally_succ]
      rfl
  have hbit (i : ℕ) :
      cross ((tally n, ((P1Benes.Tab.tabOf ((P1Benes.label n).permCongr π)).map tally,
        (P1Benes.Tab.tabOf ((P1Benes.label n).permCongr π).symm).map tally)),
        (tally i, tally (P1Benes.label n r).val)) =
      P1Benes.NetBridge.bset (n + 1) π i (P1Net.Routing.rep (n + 1) i r) := by
    rw [hc, P1Benes.Tab.crossT_eq, P1Benes.NetBridge.bset_succ]
    exact (P1Benes.settings_rep n π i r).symm
  simp only [routeHeader, routeCode, tally_length, P1SolFactor.SolPolyWords.decT_tally, hbit,
    hEmpty, routeInChoice, routeOutChoice, ruleCode]
  by_cases ho : column + 1 = 2 * (n + 1)
  · simp only [ho, decide_true, ite_true, Option.elim_none]
    by_cases hi : column = 0 <;> simp only [hi, decide_true, decide_false, Bool.cond_true,
      Bool.cond_false, ite_true, ite_false]
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false, Option.elim_some]
    by_cases hi : column = 0 <;> simp only [hi, decide_true, decide_false, Bool.cond_true,
      Bool.cond_false, ite_true, ite_false]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.routeHeader_eq
