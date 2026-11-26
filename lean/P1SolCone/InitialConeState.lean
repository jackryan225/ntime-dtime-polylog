import P1SolCone.ConeStart
import P1SolCone.GuardedLevel

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def initialConeCode {F : Type} (p : TerminalHeader × (Bool × HalfCode)) : ConeStateCode F :=
  bif coneTerminalGate p.1 && p.2.1 then (true, [(terminalPos p.1,p.2.2)], []) else (false,[],[])

theorem initialConeCode_poly {F : Type} [Fintype F] : Poly (initialConeCode (F := F)) := by
  unfold initialConeCode
  have gate := (Easy.fst.poly.compose coneTerminalGate_poly).pair
    (show Poly (fun p : TerminalHeader × (Bool × HalfCode) => p.2.1) from by fun_prop)
  have cond := gate.compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly
  have yes : Poly (fun p : TerminalHeader × (Bool × HalfCode) => (true, [(terminalPos p.1,p.2.2)], ([] : List (LevelCode F)))) := by
    exact (Code.Poly.const true).pair (((show Poly (fun p : TerminalHeader × (Bool × HalfCode) =>
      (terminalPos p.1,p.2.2)) from by fun_prop).pair (Code.Poly.const ([] : List KeyCode))).compose Poly.cons |>.pair
        (Code.Poly.const []))
  exact Poly.choose cond yes (Code.Poly.const (false,[],[]))

def initialConeState {F : Type} (D : Dims) (u : List Bool) (w v : ℕ) : CheckedTableState F :=
  let pos := (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)
  if D.fixedLen ≤ u.length ∧ v < finP D then
    if widthsWithin w (readHalfWidths D u D.top pos) then
      (readFinalHalf D u v).map (fun half => ([(pos,half)],[]))
    else none
  else none

theorem initialConeCode_eq {F : Type} (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally)
    (hc : (D.lv D.top).slots ≤ clock.length) (hc' : finArcs D ≤ clock.length) :
    let h := actualTerminalHeader D u.length w v clock
    initialConeCode (F := F) (h, replayTerminalPayload h u) = encodeConeState (initialConeState D u w v) := by
  let h := actualTerminalHeader D u.length w v clock
  let out := replayTerminalPayload h u
  let pos := (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)
  change initialConeCode (F := F) (h,out) = _
  have hp : terminalPos h = pos := by
    unfold terminalPos
    rw [terminalLanes_actual]
    rfl
  unfold initialConeCode initialConeState
  dsimp only
  rw [coneTerminalGate_eq, hp]
  by_cases hguard : D.fixedLen ≤ u.length ∧ v < finP D
  · have he := terminalPayload_replay D u w v clock hc hc' hguard.1
    change (bif out.1 then some out.2 else none) =
      (bif widthsWithin w (readHalfWidths D u D.top pos) then readFinalHalf D u v else none) at he
    rw [if_pos hguard]
    simp only [hguard, decide_true, Bool.true_and]
    by_cases hcap : widthsWithin w (readHalfWidths D u D.top pos) = true
    · rw [hcap] at he ⊢
      change (bif out.1 then some out.2 else none) = readFinalHalf D u v at he
      rw [← he]
      cases out.1 <;> rfl
    · have hf := Bool.eq_false_iff.mpr hcap
      rw [hf] at he ⊢
      cases e : out.1
      · rfl
      · rw [e] at he
        contradiction
  · simp only [hguard, decide_false, Bool.false_and, Bool.cond_false, ite_false, encodeConeState]

end P1SolCone.SolCone
