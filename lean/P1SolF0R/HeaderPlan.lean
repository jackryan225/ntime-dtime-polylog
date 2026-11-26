import P1SolF0R.BasicHeaders
import P1SolF0R.Location
import P1SolF0R.PinColumn
import P1SolF0R.Public
import P1SolF0R.RouteRead

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1Wit P1ChkFinal.AstraC10 P1SolFactor P1SolFactor.Owner
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

abbrev HeaderPlan := Header × List PinQuery
abbrev LocalInput := (PublicClocks × SiteCode) × (ℕ × IntervalChunk)

private def directoryTape (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (j : ℕ) : ℕ × Bool :=
  readAt (0, false) (List.ofFn fun i : Fin (Fintype.card V.K) =>
    let k := (kIdx V.K).symm i
    (tape k, decide (k = V.inputTape))) j

@[fun_prop] private theorem directoryTape_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) :
    Poly (directoryTape V tape) := by unfold directoryTape; fun_prop

theorem directoryTape_eq (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (k : V.K) :
    directoryTape V tape (kIdx V.K k).val = (tape k, decide (k = V.inputTape)) := by
  simp only [directoryTape, readAt_ofFn, Equiv.symm_apply_apply]

def laneOfRequest (p : LocalInput) : ℕ :=
  reverseNum (p.1.1.2.2.2, p.2.1)

def tablePlan (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (p : LocalInput) : Header :=
  let N := p.1.1.1.2.1
  let I := p.1.1.1.1
  let i := p.1.2.1.2
  let lane := laneOfRequest p
  tableHeader V tape (p.1.1.2.2.1, decide (i * N + lane + 1 = I * N), p.2.2.1, lane)

def portPlan (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (p : LocalInput) : List PinQuery :=
  let v := directoryTape V tape p.1.2.1.1.2.1
  let w := p.1.1.1.2.2.2.2.1
  let raw := startInChunk (p.2.2.2.1, w, v.1)
  pinColumn V ((p.1.1.2.2.1, v.2),
    (p.1.1.1.2.2.2.2.2, p.1.1.1.2.1, raw, p.1.2.1.1.2.2.1, laneOfRequest p))

def linkOwner (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (prev : Bool) (p : LocalInput) : ℕ :=
  let v := directoryTape V tape p.1.2.1.1.2.1
  let w := p.1.1.1.2.2.2.2.1
  let bits := bif prev then p.2.2.2.2.1 else p.2.2.2.2.2
  ownerInChunk (bits, w, v.1, p.1.2.1.1.2.2.1)

def contentHeader (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (cross : CrossIn → Bool) (p : LocalInput) : Header :=
  let v := directoryTape V tape p.1.2.1.1.2.1
  let w := p.1.1.1.2.2.2.2.1
  let nc := p.1.1.2.1
  let hc := p.1.1.2.2.2
  let centers := chunkCenters (Fintype.card V.K) (nc, p.2.2, w, v.1)
  routeHeader cross (routeArgs 3 ((hc, nc),
    (contentTables (hc, centers), p.1.2.1.1.2.2.1, p.1.2.1.1.2.2.2, p.2.1)))

def stateHeader (cross : CrossIn → Bool) (p : LocalInput) : Header :=
  let nc := p.1.1.2.1
  let hc := p.1.1.2.2.2
  routeHeader cross (routeArgs 1 ((hc, nc),
    (stateTables (hc, nc), p.1.2.1.1.2.2.1, p.1.2.1.1.2.2.2, p.2.1)))

attribute [local fun_prop] reverseNum_poly tableHeader_poly startInChunk_poly pinColumn_poly
  ownerInChunk_poly chunkCenters_poly contentTables_poly stateTables_poly routeArgs_poly

@[fun_prop] theorem laneOfRequest_poly : Poly laneOfRequest := by unfold laneOfRequest; fun_prop

@[fun_prop] theorem tablePlan_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) :
    Poly (tablePlan V tape) := by unfold tablePlan; fun_prop

@[fun_prop] theorem portPlan_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) :
    Poly (portPlan V tape) := by unfold portPlan; fun_prop

@[fun_prop] theorem linkOwner_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (prev : Bool) :
    Poly (linkOwner V tape prev) := by unfold linkOwner; fun_prop

theorem contentHeader_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) {cross : CrossIn → Bool}
    (hc : Poly cross) : Poly (contentHeader V tape cross) := by
  unfold contentHeader
  apply Poly.compose _ (routeHeader_poly hc)
  fun_prop

theorem stateHeader_poly {cross : CrossIn → Bool} (hc : Poly cross) : Poly (stateHeader cross) := by
  unfold stateHeader
  apply Poly.compose _ (routeHeader_poly hc)
  fun_prop

private def noPins (h : Header) : HeaderPlan := (h, [])

@[fun_prop] private theorem noPins_poly : Poly noPins := by unfold noPins; fun_prop

/-- Compute the header and any remaining raw-input pin queries for one site. -/
def headerPlan (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (p : LocalInput) : HeaderPlan :=
  let loc := p.1.2.1.1
  let i := p.1.2.1.2
  let free := noPins [tally 0]
  let forward := noPins [tally 4, tally 0, tally 1]
  let backward := noPins [tally 4, tally 1, tally 0]
  bif p.1.2.2 then free
  else bif decide (loc.1 = 0) then noPins (tablePlan V tape p)
  else bif decide (loc.1 = 1) then
    noPins (pathHeader V (loc.2.1, decide (loc.2.1 + 1 < Fintype.card (Ext V.K))))
  else bif decide (loc.1 = 2) then
    bif decide (linkOwner V tape true p = 0) then ([tally 3], portPlan V tape p) else forward
  else bif decide (loc.1 = 3) then
    bif decide (linkOwner V tape false p = 0) then free else backward
  else bif decide (loc.1 = 4) then noPins (contentHeader V tape cross p)
  else bif decide (loc.1 = 5) then noPins (stateHeader cross p)
  else bif decide (loc.1 = 6) then
    bif decide (i = 0) then
      bif decide (laneOfRequest p = 0) then noPins (initHeader V p.1.1.2.2.1) else noPins [tally 6]
    else forward
  else bif decide (i + 1 < p.1.1.1.1) then backward else free

attribute [local fun_prop] pathHeader_poly initHeader_poly

set_option maxHeartbeats 1500000 in
theorem headerPlan_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) {cross : CrossIn → Bool}
    (hc : Poly cross) : Poly (headerPlan V tape cross) := by
  have content : Poly (contentHeader V tape cross) := contentHeader_poly V tape hc
  have state : Poly (stateHeader cross) := stateHeader_poly hc
  unfold headerPlan
  fun_prop

end

theorem noPins_eq (h : Header) : noPins h = (h, []) := rfl

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.headerPlan_poly
