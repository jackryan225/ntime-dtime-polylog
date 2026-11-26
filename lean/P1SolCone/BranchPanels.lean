import P1SolCone.PanelReads

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill P1ChkFinal P1P7

/-- The phase geometry and incidence and width reads at one actual state. -/
structure StatePanelOK (D : Dims) (u : List Bool) (ℓ : ℕ) {a g : ℕ} (X : State a g) : Prop where
  bases : (D.lv ℓ).bases = Fintype.card X.Base
  slots : (D.lv ℓ).slots = 2 ^ a
  lanes : (D.lv ℓ).lanes = 2 ^ g
  panel : ∀ y, PanelMatch D u ℓ (addr X y) (P1P7.panel X y)

/-- All panel rows encountered along the branch, including the terminal row. -/
def BranchPanelsOK {R : Type*} [CommSemiring R] {b n : ℕ} (D : Dims) (u : List Bool) :
    {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) → E.Choices → ℕ → Prop
  | _, _, X, .done _, _, ℓ => StatePanelOK D u ℓ X ∧ ℓ = D.top
  | _, _, X, .more _ tail, c, ℓ => StatePanelOK D u ℓ X ∧ ℓ < D.top ∧
      BranchPanelsOK D u (tail c.1) c.2 (ℓ + 1)

theorem BranchPanelsOK.head {R : Type*} [CommSemiring R] {b n a g : ℕ} {D : Dims} {u : List Bool}
    {X : State a g} {E : StateExecution R b n X} {c : E.Choices} {ℓ : ℕ}
    (h : BranchPanelsOK D u E c ℓ) : StatePanelOK D u ℓ X := by
  cases E with
  | done => exact h.1
  | more => exact h.1

theorem branchPanels_of_atLevel {R : Type*} [CommSemiring R] {b n a g : ℕ} (D : Dims) (u : List Bool)
    {X : State a g} (E : StateExecution R b n X) :
    ∀ ℓ (P : ExecutionPanels D E ℓ) (c : E.Choices),
      (∀ (j : Fin (D.top + 1)) (hj : ℓ ≤ j.val), StatePanelOK D u j.val (P.atLevel E c j hj).state) →
      BranchPanelsOK D u E c ℓ := by
  induction E with
  | done X =>
    intro ℓ P c h
    have ht : ℓ = D.top := P.property
    have hlt : ℓ < D.top + 1 := by rw [ht]; exact Nat.lt_succ_self _
    exact ⟨h ⟨ℓ, hlt⟩ le_rfl, ht⟩
  | @more a₀ g₀ a' g' X₀ p tail ih =>
    intro ℓ P c h
    have hlt : ℓ < D.top := P.1.property
    refine ⟨?_, hlt, ih c.1 (ℓ + 1) (P.2 c.1) c.2 (fun j hj => ?_)⟩
    · let j : Fin (D.top + 1) := ⟨ℓ, Nat.lt_succ_of_lt hlt⟩
      have read : P.atLevel (.more p tail) c j le_rfl = ⟨a₀, g₀, X₀, P.1.val c.1⟩ := by
        simp only [ExecutionPanels.atLevel, dite_eq_right (show ¬ ℓ < j.val from lt_irrefl ℓ)]
        rfl
      exact (congrArg (fun q : IndexedPanel D j.val => StatePanelOK D u j.val q.state) read).mp (h j le_rfl)
    · have read : P.atLevel (.more p tail) c j (Nat.le_of_lt hj) = (P.2 c.1).atLevel (tail c.1) c.2 j hj := by
        simp only [ExecutionPanels.atLevel, dite_eq_left (show ℓ < j.val from hj)]
      exact (congrArg (fun q : IndexedPanel D j.val => StatePanelOK D u j.val q.state) read).mp (h j (Nat.le_of_lt hj))

/-- A tuple's true arc and width fields supply all panel reads along the selected branch. -/
theorem branchPanels_encTuple {F : Type*} [CommSemiring F] {D : Dims} {C : P1Count.CountData F}
    {d a g b n : ℕ} (R : TupleRecords D C d) (q : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R q).length ≤ m)
    {X : State a g} (E : StateExecution F b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0)
    (c : E.Choices) (hLevel : ∀ j, R.level q.1 q.2.1 j = levelOfExecution E P T c j) :
    BranchPanelsOK D (List.ofFn (encTuple R m q)) E c 0 := by
  apply branchPanels_of_atLevel D _ E 0 P c
  intro j hj
  let cur := P.atLevel E c j hj
  have h := cur.data.fits
  refine ⟨h.bases, h.slots, h.lanes, fun y => ?_⟩
  have eq : R.level q.1 q.2.1 j =
      levelRecordsOfState cur.state cur.data.fits (cur.data.step (T.table E c j)) := hLevel j
  exact panelMatch_encTuple R q m hm j cur.state cur.data.fits _ eq y

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.branchPanels_encTuple
