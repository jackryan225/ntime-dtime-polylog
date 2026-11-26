import P1Wit.WitBranchRecords
import P1Wit.WitStateRecords

namespace P1Wit.SolWitfill

open OAI.Computability.VPVNP.Compression

/-- Layout, greedy and energy records for a state at a numbered level. The
arc fields come from the state, and terms come from the selected next step. -/
structure PanelData (D : Dims) (ℓ : ℕ) {a g : ℕ} (X : State a g) where
  fits : PanelFits D (D.lv ℓ) X
  layout : Bool
  colour : Fin (D.lv ℓ).bases → Fin (2 ^ (D.lv ℓ).colW)
  offset : Fin (D.lv ℓ).bases → Fin (2 ^ (D.lv ℓ).tagW)
  energy : Fin ((D.lv ℓ).bases * 2) → Fin (2 ^ D.bigW)

def PanelData.step {D : Dims} {ℓ a g : ℕ} {X : State a g} (P : PanelData D ℓ X)
    (terms : Fin ((D.lv ℓ).bases * (D.lv ℓ).termKeys) → TermSlot D (D.lv ℓ)) :
    StepRecords D (D.lv ℓ) :=
  ⟨P.layout, P.colour, P.offset, P.energy, terms⟩

variable {R : Type*} [CommSemiring R] {b n : ℕ}

/-- Supply the bounded records at each actual state of the execution tree.
At a nonterminal state the energy prefixes and layout may depend on the
selected term. The terminal state is at level `D.top` on every branch. -/
def ExecutionPanels (D : Dims) {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (start : ℕ) : Type :=
  match E with
  | .done X => { _P : PanelData D start X // start = D.top}
  | .more p tail => { _P : p.step.Choice → PanelData D start X // start < D.top} ×
    ((i : _) → ExecutionPanels D (tail i) (start + 1))

structure IndexedPanel (D : Dims) (ℓ : ℕ) where
  degree : ℕ
  lanes : ℕ
  state : State degree lanes
  data : PanelData D ℓ state

def ExecutionPanels.atLevel {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (P : ExecutionPanels D E start)
    (ι : E.Choices) (ℓ : Fin (D.top + 1)) (hℓ : start ≤ ℓ.val) : IndexedPanel D ℓ.val :=
  match E with
  | .done X =>
    have h : start = ℓ.val := by have := P.property; omega
    ⟨_, _, X, h ▸ P.val⟩
  | .more _ tail =>
    if h : start < ℓ.val then
      atLevel (tail ι.1) (P.2 ι.1) ι.2 ℓ (Nat.succ_le_of_lt h)
    else
      have hs : start = ℓ.val := hℓ.antisymm (Nat.le_of_not_gt h)
      ⟨_, _, X, hs ▸ P.1.val ι.1⟩

def ExecutionPanels.final {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (P : ExecutionPanels D E start)
    (ι : E.Choices) : PanelData D D.top (E.finalState ι) :=
  match a, g, X, E with
  | _, _, _, .done _ => P.property ▸ P.val
  | _, _, _, .more _ tail => final (tail ι.1) (P.2 ι.1) ι.2

theorem ExecutionPanels.atLevel_final {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (P : ExecutionPanels D E start)
    (ι : E.Choices) (h : start ≤ D.top) :
    P.atLevel E ι (finalLevel D) h = ⟨b, n, E.finalState ι, P.final E ι⟩ := by
  induction E generalizing start with
  | done => rfl
  | more p tail ih =>
    have hlt : start < (finalLevel D).val := P.1.property
    simpa only [ExecutionPanels.atLevel, dite_eq_left hlt, ExecutionPanels.final, StateExecution.finalState]
      using ih ι.1 (P.2 ι.1) ι.2 (Nat.succ_le_of_lt hlt)

/-- Read the actual state and selected term table at level `ℓ`. -/
noncomputable def levelOfExecution {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0)
    (ι : E.Choices) (ℓ : Fin (D.top + 1)) : LevelRecords D (D.lv ℓ.val) :=
  let p := P.atLevel E ι ℓ (Nat.zero_le _)
  levelRecordsOfState p.state p.data.fits (p.data.step (T.table E ι ℓ))

theorem levelOfExecution_terms_injective {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0) :
    Function.Injective (fun ι ℓ => (levelOfExecution E P T ι ℓ).terms) :=
  ExecutionTerms.table_injective E T

theorem levelOfExecution_final {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0)
    (ι : E.Choices) : levelOfExecution E P T ι (finalLevel D) =
      levelRecordsOfState (E.finalState ι) (P.final E ι).fits
        ((P.final E ι).step (T.table E ι (finalLevel D))) := by
  let readPanel (p : IndexedPanel D D.top) : LevelRecords D (D.lv D.top) :=
    levelRecordsOfState p.state p.data.fits (p.data.step (T.table E ι (finalLevel D)))
  exact congrArg readPanel (ExecutionPanels.atLevel_final E P ι (Nat.zero_le D.top))

/-- Match the final state's actual payload with the widths stored by the
same execution record. -/
noncomputable def payloadOfExecution {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0)
    (ι : E.Choices) :
    ((e : (E.finalState ι).network.Edge) → (E.finalState ι).network.Payload e) ≃
      ((i : Fin (FinalArcs D)) → Fin ((levelOfExecution E P T ι (finalLevel D)).width i).val → Bool) := by
  rw [levelOfExecution_final]
  exact payloadOfState (E.finalState ι) (P.final E ι).fits
    ((P.final E ι).step (T.table E ι (finalLevel D)))

theorem payloadOfExecution_length {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0)
    (ι : E.Choices) (z : (e : (E.finalState ι).network.Edge) → (E.finalState ι).network.Payload e) :
    (flatten (payloadOfExecution E P T ι z)).length = (E.finalState ι).totalWidth := by
  rw [flatten_length]
  have h := payloadOfState_length (E.finalState ι) (P.final E ι).fits
    ((P.final E ι).step (T.table E ι (finalLevel D))) z
  rw [flatten_length] at h
  exact (congrArg (fun p : LevelRecords D (D.lv D.top) =>
    widthPrefix (finValue p.width) (FinalArcs D)) (levelOfExecution_final E P T ι)).trans h

end P1Wit.SolWitfill
