import P1Int.Records

/-!
# P1Int.TrueRecordsDefs: term tables of an execution tree without proofs (p11_records, R2 interface)

Owner: P1-lean-integ (Opus, 2026-11-25). Witfill's `ExecutionTerms` (Wit/P1Wit/WitBranchRecords.lean) needs at each node
an EMBEDDING of the step choices into term tables and the proof `start < D.top + 1`. Here:
* `TermTableN D ℓ` = witfill's `TermTable D ⟨ℓ, _⟩` with a natural level;
* `TableSupply D E start`: a term table for every choice at every node (data only);
* `TablesInjective`: at every node the map choice ↦ table is injective;
* `mkTerms`: fit facts + supply + injectivity give `ExecutionTerms`;
* `mkRecordsT`: the record package from the fit facts, panel values and term tables.
The TRUE tables and values (the ones the checks force) are the Sol item P1-sol-truerec (`trueSupply`, `trueTables`,
`trueTables_injective`).
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill

section Tree

variable {R : Type*} [CommSemiring R] {b n : ℕ}

/-- Witfill's term table at a natural level. -/
abbrev TermTableN (D : Dims) (ℓ : ℕ) :=
  Fin ((D.lv ℓ).bases * (D.lv ℓ).termKeys) → TermSlot D (D.lv ℓ)

/-- **Term tables of an execution tree** (data only). -/
def TableSupply (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ) : Type :=
  match E with
  | .done _ => PUnit
  | .more p tail => (p.step.Choice → TermTableN D start) × ((i : _) → TableSupply D (tail i) (start + 1))

/-- At every node the map choice ↦ table is injective. -/
def TablesInjective (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ)
    (ts : TableSupply D E start) : Prop :=
  match E, ts with
  | .done _, _ => True
  | .more _ tail, ts => Function.Injective ts.1 ∧ ∀ i, TablesInjective D (tail i) (start + 1) (ts.2 i)

/-- Fit facts, tables and injectivity give witfill's `ExecutionTerms`. -/
def mkTerms (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ)
    (hf : ExecFits D E start) (ts : TableSupply D E start) (hinj : TablesInjective D E start ts) :
    ExecutionTerms D E start :=
  match E, hf, ts, hinj with
  | .done _, _, _, _ => ()
  | .more _ tail, hf, ts, hinj =>
    (⟨Nat.lt_succ_of_lt hf.1, ⟨ts.1, hinj.1⟩⟩,
      fun i => mkTerms D (tail i) (start + 1) (hf.2.2 i) (ts.2 i) (hinj.2 i))

end Tree

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- **The record package from fit facts, panel values and injective term tables.** -/
def mkRecordsT (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hfit : RecordsFitStmt Bt κ hκ V a b x d bigBias termBias)
    (sv : ∀ σ, PanelSupply (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0)
    (ts : ∀ σ, TableSupply (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0)
    (hinj : ∀ σ, TablesInjective (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0
      (ts σ)) :
    FixedRecords Bt κ hκ V a b x d bigBias termBias :=
  mkRecords Bt κ hκ V a b x d bigBias termBias hfit sv
    (fun σ => mkTerms _ _ 0 (hfit.choose_spec.choose_spec.2.1 σ) (ts σ) (hinj σ))

end

end P11

end P1Int
