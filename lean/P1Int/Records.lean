import P1Int.WitfillLink

/-!
# P1Int.Records: the record package of Sol witfill from its FIT facts and a SUPPLY of panel values (p11_records, R1)

Owner: P1-lean-integ (Opus restart, 2026-11-25). `P1Wit.SolWitfill.NetRecordInputs` (Wit/P1Wit/WitNetTuple.lean)
mixes two kinds of fields:
* FIT facts (Props): the dims match the routed network, every state of the execution tree fits the dims at its level
  (`PanelFits`), and the bounds `start_fits`, `owner_fits`, `terms_fits_flag`, `chain_fits_len`, `chain_fits_entry`,
  `omega_fits`;
* VALUES (data): per node the layout bit, colours, offsets, energies (`PanelVals`), and per node an embedding of the
  step choices into term tables (`P1Wit.SolWitfill.ExecutionTerms`).
This file separates them. `ExecFits` (the fit facts of the tree), `PanelSupply` (the values of the tree without the fit
proofs), `mkPanels` (both together give witfill's `ExecutionPanels`), `RecordsFitStmt` (ALL fit facts at the fixed
parameters, a Sol target: tracker p11_records), and `mkRecords` (fit facts + values give `FixedRecords`).
The TRUE values (the ones the checks force) are the separate step R2.
-/

namespace P1Int

namespace P11

open Filter OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill

section Tree

variable {R : Type*} [CommSemiring R] {b n : ℕ}

/-- The values of one panel beyond its structural fields (witfill's `PanelData` without `fits`). -/
structure PanelVals (D : Dims) (ℓ : ℕ) where
  layout : Bool
  colour : Fin (D.lv ℓ).bases → Fin (2 ^ (D.lv ℓ).colW)
  offset : Fin (D.lv ℓ).bases → Fin (2 ^ (D.lv ℓ).tagW)
  energy : Fin ((D.lv ℓ).bases * 2) → Fin (2 ^ D.bigW)

/-- **Fit facts of an execution tree**: every state fits the dims at its level, and the tree ends at level `D.top`. -/
def ExecFits (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ) : Prop :=
  match E with
  | .done X => start = D.top ∧ PanelFits D (D.lv start) X
  | .more p tail => start < D.top ∧ PanelFits D (D.lv start) X ∧ ∀ i, ExecFits D (tail i) (start + 1)

/-- **Values of an execution tree** (same shape as witfill's `ExecutionPanels`, without the fit proofs). -/
def PanelSupply (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ) : Type :=
  match E with
  | .done _ => PanelVals D start
  | .more p tail => (p.step.Choice → PanelVals D start) × ((i : _) → PanelSupply D (tail i) (start + 1))

/-- Fit facts and values give witfill's `ExecutionPanels`. -/
def mkPanels (D : Dims) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) (start : ℕ)
    (hf : ExecFits D E start) (sv : PanelSupply D E start) : ExecutionPanels D E start :=
  match E, hf, sv with
  | .done _, hf, sv => ⟨⟨hf.2, sv.layout, sv.colour, sv.offset, sv.energy⟩, hf.1⟩
  | .more _ tail, hf, sv =>
    (⟨fun c => ⟨hf.2.1, (sv.1 c).layout, (sv.1 c).colour, (sv.1 c).offset, (sv.1 c).energy⟩, hf.1⟩,
      fun i => mkPanels D (tail i) (start + 1) (hf.2.2 i) (sv.2 i))

end Tree

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- The execution of the compressor on the routed network of skeleton `σ`, at the fixed parameters. -/
abbrev fixedExec (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool)
    (σ : RoutedSkeleton V (P1Wrap.Params.I 1 (lpTime a b x.length)) (P1Wrap.Params.h (lpTime a b x.length))) :=
  netExecution Bt κ hκ V (P1Wrap.Params.B (lpTime a b x.length)) (P1Wrap.Params.I 1 (lpTime a b x.length))
    (h := P1Wrap.Params.h (lpTime a b x.length)) (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
    (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length)) σ

/-- The canonical tape order: `Fintype.equivFin` (`D.r = Fintype.card (toOAI V).K` in `genuineDims`). -/
abbrev fixedTapeOrder (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) :
    (toOAI V).K ≃ Fin (fixedDims Bt V a b x d bigBias termBias).r :=
  Fintype.equivFin (toOAI V).K

/-- **ALL fit facts of the record package at the fixed parameters** (Sol target, tracker p11_records).
The dims equalities are stated as equalities; the later conjuncts quantify over their proofs (proof irrelevance). -/
def RecordsFitStmt (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) : Prop :=
  ∃ (hI : (fixedDims Bt V a b x d bigBias termBias).I = P1Wrap.Params.I 1 (lpTime a b x.length))
    (hN : (fixedDims Bt V a b x d bigBias termBias).N = 2 ^ P1Wrap.Params.h (lpTime a b x.length)),
    (∀ (σ : RoutedSkeleton V (P1Wrap.Params.I 1 (lpTime a b x.length)) (P1Wrap.Params.h (lpTime a b x.length)))
      (i : Fin (fixedDims Bt V a b x d bigBias termBias).I) (j : Fin (fixedDims Bt V a b x d bigBias termBias).r),
      zigzag (P1Net.betaOf (netSkeleton V (P1Wrap.Params.I 1 (lpTime a b x.length)) hI hN
        (fixedTapeOrder Bt V a b x d bigBias termBias) σ) j
        (i.val * (fixedDims Bt V a b x d bigBias termBias).N)) <
        2 ^ (fixedDims Bt V a b x d bigBias termBias).bigW) ∧
    (∀ σ, ExecFits (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0) ∧
    (fixedDims Bt V a b x d bigBias termBias).I < 2 ^ (fixedDims Bt V a b x d bigBias termBias).bigW ∧
    0 < (fixedDims Bt V a b x d bigBias termBias).wW ∧
    (∀ σ ι, Fintype.card ((fixedExec Bt κ hκ V a b x σ).finalState ι).network.Site + 1 ≤
      (fixedDims Bt V a b x d bigBias termBias).chainLen) ∧
    d ≤ 2 ^ (fixedDims Bt V a b x d bigBias termBias).chainW ∧
    (∀ σ (hf : ExecFits (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0)
      (sv : PanelSupply (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0) ι
      (y : Fin ((fixedDims Bt V a b x d bigBias termBias).lv (fixedDims Bt V a b x d bigBias termBias).top).bases),
      widthPrefix (finValue ((mkPanels (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0
          hf sv).final (fixedExec Bt κ hκ V a b x σ) ι).fits.wireWidth)
        (y.val * (((fixedDims Bt V a b x d bigBias termBias).lv (fixedDims Bt V a b x d bigBias termBias).top).lanes *
          ((fixedDims Bt V a b x d bigBias termBias).lv (fixedDims Bt V a b x d bigBias termBias).top).slots)) <
        2 ^ (fixedDims Bt V a b x d bigBias termBias).bigW)

/-- **The record package from the fit facts and a supply of values** (tape order `fixedTapeOrder`). -/
def mkRecords (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hfit : RecordsFitStmt Bt κ hκ V a b x d bigBias termBias)
    (sv : ∀ σ, PanelSupply (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0)
    (tm : ∀ σ, ExecutionTerms (fixedDims Bt V a b x d bigBias termBias) (fixedExec Bt κ hκ V a b x σ) 0) :
    FixedRecords Bt κ hκ V a b x d bigBias termBias where
  interval_count := hfit.choose
  initial_lanes := hfit.choose_spec.choose
  tape_order := fixedTapeOrder Bt V a b x d bigBias termBias
  start_fits := hfit.choose_spec.choose_spec.1
  panels := fun σ => mkPanels _ _ 0 (hfit.choose_spec.choose_spec.2.1 σ) (sv σ)
  terms := tm
  owner_fits := hfit.choose_spec.choose_spec.2.2.1
  terms_fits_flag := hfit.choose_spec.choose_spec.2.2.2.1
  chain_fits_len := hfit.choose_spec.choose_spec.2.2.2.2.1
  chain_fits_entry := hfit.choose_spec.choose_spec.2.2.2.2.2.1
  omega_fits := fun σ ι y =>
    hfit.choose_spec.choose_spec.2.2.2.2.2.2 σ (hfit.choose_spec.choose_spec.2.1 σ) (sv σ) ι y

end

/-- **Target (Sol), tracker p11_records (R1)**: the fit facts hold at the fixed parameters for all long inputs. -/
def RecordsFitTarget : Prop :=
  ∀ {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F]
    (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ), 1 ≤ b →
    ∃ n₂ : ℕ, ∀ x : List Bool, n₂ ≤ x.length → RecordsFitStmt Bt κ hκ V a b x d bigBias termBias

end P11

end P1Int
