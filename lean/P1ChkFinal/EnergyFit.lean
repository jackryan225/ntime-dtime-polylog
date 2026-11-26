import P1Int.TrueRecords

/-!
# P1ChkFinal.EnergyFit: the energy fit of the true records (statement; lane P1-lean-greedy, decision D16)

`TrueRecords.panelAt` stores the true shrink energy prefixes as `fieldValue D.bigW (truePrefix ..)`, i.e. modulo `2^bigW`;
`TrueHFacts` bounds the Omega prefixes but not these. The checks C8/C9 compare the stored prefixes with the true recurrence, so
the greedy field needs the prefixes below `2^bigW`. `energyTree` follows `panelTree` (same recursion, same origins
`executeOrigins`): at every shrink node, for every selection `s`, base `y` and layout `l`, `truePrefix X (termW Bt.shrink X s) y l
< 2^bigW`. `EnergyFitTarget` (one input `x`) is the hypothesis `hE` of the bridges and the field; `EnergyFitLong` (one
threshold for all long inputs, the shape of the count fit) is the target of the Astra worker.
-/

namespace P1ChkFinal.EnergyFit

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords P1Int P1Int.P11

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
variable {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- The energy bound at one pass: every shrink energy prefix is below `2^w` (refresh passes store no energy). -/
def energyOK (w : ℕ) {a g b n : ℕ} {X : State a g} {p : StatePass F X b n} (origin : PassOrigin Bt κ hκ p) : Prop := by
  cases origin with
  | shrink i h X =>
    subst h
    exact ∀ (s : X.ShrinkSelection Bt.shrink) (y : X.Base) (l : Bool),
      P1ChkGreedy.truePrefix X (P1ChkGreedy.termW Bt.shrink X s) y l < 2 ^ w
  | refresh X => exact True

/-- The energy bound at every pass of an execution tree (the recursion of `panelTree`). -/
def energyTree (w : ℕ) {a g b n : ℕ} {X : State a g} (E : StateExecution F b n X) : PassOrigins Bt κ hκ E → Prop :=
  match E with
  | .done _ => fun _ => True
  | .more _ tail => fun o => energyOK Bt κ hκ w o.1 ∧ ∀ i, energyTree w (tail i) (o.2 i)

variable [Algebra (ZMod 2) F]

/-- **The energy fit at one input** (hypothesis `hE` of the greedy bridges and field). -/
def EnergyFitTarget (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ) : Prop :=
  ∀ σ, energyTree Bt κ hκ (fixedDims Bt V a b x d bigBias termBias).bigW (fixedExec Bt κ hκ V a b x σ)
    (CompressorRecords.executeOrigins Bt κ hκ _ _ _)

end P1ChkFinal.EnergyFit

namespace P1ChkFinal.EnergyFit

/-- **The energy fit for long inputs** (target of the Astra worker; the threshold is part of the statement). -/
def EnergyFitLong : Prop :=
  ∀ {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ), 1 ≤ b →
    ∃ n₀ : ℕ, ∀ x : List Bool, n₀ ≤ x.length → EnergyFitTarget Bt κ hκ V a b x d bigBias termBias

end P1ChkFinal.EnergyFit
