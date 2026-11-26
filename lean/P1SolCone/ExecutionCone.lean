import P1SolCone.NumericLevel
import P1SolCone.BranchPanels
import OAI.Computability.VPVNP.CompressorExecutionLevels

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel OAI.Computability.VPVNP.CompressorRecords
open OAI.Computability.VPVNP.Compression.Refresh OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.Compression.ShrinkMotif OAI.Computability.VPVNP.Compression.ShrinkEnergy
open P1ChkFinal P1Wit P1P7 P1P5.KW
open OAI.Computability.IntegerMultiplication.Code

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)

local notation "degH" => 2 ^ S.expanderExponent
local notation "Hpos" => Nat.two_pow_pos S.expanderExponent
local notation "Hconn" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "SolS" => And.left (Iff.mp (B.solution_iff κ) hκ)
local notation "SolR" => And.right (Iff.mp (B.solution_iff κ) hκ)

/-- Evaluators obtained from the scheduled kernel writers, with the values of the exact
local input codes. The encoded history need only supply these inputs. -/
structure ScheduleKernelsOK (values : KernelValues R) : Prop where
  shrink : ∀ (i : Fin S.steps) (g : ℕ)
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (s : X.ShrinkSelection B.shrink) (x : X.Base) (j : TagW (S.degreeExponent i.castSucc)) (l : BitWord g),
    let p := X.shrinkStatePass B.shrink (κ ∘ Sum.inl) SolS (S.shrink i)
    let t := p.step.term s
    ∀ (pa : Placed t.place X.network.Half ((x, j), l))
      (z : (p.next s).network.Half ((x, j), l)) (ps : List PosCode) (pad : Tally),
      PlacedList X _ _ pa ps → shrinkWordCount B.shrink X s x j l ≤ pad.length →
      values.shrink (S.degreeExponent i.castSucc) (S.degreeExponent i.succ)
        (paddedShrinkInput B.shrink (S.shrink i) X s x j l ps z pad) = t.kernel ((x, j), l) pa z
  refresh : ∀ (g : ℕ) (X : State S.portExponent (S.portExponent + g))
    (c : DyadicRefreshChoice X S.graph Hpos Hconn B.refresh) (x : X.Base)
    (j : Fin (2 ^ S.portExponent)) (l : BitWord g),
    let p := dyadicRefreshPass X S.graph Hpos Hconn B.refresh S.port_order S.degree_bounds.2
      (κ ∘ Sum.inr) SolR
    let t := p.step.term c
    ∀ (pa : Placed t.place X.network.Half ((x, j), l))
      (z : (p.next c).network.Half ((x, j), l)) (ps : List PosCode),
      PlacedList X _ _ pa ps →
      values.refresh (refreshKIn S.graph Hpos Hconn B.refresh S.port_order S.degree_bounds.2
        g X c x j l ps z) = t.kernel ((x, j), l) pa z

/-- The D1 fields and D2 decoder agreement required at the head of the selected branch.
Arc and width correctness is instead proved from the actual P6 encoding. -/
def OriginExtras (D : Dims) (u : List Bool) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass R X b n} (origin : PassOrigin B κ hκ p) : p.step.Choice → Prop := by
  cases origin with
  | shrink i hm X =>
    subst_vars
    intro s
    exact (∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y).val) ∧
      (∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y)) ∧
      (rdLayout D u ℓ = if layoutBit B.shrink X s then 1 else 0) ∧
      (∀ y, termsDec D u ℓ (addr X y) = choiceAt B.shrink X s y)
  | refresh X =>
    intro c
    exact ∀ (y : X.Base) (l : _) (jh : Fin (2 ^ S.portExponent) × Fin degH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + (jh.1.val * degH + jh.2.val)) = (c (y, l)).val jh

def BranchExtras (D : Dims) (u : List Bool) {b n : ℕ} :
    {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) →
      PassOrigins B κ hκ E → E.Choices → ℕ → Prop
  | _, _, _, .done _, _, _, _ => True
  | _, _, _, .more _ tail, origins, c, ℓ =>
    OriginExtras B κ hκ D u ℓ origins.1 c.1 ∧ BranchExtras D u (tail c.1) (origins.2 c.1) c.2 (ℓ + 1)

/-- The pad requirement of a selected pass. Refresh writers have no internal-word sum. -/
def OriginPadOK (pad : Tally) {a g b n : ℕ} {X : State a g}
    {p : StatePass R X b n} (origin : PassOrigin B κ hκ p) : p.step.Choice → Prop := by
  cases origin with
  | shrink i hm X =>
    subst_vars
    intro s
    exact ∀ x j l, shrinkWordCount B.shrink X s x j l ≤ pad.length
  | refresh X => exact fun _ => True

def BranchPadOK (pad : Tally) {b n : ℕ} :
    {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) →
    PassOrigins B κ hκ E → E.Choices → Prop
  | _, _, _, .done _, _, _ => True
  | _, _, _, .more _ tail, origins, c =>
    OriginPadOK B κ hκ pad origins.1 c.1 ∧ BranchPadOK pad (tail c.1) (origins.2 c.1) c.2

def outputCoding {a g b n : ℕ} {X : State a g} (p : StatePass R X b n) (s : p.step.Choice) :
    KeyCoding (p.step.term s).output := (p.output_eq s).symm ▸ stateCoding (p.next s)

theorem levelOfOrigin_ok (values : KernelValues R) (hv : ScheduleKernelsOK B κ hκ values)
    (pad : Tally) (D : Dims) (u : List Bool) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass R X b n} (origin : PassOrigin B κ hκ p) (s : p.step.Choice)
    (hOld : StatePanelOK D u ℓ X) (hNew : StatePanelOK D u (ℓ + 1) (p.next s))
    (hExtra : OriginExtras B κ hκ D u ℓ origin s)
    (hPad : OriginPadOK B κ hκ pad origin s) :
    NumericLevelOK (p.step.term s) (stateCoding X) (outputCoding p s)
      (phasePreimages D u ℓ) (phaseHalves D u ℓ) (phaseKernel values pad degH D u ℓ) := by
  cases origin with
  | shrink i hm X =>
    subst_vars
    obtain ⟨hcol, hoff, hlay, hterm⟩ := hExtra
    exact shrinkLevel_ok B.shrink (S.shrink i) (κ ∘ Sum.inl) SolS values pad degH D u ℓ X s
      (phaseShape_eq D ℓ _ _ _ _ hOld.slots hNew.slots hOld.lanes hNew.lanes)
      hOld.slots hOld.bases hOld.panel hcol hoff hterm hlay
      (fun x j l pa z ps hp => hv.shrink i _ X s x j l pa z ps pad hp (hPad x j l))
  | refresh X =>
    exact refreshLevel_ok S.graph Hpos Hconn B.refresh S.port_order S.degree_bounds.2 (κ ∘ Sum.inr)
      SolR values pad D u ℓ X s (phaseShape_eq D ℓ _ _ _ _ hOld.slots hNew.slots hOld.lanes hNew.lanes)
      hOld.slots hOld.bases hOld.panel hExtra (hv.refresh _ X s)

private theorem numericChain_cast {N N' Y : Network} (eq : N' = N)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → R)
    (c : TermChain R N Y) (src : KeyCoding N) (dst : KeyCoding Y) (phases : List ℕ)
    (h : NumericChainOK pre halves kernel c src dst phases) :
    NumericChainOK pre halves kernel (eq.symm ▸ c : TermChain R N' Y) (eq.symm ▸ src) dst phases := by
  subst N'
  exact h

/-- A selected compression execution has a compatible numerical table at every phase. -/
theorem numericChain_execution (values : KernelValues R) (hv : ScheduleKernelsOK B κ hκ values)
    (pad : Tally) (D : Dims) (u : List Bool) {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X) :
    ∀ (rec : E.Records) (origins : PassOrigins B κ hκ E) (c : E.Choices) (ℓ : ℕ),
      BranchPanelsOK D u E c ℓ → BranchExtras B κ hκ D u E origins c ℓ →
      BranchPadOK B κ hκ pad E origins c →
      NumericChainOK (phasePreimages D u) (phaseHalves D u) (phaseKernel values pad degH D u)
        (E.termChain rec c) (stateCoding X) (stateCoding (E.finalState c)) (List.range' ℓ (D.top - ℓ)) := by
  induction E with
  | done X =>
    intro rec origins c ℓ hp he hpad
    exact ⟨by rw [hp.2, Nat.sub_self]; rfl, rfl⟩
  | more p tail ih =>
    intro rec origins c ℓ hp he hpad
    obtain ⟨hOld, hLt, hTail⟩ := hp
    obtain ⟨hExtra, hRest⟩ := he
    have hNew := hTail.head
    have hLevel := levelOfOrigin_ok B κ hκ values hv pad D u ℓ origins.1 c.1 hOld hNew hExtra hpad.1
    have hh := ih c.1 (rec.2 c.1) (origins.2 c.1) c.2 (ℓ + 1) hTail hRest hpad.2
    have ht := numericChain_cast (p.output_eq c.1) _ _ _ _ _ _ _ hh
    exact ⟨ℓ, List.range' (ℓ + 1) (D.top - (ℓ + 1)), outputCoding p c.1,
      by rw [show D.top - ℓ = D.top - (ℓ + 1) + 1 from by omega, List.range'_succ], hLevel, ht⟩

end

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.numericChain_execution
