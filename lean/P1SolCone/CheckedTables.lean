import P1SolCone.ExecutionCone
import P1SolCone.BranchCaps
import Mathlib.Data.List.NodupEquivFin

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.IntegerMultiplication.Code
open P1Wit P1P7 P1ChkFinal
open scoped Classical

def widthsWithin (cap : ℕ) (ws : List ℕ × List ℕ) : Bool :=
  ws.1.all (fun w => decide (w ≤ cap)) && ws.2.all (fun w => decide (w ≤ cap))

theorem stateWidthsWithin {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a g)
    (hp : StatePanelOK D u ℓ X) (cap : ℕ) (hw : X.maxWireWidth ≤ cap) (s : X.network.Site) :
    widthsWithin cap (readHalfWidths D u ℓ ((stateCoding X).position s)) = true := by
  change widthsWithin cap (readHalfWidths D u ℓ (addr X s.1, bwNum s.2)) = true
  rw [readHalfWidths_eq D u ℓ X hp.slots hp.panel s]
  simp only [widthsWithin, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro w hm
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hm
    exact (X.width_le_maxWireWidth _).trans hw
  · intro w hm
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hm
    exact (X.width_le_maxWireWidth _).trans hw

/-- Check sizes before expanding the half-assignments at one new site. -/
def phaseAllowed (D : Dims) (u : List Bool) (c w ℓ : ℕ) (key : KeyCode) : Bool :=
  let old := phasePreimages D u ℓ key.1
  decide (old.length ≤ c) && old.all (fun s => widthsWithin w (readHalfWidths D u ℓ s))

theorem phaseAllowed_of_level {R : Type} [CommRing R] {a g : ℕ} {X : State a g}
    (D : Dims) (u : List Bool) (ℓ c w : ℕ) (t : Term R X.network) (dst : KeyCoding t.output)
    (values : KernelValues R) (pad : Tally) (dH : ℕ) (hp : StatePanelOK D u ℓ X)
    (h : NumericLevelOK t (stateCoding X) dst (phasePreimages D u ℓ) (phaseHalves D u ℓ)
      (phaseKernel values pad dH D u ℓ))
    (hw : X.maxWireWidth ≤ w) (hc : ∀ v, Fintype.card (t.Preimage v) ≤ c) (key : P1P5.Key t.output) :
    phaseAllowed D u c w ℓ (dst.key key) = true := by
  obtain ⟨ps, hps, hpEq⟩ := h.predecessors key.1
  unfold phaseAllowed
  let old := phasePreimages D u ℓ (dst.position key.1)
  change (decide (old.length ≤ c) && old.all (fun s => widthsWithin w (readHalfWidths D u ℓ s))) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, old]
  rw [hpEq]
  simp only [List.length_map]
  constructor
  · have hlen := Fintype.card_congr (List.Nodup.getEquivOfForallMemList ps hps.1 hps.2)
    rw [Fintype.card_fin] at hlen
    exact hlen.symm ▸ hc key.1
  · intro s hs
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hs
    exact stateWidthsWithin D u ℓ X hp w hw v.val

/-- The backward traversal stops if any requested level fails its bounds checks. -/
def assembleCheckedChain {F : Type} (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) :
    List ℕ → List KeyCode → Option (List KeyCode × List (P1P5.Level F))
  | [], final => some (final, [])
  | ℓ :: tail, final => do
    let (keys, ls) ← assembleCheckedChain allow pre halves kernel tail final
    if keys.all (allow ℓ) then
      let (old, data) := assembleLevel (pre ℓ) (halves ℓ) (kernel ℓ) keys
      some (old, data :: ls)
    else none

/-- At genuine branches each numerical step matches its typed term and passes the guard. -/
def CheckedChainOK {F : Type} [CommRing F] (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) :
    {N Y : Network} → TermChain F N Y → KeyCoding N → KeyCoding Y → List ℕ → Prop
  | _, _, .done _, src, dst, phases => phases = [] ∧ src = dst
  | _, _, .more t _ tail, src, dst, phases =>
    ∃ (ℓ : ℕ) (next : List ℕ) (mid : KeyCoding t.output), phases = ℓ :: next ∧
      NumericLevelOK t src mid (pre ℓ) (halves ℓ) (kernel ℓ) ∧
      (∀ key, allow ℓ (mid.key key) = true) ∧ CheckedChainOK allow pre halves kernel tail mid dst next

theorem assembleCheckedChain_good {F : Type} [CommRing F] (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) :
    ∀ {N Y : Network} (c : TermChain F N Y) (src : KeyCoding N) (dst : KeyCoding Y)
      (phases : List ℕ) (fin : List (P1P5.Key Y)),
      CheckedChainOK allow pre halves kernel c src dst phases →
      ∃ ord : P1P5.ChainOrd c, P1P5.ChainOrd.Good c ord fin ∧
        assembleCheckedChain allow pre halves kernel phases (fin.map dst.key) =
          some ((P1P5.ChainOrd.first c ord fin).map src.key, P1P5.encLevelsO c ord) := by
  intro N Y c
  induction c with
  | done N =>
    intro src dst phases fin h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨PUnit.unit, True.intro, rfl⟩
  | more t rec tail ih =>
    intro src dst phases fin h
    rcases h with ⟨ℓ, next, mid, rfl, hhead, hallow, htail⟩
    obtain ⟨ord, hgood, hnum⟩ := ih mid dst next fin htail
    obtain ⟨level, hlevel, hnew, htable⟩ := assembleLevel_good t src mid _ _ _ hhead
      (P1P5.ChainOrd.first tail ord fin)
    have permit : ((P1P5.ChainOrd.first tail ord fin).map mid.key).all (allow ℓ) = true := by
      rw [List.all_eq_true]
      intro q hq
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hq
      exact hallow key
    refine ⟨(level, ord), ⟨hlevel, hnew, hgood⟩, ?_⟩
    rw [assembleCheckedChain, hnum]
    let keys := (P1P5.ChainOrd.first tail ord fin).map mid.key
    let tab := assembleLevel (pre ℓ) (halves ℓ) (kernel ℓ) keys
    change (if keys.all (allow ℓ) then some (tab.1, tab.2 :: P1P5.encLevelsO tail ord) else none) = _
    have htab : tab = (level.old.map src.key, P1P5.levelDataO t level) := htable
    rw [ite_eq_left permit, htab]
    rfl

private theorem checkedChain_cast {R : Type} [CommRing R] {N N' Y : Network} (eq : N' = N)
    (allow : ℕ → KeyCode → Bool) (pre : ℕ → PositionCode → List PositionCode)
    (halves : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → R)
    (c : TermChain R N Y) (src : KeyCoding N) (dst : KeyCoding Y) (phases : List ℕ)
    (h : CheckedChainOK allow pre halves kernel c src dst phases) :
    CheckedChainOK allow pre halves kernel (eq.symm ▸ c : TermChain R N' Y) (eq.symm ▸ src) dst phases := by
  subst N'
  exact h

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)

theorem checkedChain_execution (values : KernelValues R) (hv : ScheduleKernelsOK B κ hκ values)
    (pad : Tally) (D : Dims) (u : List Bool) (c w : ℕ) {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X) :
    ∀ (rec : E.Records) (origins : OAI.Computability.VPVNP.CompressorRecords.PassOrigins B κ hκ E)
      (sel : E.Choices) (ℓ : ℕ), BranchPanelsOK D u E sel ℓ → BranchExtras B κ hκ D u E origins sel ℓ →
      BranchCapsOK c w E sel → BranchPadOK B κ hκ pad E origins sel →
      CheckedChainOK (phaseAllowed D u c w) (phasePreimages D u) (phaseHalves D u)
        (phaseKernel values pad (2 ^ S.expanderExponent) D u) (E.termChain rec sel)
        (stateCoding X) (stateCoding (E.finalState sel)) (List.range' ℓ (D.top - ℓ)) := by
  induction E with
  | done X =>
    intro rec origins sel ℓ hp he hc hpad
    exact ⟨by rw [hp.2, Nat.sub_self]; rfl, rfl⟩
  | more p tail ih =>
    intro rec origins sel ℓ hp he hc hpad
    obtain ⟨hOld, hLt, hTail⟩ := hp
    obtain ⟨hExtra, hRest⟩ := he
    obtain ⟨hWidth, hCount, hCaps⟩ := hc
    have hLevel := levelOfOrigin_ok B κ hκ values hv pad D u ℓ origins.1 sel.1 hOld hTail.head hExtra hpad.1
    have hAllowed := phaseAllowed_of_level D u ℓ c w (p.step.term sel.1) (outputCoding p sel.1)
      values pad (2 ^ S.expanderExponent) hOld hLevel hWidth hCount
    have hh := ih sel.1 (rec.2 sel.1) (origins.2 sel.1) sel.2 (ℓ + 1) hTail hRest hCaps hpad.2
    have ht := checkedChain_cast (p.output_eq sel.1) _ _ _ _ _ _ _ _ hh
    exact ⟨ℓ, List.range' (ℓ + 1) (D.top - (ℓ + 1)), outputCoding p sel.1,
      by rw [show D.top - ℓ = D.top - (ℓ + 1) + 1 from by omega, List.range'_succ], hLevel, hAllowed, ht⟩

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.checkedChain_execution
