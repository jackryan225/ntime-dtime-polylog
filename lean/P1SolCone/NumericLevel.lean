import P1SolCone.Tables
import P1SolCone.Placement
import P1SolCone.KernelReads
import P1SolCone.PanelReads
import P1SolCone.HalfWords

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open P1P7 P1ChkFinal
open P1Wit P1P5.KW

/-- The typed arguments needed at one numerical phase. Logarithms of the axis counts agree
with binary degrees and lane counts at a genuine level. -/
structure PhaseShape where
  inDegree : ℕ
  outDegree : ℕ
  inLanes : ℕ
  outLanes : ℕ

def phaseShape (D : Dims) (ℓ : ℕ) : PhaseShape :=
  ⟨Nat.log 2 (D.lv ℓ).slots, Nat.log 2 (D.lv (ℓ + 1)).slots,
    Nat.log 2 (D.lv ℓ).lanes, Nat.log 2 (D.lv (ℓ + 1)).lanes⟩

/-- A refresh drops only the promoted port bits. A shrink also drops the packing bits. -/
def PhaseShape.isShrink (s : PhaseShape) : Bool := decide (s.inDegree + s.outLanes < s.inLanes)

theorem phaseShape_eq (D : Dims) (ℓ a b G g : ℕ)
    (ha : (D.lv ℓ).slots = 2 ^ a) (hb : (D.lv (ℓ + 1)).slots = 2 ^ b)
    (hG : (D.lv ℓ).lanes = 2 ^ G) (hg : (D.lv (ℓ + 1)).lanes = 2 ^ g) :
    phaseShape D ℓ = ⟨a, b, G, g⟩ := by
  simp only [phaseShape, ha, hb, hG, hg, Nat.log_pow (by decide : 1 < (2 : ℕ))]

theorem shape_shrink (a b g : ℕ) :
    (PhaseShape.mk a b (packingLaneBits a g) g).isShrink = true := by
  apply decide_eq_true
  change a + g < packingLaneBits a g
  unfold packingLaneBits
  omega

theorem shape_refresh (a b g : ℕ) : (PhaseShape.mk a b (a + g) g).isShrink = false := by
  simp only [PhaseShape.isShrink, lt_self_iff_false, decide_false]

def phasePreimages (D : Dims) (u : List Bool) (ℓ : ℕ) (v : PositionCode) : List PositionCode :=
  let s := phaseShape D ℓ
  bif s.isShrink then shrinkPreimages D u ℓ s.inDegree s.outLanes v
  else [refreshPreimage s.inDegree s.outLanes v]

def phaseHalves (D : Dims) (u : List Bool) (ℓ : ℕ) (v : PositionCode) : List HalfCode :=
  halfCodes (readHalfWidths D u ℓ v)

/-- One kernel evaluator per scheduled shrink shape and one for refresh. -/
structure KernelValues (F : Type) where
  shrink : ℕ → ℕ → ShrinkKIn → F
  refresh : RefreshKIn → F

noncomputable def phaseKernel {F : Type} (val : KernelValues F) (pad : Tally) (dH : ℕ)
    (D : Dims) (u : List Bool) (ℓ : ℕ) (k : KeyCode) (placed : List KeyCode) : F :=
  let s := phaseShape D ℓ
  bif s.isShrink then val.shrink s.inDegree s.outDegree
    (readShrinkKIn pad D u ℓ s.inDegree s.outLanes k.1 placed k.2)
  else val.refresh (readRefreshKIn D u ℓ s.inDegree s.outLanes dH k.1 placed k.2)

/-- The numerical cone of the final half-label, using precisely the witness's phase rows. -/
noncomputable def readTables {F : Type} (val : KernelValues F) (pad : Tally) (dH : ℕ)
    (D : Dims) (u : List Bool) (k : KeyCode) : List KeyCode × List (P1P5.Level F) :=
  assembleChain (phasePreimages D u) (phaseHalves D u) (phaseKernel val pad dH D u) (List.range D.top) [k]

/-- The numerical D9 position and the slot-ordered half words of the actual state. -/
noncomputable def stateCoding {a g : ℕ} (X : State a g) : KeyCoding X.network where
  position := fun s => (addr X s.1, bwNum s.2)
  half := halfWords X
  position_injective := positionCode_injective X
  half_injective := halfWords_injective X

theorem stateCoding_half_eq {a g : ℕ} (X : State a g) (s : X.network.Site) (z : X.network.Half s) :
    (stateCoding X).half s z = halfCode X s z := rfl

theorem phaseHalves_cover_valid {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a g)
    (hslots : (D.lv ℓ).slots = 2 ^ a) (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (s : X.network.Site) :
    (∀ z, (stateCoding X).half s z ∈ phaseHalves D u ℓ ((stateCoding X).position s)) ∧
    (∀ m ∈ phaseHalves D u ℓ ((stateCoding X).position s), ∃ z, (stateCoding X).half s z = m) := by
  change (∀ z, halfWords X s z ∈ halfCodes (readHalfWidths D u ℓ (addr X s.1, bwNum s.2))) ∧ _
  have widths := readHalfWidths_eq D u ℓ X hslots hPanel s
  constructor
  · intro z
    rw [widths, mem_halfCodes]
    simp only [halfWords, List.map_ofFn]
    constructor
    all_goals
      apply congrArg List.ofFn
      funext k
      exact List.length_ofFn
  · intro m hm
    change m ∈ halfCodes (readHalfWidths D u ℓ (addr X s.1, bwNum s.2)) at hm
    rw [widths, mem_halfCodes] at hm
    exact halfWords_of_widths X s m hm.1 hm.2

section Shrink

variable {a b g : ℕ} {δ factor : ℝ} {k : Type} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {R : Type} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)

/-- The numeric predecessor list at a shrinking site supplies the typed order required
by the writer and by the D11 pointer calculation. -/
theorem shrinkPreimages_enum (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hColor : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y).val)
    (hOffset : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hLayout : rdLayout D u ℓ = if layoutBit B X s then 1 else 0)
    (x : X.Base) (j : TagW a) (l : BitWord g) :
    let t := (X.shrinkStatePass B κ hκ ready).step.term s
    let Y := X.shrinkNext B ready s
    let w : Y.network.Site := ((x, j), l)
    ∃ us : List (t.Preimage w), P1P5.IsEnum us ∧
      shrinkPreimages D u ℓ a g ((stateCoding Y).position w) =
        us.map (fun q => (stateCoding X).position q.val) := by
  intro t Y w
  let p : PositionCode := (addr X x * 2 ^ packingTagBits (2 ^ a) + bwNum j, bwNum l)
  have target : (stateCoding Y).position w = p := by
    change (addr (X.shrinkNext B ready s) (x, j), bwNum l) = p
    rw [shrink_addr B ready X s x j, Nat.mul_comm]
    rfl
  rw [target]
  have isPre (old : X.network.Site) : (stateCoding X).position old ∈ shrinkPreimages D u ℓ a g p ↔
      w = t.place old := by
    change (addr X old.1, bwNum old.2) ∈ shrinkPreimages D u ℓ a g p ↔
      ((x, j), l) = oplace X (layoutBit B X s) old
    rw [← layoutOf_eq D u ℓ hLayout]
    exact mem_shrinkPreimages X D u ℓ hPanel hColor hOffset x j l old
  refine enum_of_codes (fun q : t.Preimage w => (stateCoding X).position q.val) ?_ _
    (shrinkPreimages_nodup D u ℓ a g p) (fun q => (isPre q.val).mpr q.property) ?_
  · intro v v' he
    exact Subtype.ext ((stateCoding X).position_injective he)
  · intro code hc
    obtain ⟨old, he⟩ := shrinkPreimages_valid X D u ℓ hPanel x j l hc
    change (stateCoding X).position old = code at he
    exact ⟨⟨old, (isPre old).mp (by rw [he]; exact hc)⟩, he⟩

theorem shrinkLevel_ok (val : KernelValues R) (pad : Tally) (dH : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (hShape : phaseShape D ℓ = ⟨a, b, packingLaneBits a g, g⟩)
    (hSlots : (D.lv ℓ).slots = 2 ^ a) (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hColor : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y).val)
    (hOffset : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (hTerm : ∀ y, termsDec D u ℓ (addr X y) = choiceAt B X s y)
    (hLayout : rdLayout D u ℓ = if layoutBit B X s then 1 else 0)
    (hEval : let t := (X.shrinkStatePass B κ hκ ready).step.term s
      ∀ (x : X.Base) (j : TagW a) (l : BitWord g)
      (pa : Placed t.place X.network.Half ((x, j), l))
      (z : (X.shrinkNext B ready s).network.Half ((x, j), l)) (ps : List PosCode),
      PlacedList X _ _ pa ps → val.shrink a b (paddedShrinkInput B ready X s x j l ps z pad) = t.kernel ((x, j), l) pa z) :
    NumericLevelOK ((X.shrinkStatePass B κ hκ ready).step.term s) (stateCoding X)
      (stateCoding (X.shrinkNext B ready s)) (phasePreimages D u ℓ) (phaseHalves D u ℓ)
      (phaseKernel val pad dH D u ℓ) := by
  let t := (X.shrinkStatePass B κ hκ ready).step.term s
  let Y := X.shrinkNext B ready s
  have reads := phaseHalves_cover_valid D u ℓ X hSlots hPanel
  refine ⟨?_, fun _ => halfCodes_nodup _, fun w => (reads w).1, fun w => (reads w).2, ?_⟩
  · rintro ⟨⟨x, j⟩, l⟩
    simp only [phasePreimages, hShape, shape_shrink, Bool.cond_true]
    exact shrinkPreimages_enum B ready κ hκ D u ℓ X s hPanel hColor hOffset hLayout x j l
  · rintro ⟨⟨x, j⟩, l⟩ z pa us hus
    let ps : List PosCode := us.map fun q => (stateCoding X).key ⟨q.val, pa q.val q.property⟩
    have hp : PlacedList X t.place ((x, j), l) pa ps := ⟨us, hus.1, hus.2, rfl⟩
    simp only [phaseKernel, hShape, shape_shrink, Bool.cond_true]
    change val.shrink a b (readShrinkKIn pad D u ℓ a g (addr Y (x, j), bwNum l) ps
      (halfCode Y ((x, j), l) z)) = _
    have addr_eq : addr Y (x, j) = addr X x * 2 ^ packingTagBits (2 ^ a) + bwNum j := by
      rw [shrink_addr B ready X s x j, Nat.mul_comm]
      rfl
    rw [addr_eq]
    exact (congrArg (val.shrink a b)
      (readShrinkKIn_eq B ready pad D u ℓ X s hN hPanel hColor hOffset hTerm hLayout x j l ps z)).trans
      (hEval x j l pa z ps hp)

end Shrink

section Refresh

open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh OAI.Computability.VPVNP.Compression.DegreeRefresh

variable {a b g dH : ℕ} {k : Type} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (B : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ b) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ b)
variable {R : Type} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)

/-- A refresh has a single predecessor. The port digit of the output base address
is returned to the old lane. -/
theorem refreshPreimages_enum (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn B)
    (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g) :
    let t := (dyadicRefreshPass X P hdH hconn B hD hd κ hκ).step.term c
    let Y := dyadicRefreshNext X P hdH hconn B hD hd c
    let w : Y.network.Site := ((x, j), l)
    ∃ us : List (t.Preimage w), P1P5.IsEnum us ∧
      [refreshPreimage a g ((stateCoding Y).position w)] =
        us.map (fun q => (stateCoding X).position q.val) := by
  intro t Y w
  let e : X.network.Site ≃ Y.network.Site :=
    ((Equiv.refl X.Base).prodCongr (splitBitWord a g).toEquiv).trans
      (refreshPositions (bitWordFinEquiv a))
  have place (q : X.network.Site) : t.place q = e q := rfl
  let old := e.symm w
  have hit : w = t.place old := by rw [place, Equiv.apply_symm_apply]
  let q : t.Preimage w := ⟨old, hit⟩
  refine ⟨[q], ⟨List.nodup_singleton _, ?_⟩, ?_⟩
  · intro u
    apply List.mem_singleton.mpr
    apply Subtype.ext
    apply e.injective
    rw [← place, ← u.property, show e q.val = w from e.apply_symm_apply w]
  · have pos (s : X.network.Site) : (stateCoding Y).position (e s) =
        (addr X s.1 * 2 ^ a + bwNum (splitBitWord a g s.2).1,
          bwNum (splitBitWord a g s.2).2) := by
      change (bwNum (splitBitWord a g s.2).1 + 2 ^ a * addr X s.1, _) = _
      rw [Nat.add_comm, Nat.mul_comm (2 ^ a) (addr X s.1)]
      rfl
    change [refreshPreimage a g ((stateCoding Y).position w)] = [(stateCoding X).position old]
    rw [← show e old = w from e.apply_symm_apply w, pos]
    exact congrArg List.singleton (refreshPreimage_split X old)

theorem refreshLevel_ok (val : KernelValues R) (pad : Tally) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn B)
    (hShape : phaseShape D ℓ = ⟨a, b, a + g, g⟩)
    (hSlots : (D.lv ℓ).slots = 2 ^ a) (hN : (D.lv ℓ).bases = Fintype.card X.Base)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hTerm : ∀ y (l : BitWord g) (jh : Fin (2 ^ a) × Fin dH),
      rdTerms D u ℓ (addr X y) (bwNum l) (1 + (jh.1.val * dH + jh.2.val)) = (c (y, l)).val jh)
    (hEval : let t := (dyadicRefreshPass X P hdH hconn B hD hd κ hκ).step.term c
      ∀ (x : X.Base) (j : Fin (2 ^ a)) (l : BitWord g)
      (pa : Placed t.place X.network.Half ((x, j), l))
      (z : (dyadicRefreshNext X P hdH hconn B hD hd c).network.Half ((x, j), l)) (ps : List PosCode),
      PlacedList X _ _ pa ps → val.refresh (refreshKIn P hdH hconn B hD hd g X c x j l ps z) =
        t.kernel ((x, j), l) pa z) :
    NumericLevelOK ((dyadicRefreshPass X P hdH hconn B hD hd κ hκ).step.term c) (stateCoding X)
      (stateCoding (dyadicRefreshNext X P hdH hconn B hD hd c)) (phasePreimages D u ℓ)
      (phaseHalves D u ℓ) (phaseKernel val pad dH D u ℓ) := by
  let t := (dyadicRefreshPass X P hdH hconn B hD hd κ hκ).step.term c
  let Y := dyadicRefreshNext X P hdH hconn B hD hd c
  have reads := phaseHalves_cover_valid D u ℓ X hSlots hPanel
  refine ⟨?_, fun _ => halfCodes_nodup _, fun w => (reads w).1, fun w => (reads w).2, ?_⟩
  · rintro ⟨⟨x, j⟩, l⟩
    simp only [phasePreimages, hShape, shape_refresh, Bool.cond_false]
    exact refreshPreimages_enum P hdH hconn B hD hd κ hκ X c x j l
  · rintro ⟨⟨x, j⟩, l⟩ z pa us hus
    let ps : List PosCode := us.map fun q => (stateCoding X).key ⟨q.val, pa q.val q.property⟩
    have hp : PlacedList X t.place ((x, j), l) pa ps := ⟨us, hus.1, hus.2, rfl⟩
    simp only [phaseKernel, hShape, shape_refresh, Bool.cond_false]
    change val.refresh (readRefreshKIn D u ℓ a g dH (addr Y (x, j), bwNum l) ps
      (halfCode Y ((x, j), l) z)) = _
    have addr_eq : addr Y (x, j) = addr X x * 2 ^ a + j.val := by
      change j.val + 2 ^ a * addr X x = _
      rw [Nat.add_comm, Nat.mul_comm (2 ^ a)]
    rw [addr_eq]
    exact (congrArg val.refresh
      (readRefreshKIn_eq P hdH hconn B hD hd D u ℓ X c hN hPanel hTerm x j l ps z)).trans
      (hEval x j l pa z ps hp)

end Refresh

#print axioms phaseHalves_cover_valid
#print axioms shrinkPreimages_enum
#print axioms refreshPreimages_enum
#print axioms shrinkLevel_ok
#print axioms refreshLevel_ok

end P1SolCone.SolCone
