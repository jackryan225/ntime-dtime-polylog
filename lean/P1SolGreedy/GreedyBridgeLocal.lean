import P1SolGreedy.GreedyBridgePanels
import P1SolGreedy.GreedyBridgeTermRows
import P1Int.WLinkProof

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open CompressorRecords Compression.Refresh
open P1Int.P11 P1Int.SolTrueRecords P1Wit P1Wit.SolWitfill P1P7 P1ChkFinal P1ChkGreedy
open private levelDims from P1Wit.SpaceFacts
open private baseValue_addr finValue_at refresh_coord_lt from P1Int.WLinkProof

private theorem base_field_iff {a g ℓ : ℕ} {D : Dims} (u : List Bool) (X : State a g)
    (r : LevelRecords D (D.lv ℓ)) (m : Mem) (v : X.Base → ℕ)
    (hn : (D.lv ℓ).count m = Fintype.card X.Base) (hc : ∀ y, r.code m (addr X y) = v y) :
    ReadsKind D u ℓ r m ↔ ∀ y, readField D u (secLev ℓ m) (addr X y) = v y := by
  constructor
  · intro h y
    exact (h _ (hn.symm ▸ (X.baseIndex y).isLt)).trans (hc y)
  · intro h j hj
    obtain ⟨y, rfl⟩ := exists_addr_eq X (hn ▸ hj)
    exact (h y).trans (hc y).symm

private theorem energy_field_iff {a g ℓ : ℕ} {D : Dims} (u : List Bool) (X : State a g)
    (r : LevelRecords D (D.lv ℓ)) (hb : (D.lv ℓ).bases = Fintype.card X.Base)
    (hsh : (D.lv ℓ).shrink = true) (v : X.Base → Bool → ℕ)
    (hc : ∀ y l, r.code .energy (addr X y * 2 + eCode l) = v y l) :
    ReadsKind D u ℓ r .energy ↔ ∀ y l, rdEnergy D u ℓ (addr X y) (eCode l) = v y l := by
  have hn : (D.lv ℓ).count .energy = (D.lv ℓ).bases * 2 := by
    simp only [LevelDims.count, hsh, ite_true]
  constructor
  · intro h y l
    have hy := (X.baseIndex y).isLt.trans_eq hb.symm
    have hl : eCode l < 2 := by cases l <;> decide
    exact (h _ (hn.symm ▸ idx_lt hy hl)).trans (hc y l)
  · intro h j hj
    obtain ⟨⟨q, c⟩, hqc⟩ := (ord (D.lv ℓ).bases 2).surjective ⟨j, hn ▸ hj⟩
    obtain ⟨y, hy⟩ := exists_addr_eq X (q.isLt.trans_eq hb)
    have hl : ∃ l, eCode l = c.val := by
      fin_cases c
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨l, hl⟩ := hl
    have hj' : addr X y * 2 + eCode l = j := by
      rw [hy, hl]
      exact congrArg Fin.val hqc
    rw [← hj']
    exact (h y l).trans (hc y l).symm

private theorem layout_field_iff {ℓ : ℕ} {D : Dims} (u : List Bool)
    (r : LevelRecords D (D.lv ℓ)) (hsh : (D.lv ℓ).shrink = true) :
    ReadsKind D u ℓ r .layout ↔ rdLayout D u ℓ = layoutCode r.layout := by
  have hn : (D.lv ℓ).count .layout = 1 := by simp only [LevelDims.count, hsh, ite_true]
  constructor
  · intro h
    exact h 0 (hn.symm ▸ Nat.zero_lt_one)
  · intro h j hj
    have hj' : j < 1 := hn ▸ hj
    have hz : j = 0 := by omega
    subst j
    exact h

private theorem shrink_kinds_iff {D : Dims} {u : List Bool} {ℓ : ℕ} (r : LevelRecords D (D.lv ℓ))
    (hp : ∀ m, panelKind m = true → ReadsKind D u ℓ r m) :
    (∀ m, ReadsKind D u ℓ r m) ↔ ReadsKind D u ℓ r .colour ∧ ReadsKind D u ℓ r .offset ∧
      ReadsKind D u ℓ r .terms ∧ ReadsKind D u ℓ r .energy ∧ ReadsKind D u ℓ r .layout := by
  constructor
  · exact fun h => ⟨h .colour, h .offset, h .terms, h .energy, h .layout⟩
  · rintro ⟨hc, ho, ht, he, hl⟩ m
    cases m <;> first | exact hp _ rfl | assumption

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

noncomputable def originStep (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass F X b n} (o : PassOrigin Bt κ hκ p) (c : p.step.Choice) : StepRecords D (D.lv ℓ) :=
  let v := panelAt Bt κ hκ D ℓ o c
  ⟨v.layout, v.colour, v.offset, v.energy, tableAt Bt κ hκ D ℓ o c⟩

noncomputable def originRow (D : Dims) (ℓ : ℕ) {a g b n : ℕ} {X : State a g}
    {p : StatePass F X b n} (o : PassOrigin Bt κ hκ p) (f : PanelFits D (D.lv ℓ) X)
    (c : p.step.Choice) : LevelRecords D (D.lv ℓ) :=
  levelRecordsOfState X f (originStep Bt κ hκ D ℓ o c)

attribute [local instance] P1P7.instDecEqBase

private theorem c9_layout_iff {D : Dims} {u : List Bool} {a g ℓ : ℕ} (X : State a (packingLaneBits a g))
    (s : X.ShrinkSelection Bt.shrink)
    (he : ∀ y l, rdEnergy D u ℓ (addr X y) (eCode l) = truePrefix X (termW Bt.shrink X s) y l) :
    C9u D u ℓ X ↔ rdLayout D u ℓ = layoutCode (layoutBit Bt.shrink X s) := by
  have hp : EOf D u ℓ X = truePrefix X (termW Bt.shrink X s) := funext fun y => funext (he y)
  unfold C9u
  rw [hp, C9_iff Bt.shrink X s]
  exact layout_iff _ _

theorem shrink_row_iff (D : Dims) (u : List Bool) (ℓ : ℕ) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (f : PanelFits D (D.lv ℓ) X) (s : X.ShrinkSelection Bt.shrink)
    (hrow : D.lv ℓ = levelDims S.expanderExponent (S.degreeExponent i.castSucc)
      (packingLaneBits (S.degreeExponent i.castSucc) g) X.positions (some true))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (hE : ∀ y l, truePrefix X (termW Bt.shrink X s) y l < 2 ^ D.bigW)
    (hp : ∀ m, panelKind m = true →
      ReadsKind D u ℓ (originRow Bt κ hκ D ℓ (.shrink i rfl X) f s) m) :
    (∀ m, ReadsKind D u ℓ (originRow Bt κ hκ D ℓ (.shrink i rfl X) f s) m) ↔
      (∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ)) ∧
      (∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y)) ∧
      (∀ e, rawOf D u ℓ X e = termCode (trueTerms Bt.shrink X s e)) ∧
      (∀ y l, rdEnergy D u ℓ (addr X y) (eCode l) = truePrefix X (termW Bt.shrink X s) y l) ∧
      C9u D u ℓ X := by
  let r := originRow Bt κ hκ D ℓ (.shrink i rfl X) f s
  change (∀ m, ReadsKind D u ℓ r m) ↔ _
  have hs : (D.lv ℓ).shrink = true := hrow ▸ rfl
  have hb (y : X.Base) : addr X y < (D.lv ℓ).bases := (X.baseIndex y).isLt.trans_eq f.bases.symm
  have hc : ReadsKind D u ℓ r .colour ↔ ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y : ℕ) := by
    apply base_field_iff u X r .colour (fun y => (X.packingData.color y).val)
    · simpa only [LevelDims.count, hs, ite_true] using f.bases
    · intro y
      change finValue (fun j => fieldValue (D.lv ℓ).colW
        (baseValue X (fun z => (X.packingData.color z).val) j.val)) (addr X y) = _
      rw [finValue_at _ (hb y), baseValue_addr]
      apply fieldValue_val
      have hw : (D.lv ℓ).colW = Nat.clog 2 (2 * 2 ^ S.degreeExponent i.castSucc + 1) := hrow ▸ rfl
      rw [hw]
      exact (X.packingData.color y).isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have ho : ReadsKind D u ℓ r .offset ↔ ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y) := by
    apply base_field_iff u X r .offset (fun y => bwNum (X.packingData.offset y))
    · simpa only [LevelDims.count, hs, ite_true] using f.bases
    · intro y
      change finValue (fun j => fieldValue (D.lv ℓ).tagW
        (baseValue X (fun z => bwNum (X.packingData.offset z)) j.val)) (addr X y) = _
      rw [finValue_at _ (hb y), baseValue_addr]
      apply fieldValue_val
      have hw : (D.lv ℓ).tagW = packingTagBits (2 ^ S.degreeExponent i.castSucc) := hrow ▸ rfl
      rw [hw]
      exact (bitWordFinEquiv _ (X.packingData.offset y)).isLt
  have ht := shrink_term_reads u X r (trueTerms Bt.shrink X s) rfl f.bases
    (hrow ▸ rfl) (hrow ▸ rfl) (shrinkTerm_lt Bt D i X hW s)
  have he : ReadsKind D u ℓ r .energy ↔
      ∀ y l, rdEnergy D u ℓ (addr X y) (eCode l) = truePrefix X (termW Bt.shrink X s) y l := by
    apply energy_field_iff u X r f.bases hs
    intro y l
    let j : Fin ((D.lv ℓ).bases * 2) := ⟨addr X y * 2 + eCode l, idx_lt (hb y) (by cases l <;> decide)⟩
    calc
      _ = ((panelAt Bt κ hκ D ℓ (.shrink i rfl X) s).energy j).val := finValue_fin _ j
      _ = _ := (shrink_energy_exact_iff Bt κ hκ D ℓ i X s y l (hb y)).mpr (hE y l)
  have hl : ReadsKind D u ℓ r .layout ↔ rdLayout D u ℓ = layoutCode (layoutBit Bt.shrink X s) :=
    layout_field_iff u r hs
  rw [shrink_kinds_iff r hp, hc, ho, ht, he, hl]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₁, h₂, h₃, h₄, (c9_layout_iff Bt X s h₄).mpr h₅⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₁, h₂, h₃, h₄, (c9_layout_iff Bt X s h₄).mp h₅⟩

theorem refresh_row_iff (D : Dims) (u : List Bool) (ℓ : ℕ) {g : ℕ}
    (X : State S.portExponent (S.portExponent + g)) (f : PanelFits D (D.lv ℓ) X)
    (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh)
    (hrow : D.lv ℓ = levelDims S.expanderExponent S.portExponent (S.portExponent + g) X.positions (some false))
    (hnext : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      Bt.refresh S.port_order S.degree_bounds.2 c).maxWireWidth + 1 ≤ Bt.recordLimit * (X.maxWireWidth + 1))
    (hW : Bt.recordLimit * (X.maxWireWidth + 1) < 2 ^ D.wW)
    (hp : ∀ m, panelKind m = true → ReadsKind D u ℓ (originRow Bt κ hκ D ℓ (.refresh X) f c) m) :
    (∀ m, ReadsKind D u ℓ (originRow Bt κ hκ D ℓ (.refresh X) f c) m) ↔
      C7R.storedTm (dH := 2 ^ S.expanderExponent) D u ℓ X =
        trueBlockTerms S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh X c := by
  let r := originRow Bt κ hκ D ℓ (.refresh X) f c
  have hs : (D.lv ℓ).shrink = false := hrow ▸ rfl
  have hk : (D.lv ℓ).termKeys = 2 ^ g := by
    rw [hrow]
    change 2 ^ (S.portExponent + g - S.portExponent) = 2 ^ g
    rw [Nat.add_sub_cancel_left]
  apply (refresh_kinds_iff r hs hp).trans
  exact refresh_term_reads u X r (fun z => (c z).val) rfl f.bases hk (hrow ▸ rfl)
    (refresh_coord_lt Bt D X c hnext hW)

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.shrink_row_iff
#print axioms P1SolGreedy.SolBridge.refresh_row_iff
