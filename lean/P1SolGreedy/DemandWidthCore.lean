import P1ChkGreedy.LocalC78
import P1ChkFinal.C10Bits
import P1P7.ShrinkWidth

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy

namespace P1SolGreedy.SolDemand

/-- The address and displacement fields of a matching panel. -/
theorem recTrue_of_panelMatch {a g : ℕ} {D : Dims} {u : List Bool} {ℓ : ℕ}
    {X : State a (packingLaneBits a g)}
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z)) :
    RecTrue D u ℓ X := by
  intro z k
  obtain ⟨hO, hOD, _, hI, hID, _, _⟩ := hpan z k
  exact ⟨hO, hI, hOD, hID⟩

abbrev TagWord (a : ℕ) := BitWord (packingTagBits (2 ^ a))
abbrev ColorWord (a : ℕ) := BitWord (2 * 2 ^ a + 1)
abbrev Wire (V : Type*) (a g : ℕ) :=
  Arc V (BitWord a) (TagWord a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)
abbrev ThinEnd (V : Type*) (a g : ℕ) :=
  Site V (TagWord a) (BitWord g) × BitWord a

def mapWire {V V' : Type*} {a g : ℕ} (f : V → V') (e : Wire V a g) : Wire V' a g :=
  (((f e.1.1.1, e.1.1.2), e.1.2), e.2)

theorem mapWire_pack {V V' : Type*} {a g : ℕ} (f : V → V') (p : V × Fin (2 ^ a))
    (w : BitWord (packingLaneBits a g)) :
    mapWire f (packingArcEquiv V a g (p, w)) =
      packingArcEquiv V' a g ((f p.1, p.2), w) := rfl

theorem finOr0_fin {n : ℕ} [NeZero n] (k : Fin n) : finOr0 n (k : ℕ) = k :=
  ((finOr0_eq_iff _ _).mpr rfl).2

def sOut (a g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (e : Wire ℕ a g) : Wire ℕ a g :=
  let p := (packingArcEquiv ℕ a g).symm e
  let Y := p.1.1
  let k := p.1.2
  let w := p.2
  packingArcEquiv ℕ a g
    ((rdOutAddr D u ℓ Y k, finOr0 _ (rdOutFar D u ℓ Y k)),
      w + P1ChkFinal.bwOf _ (rdOutDisp D u ℓ Y k))

def sIn (a g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (e : Wire ℕ a g) : Wire ℕ a g :=
  let p := (packingArcEquiv ℕ a g).symm e
  let Y := p.1.1
  let k := p.1.2
  let w := p.2
  packingArcEquiv ℕ a g
    ((rdInAddr D u ℓ Y k, finOr0 _ (rdInFar D u ℓ Y k)),
      w - P1ChkFinal.bwOf _ (rdInDisp D u ℓ Y k))

def sThick (D : Dims) (u : List Bool) (ℓ : ℕ) {a g : ℕ} (e : Wire ℕ a g) : Prop :=
  e.2.1 (colS a D u ℓ e.1.1.1) = 1

instance (D : Dims) (u : List Bool) (ℓ : ℕ) {a g : ℕ} (e : Wire ℕ a g) :
    Decidable (sThick D u ℓ e) := by
  unfold sThick
  infer_instance

def sWidth (D : Dims) (u : List Bool) (ℓ : ℕ) {a g : ℕ} (e : Wire ℕ a g) : ℕ :=
  let p := (packingArcEquiv ℕ a g).symm e
  rdWidth D u ℓ p.1.1 (P1ChkFinal.bwNum p.2) p.1.2

def sKey {a g : ℕ} (e : Wire ℕ a g) : ℕ :=
  (((e.1.1.1 * 2 ^ packingTagBits (2 ^ a) + P1ChkFinal.bwNum e.1.1.2.1) * 2 ^ a + e.1.2) *
        2 ^ (2 * 2 ^ a + 1) + P1ChkFinal.bwNum e.2.1) * 2 ^ a + P1ChkFinal.bwNum e.2.2

section Fields

variable {a g : ℕ} {D : Dims} {u : List Bool} {ℓ : ℕ} {X : State a (packingLaneBits a g)}
variable (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
variable (hcol : ∀ z, rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))

include hpan in
theorem sOut_eq (e : Wire X.Base a g) :
    sOut a g D u ℓ (mapWire (P1P7.addr X) e) = mapWire (P1P7.addr X) (X.packingData.actual e) := by
  obtain ⟨⟨⟨y, k⟩, w⟩, rfl⟩ := (packingArcEquiv X.Base a g).surjective e
  rw [mapWire_pack]
  unfold sOut
  rw [Equiv.symm_apply_apply]
  dsimp only
  obtain ⟨hO, hOD, hOF, _, _, _, _⟩ := hpan y k
  change rdOutAddr D u ℓ (P1P7.addr X y) k = P1P7.addr X (X.slots.base.target (y, k)).1 at hO
  change rdOutDisp D u ℓ (P1P7.addr X y) k =
    P1ChkFinal.bwNum (X.slots.displacement (y, k)) at hOD
  change rdOutFar D u ℓ (P1P7.addr X y) k = ((X.slots.base.target (y, k)).2 : ℕ) at hOF
  rw [hO, hOD, hOF, P1ChkFinal.bwOf_bwNum, finOr0_fin]
  have ha : X.packingData.actual (packingArcEquiv X.Base a g ((y, k), w)) =
      packingArcEquiv X.Base a g (X.slots.actualTarget ((y, k), w)) :=
    orderedDyadicPacking_actual X.slots X.baseIndex _
  rw [ha, LiftedSlots.actualTarget_apply, mapWire_pack]

include hpan in
theorem sIn_eq (e : Wire X.Base a g) :
    sIn a g D u ℓ (mapWire (P1P7.addr X) e) = mapWire (P1P7.addr X) (X.packingData.actual.symm e) := by
  obtain ⟨⟨⟨y, k⟩, w⟩, rfl⟩ := (packingArcEquiv X.Base a g).surjective e
  rw [mapWire_pack]
  unfold sIn
  rw [Equiv.symm_apply_apply]
  dsimp only
  obtain ⟨_, _, _, hI, hID, hIF, _⟩ := hpan y k
  change rdInAddr D u ℓ (P1P7.addr X y) k = P1P7.addr X (X.slots.base.target.symm (y, k)).1 at hI
  change rdInDisp D u ℓ (P1P7.addr X y) k =
    P1ChkFinal.bwNum (X.slots.displacement (X.slots.base.target.symm (y, k))) at hID
  change rdInFar D u ℓ (P1P7.addr X y) k = ((X.slots.base.target.symm (y, k)).2 : ℕ) at hIF
  rw [hI, hID, hIF, P1ChkFinal.bwOf_bwNum, finOr0_fin]
  have ha : X.packingData.actual.symm (packingArcEquiv X.Base a g ((y, k), w)) =
      packingArcEquiv X.Base a g (X.slots.actualTarget.symm ((y, k), w)) := by
    apply X.packingData.actual.injective
    rw [Equiv.apply_symm_apply]
    have h := orderedDyadicPacking_actual X.slots X.baseIndex (X.slots.actualTarget.symm ((y, k), w))
    change X.packingData.actual (packingArcEquiv X.Base a g (X.slots.actualTarget.symm ((y, k), w))) = _ at h
    rw [h, Equiv.apply_symm_apply]
  rw [ha, LiftedSlots.actualTarget_symm_apply, mapWire_pack]

include hcol in
theorem sThick_iff (e : Wire X.Base a g) :
    sThick D u ℓ (mapWire (P1P7.addr X) e) ↔ X.packingData.thick (sourcePosition e) := by
  unfold sThick PackingData.thick
  change e.2.1 (colS a D u ℓ (P1P7.addr X e.1.1.1)) = 1 ↔ _
  unfold colS
  rw [hcol]
  rw [finOr0_fin]
  rfl

include hpan in
theorem sWidth_eq (e : Wire X.Base a g) :
    sWidth D u ℓ (mapWire (P1P7.addr X) e) = X.packingWidth e := by
  obtain ⟨⟨⟨y, k⟩, w⟩, rfl⟩ := (packingArcEquiv X.Base a g).surjective e
  rw [mapWire_pack]
  unfold sWidth
  rw [Equiv.symm_apply_apply]
  simpa only [P1P7.panel, P1P7.outWidths, State.packingWidth, Function.comp_apply,
    Equiv.symm_apply_apply] using (hpan y k).2.2.2.2.2.2 w

theorem sKey_eq (e : Wire X.Base a g) :
    sKey (mapWire (P1P7.addr X) e) = P1P7.arcKey X e := rfl

end Fields

section Offsets

def forbid (a g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) (earlier : ℕ → TagWord a) :
    SlotGraph.TagTests (2 ^ a) → TagWord a
  | ((true, i), .inl o) => tauOut a g D u ℓ Y i + incS a g D u ℓ Y o
  | ((false, i), .inl o) => tauIn a g D u ℓ Y i + incS a g D u ℓ Y o
  | ((true, i), .inr (o₁, o₂)) =>
    let Z := rdOutAddr D u ℓ Y i
    tauOut a g D u ℓ Y i + incS a g D u ℓ Y o₁ + incS a g D u ℓ Z o₂ - earlier Z
  | ((false, i), .inr (o₁, o₂)) =>
    let Z := rdInAddr D u ℓ Y i
    tauIn a g D u ℓ Y i + incS a g D u ℓ Z o₁ + incS a g D u ℓ Y o₂ - earlier Z

def pickTag (a : ℕ) (f : SlotGraph.TagTests (2 ^ a) → TagWord a) : TagWord a :=
  let index := bitWordFinEquiv (packingTagBits (2 ^ a))
  let choices := Finset.univ \ (Finset.univ.image fun t => index (f t))
  if h : choices.Nonempty then index.symm (choices.min' h) else 0

theorem pickTag_eq {a : ℕ} (f : SlotGraph.TagTests (2 ^ a) → TagWord a) (v : TagWord a)
    (hv₁ : ∀ t, bitWordFinEquiv _ v ≠ bitWordFinEquiv _ (f t))
    (hv₂ : ∀ k < bitWordFinEquiv _ v, ∃ t, bitWordFinEquiv _ (f t) = k) :
    pickTag a f = v := by
  let index := bitWordFinEquiv (packingTagBits (2 ^ a))
  let choices := Finset.univ \ (Finset.univ.image fun t => index (f t))
  have hm : index v ∈ choices := by
    simp only [choices, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    rintro ⟨t, ht⟩
    exact hv₁ t ht.symm
  have hn : choices.Nonempty := ⟨_, hm⟩
  unfold pickTag
  change (if h : choices.Nonempty then index.symm (choices.min' h) else 0) = v
  rw [dite_eq_left hn]
  apply index.injective
  rw [Equiv.apply_symm_apply]
  apply le_antisymm (Finset.min'_le _ _ hm)
  apply le_of_not_gt
  intro hlt
  obtain ⟨t, ht⟩ := hv₂ _ hlt
  have hmem := Finset.min'_mem choices hn
  exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩)

/-- Greedy offsets from the panels with addresses below the given cutoff. -/
def offsets (a g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) : ℕ → ℕ → TagWord a
  | 0 => fun _ => 0
  | n + 1 => fun Z =>
    if Z = n then pickTag a (forbid a g D u ℓ n (offsets a g D u ℓ n))
    else offsets a g D u ℓ n Z

variable {a g : ℕ} {D : Dims} {u : List Bool} {ℓ : ℕ} {X : State a (packingLaneBits a g)}

theorem forbid_eq (hr : RecTrue D u ℓ X) (z : X.Base) (f : ℕ → TagWord a)
    (t : SlotGraph.TagTests (2 ^ a)) :
    forbid a g D u ℓ (P1P7.addr X z) f t =
      X.slots.base.tagForbidden (tagShift X) z (f ∘ P1P7.addr X) t := by
  obtain ⟨⟨b, i⟩, t⟩ := t
  cases b <;> rcases t with o | ⟨o₁, o₂⟩
  · simp only [forbid, tauIn_eq hr, incS_eq hr]
    rfl
  · have hI : rdInAddr D u ℓ (P1P7.addr X z) i =
        P1P7.addr X (X.slots.base.target.symm (z, i)).1 := (hr z i).2.1
    simp only [forbid, hI, tauIn_eq hr, incS_eq hr]
    rfl
  · simp only [forbid, tauOut_eq hr, incS_eq hr]
    rfl
  · have hO : rdOutAddr D u ℓ (P1P7.addr X z) i =
        P1P7.addr X (X.slots.base.target (z, i)).1 := (hr z i).1
    simp only [forbid, hO, tauOut_eq hr, incS_eq hr]
    rfl

theorem offsets_eq (hr : RecTrue D u ℓ X) (n : ℕ) (z : X.Base) :
    offsets a g D u ℓ n (P1P7.addr X z) =
      if P1P7.addr X z < n then X.packingData.offset z else 0 := by
  induction n generalizing z with
  | zero => simp only [offsets, Nat.not_lt_zero, ite_false]
  | succ n ih =>
    simp only [offsets]
    by_cases h : P1P7.addr X z = n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
      have hf (t : SlotGraph.TagTests (2 ^ a)) :
          forbid a g D u ℓ n (offsets a g D u ℓ n) t =
            X.slots.base.tagForbidden (tagShift X) z (masked X.baseIndex 0 X.packingData.offset z) t := by
        rw [← h, forbid_eq hr]
        congr 1
        funext v
        change offsets a g D u ℓ (P1P7.addr X z) (P1P7.addr X v) =
          if P1P7.addr X v < P1P7.addr X z then X.packingData.offset v else 0
        rw [h, ih v]
      have hv := (C6_iff_least X.slots.base X.baseIndex
        (bitWordFinEquiv (packingTagBits (2 ^ a))) (tagShift X) (packingTagBits_sufficient (2 ^ a))
        X.packingData.offset z).mp
        (C6_true X.slots.base X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a)))
          (tagShift X) (packingTagBits_sufficient (2 ^ a)) z)
      exact pickTag_eq _ _ (fun t => (hf t).symm ▸ hv.1 t)
        (fun k hk => let ⟨t, ht⟩ := hv.2 k hk; ⟨t, (hf t).symm ▸ ht⟩)
    · rw [ite_eq_right h, ih]
      have hh : P1P7.addr X z < n ↔ P1P7.addr X z < n + 1 := by omega
      simp only [hh]

end Offsets

section Ranks

variable {V : Type} {a g : ℕ} [Fintype V] [DecidableEq V]
variable (P : DyadicPackingData V a g)
variable (b : Site V (TagWord a) (BitWord g) × Fin (2 ^ a))

theorem sum_assigned (p : Wire V a g → Prop) [DecidablePred p] (f : Wire V a g → ℕ) :
    (∑ e : {e : Wire V a g // p e ∧ P.assignedBundle (sourcePosition e) = b}, f e.val) =
      ∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
        if p (P.arcAtBundle b i w) then f (P.arcAtBundle b i w) else 0 := by
  let e := P.assignedArcEquiv b p
  let weight (x : {e : Wire V a g // p e ∧ P.assignedBundle (sourcePosition e) = b}) := f x.val
  change (∑ x, weight x) = _
  rw [← e.symm.sum_comp weight, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (∑ w : {w : ColorWord a // p (P.arcAtBundle b i w)}, f (P.arcAtBundle b i w.val)) = _
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun w => by simp) (fun w => f (P.arcAtBundle b i w))).symm

set_option maxHeartbeats 800000 in
/-- Count smaller keys by the two incidence directions at the thin end. -/
theorem rank_sum (key : Wire V a g → ℕ) (κ : ℕ) :
    Fintype.card {m : P.MotifFiber b // key m.1.val < κ} =
      (∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
        if ¬ P.thick (sourcePosition (P.arcAtBundle b i w)) ∧ key (P.arcAtBundle b i w) < κ
          then 1 else 0) +
      (∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
        if P.thick (sourcePosition (P.actual.symm (P.arcAtBundle b i w))) ∧
            ¬ P.thick (sourcePosition (P.arcAtBundle b i w)) ∧
            key (P.actual.symm (P.arcAtBundle b i w)) < κ then 1 else 0) := by
  classical
  let p (e : Wire V a g) := ¬ P.thick (sourcePosition e)
  let q (e : Wire V a g) := P.thick (sourcePosition (P.actual.symm e)) ∧ p e
  let weight (e : Wire V a g) : ℕ := if key e < κ then 1 else 0
  let Out := {e : Wire V a g // p e ∧ P.assignedBundle (sourcePosition e) = b}
  let In := {e : Wire V a g // P.thick (sourcePosition (P.actual.symm e)) ∧
    p e ∧ P.assignedBundle (sourcePosition e) = b}
  let instOut : Fintype Out := inferInstanceAs (Fintype {e : Wire V a g // p e ∧ P.assignedBundle (sourcePosition e) = b})
  let instIn : Fintype In := inferInstanceAs (Fintype {e : Wire V a g //
    P.thick (sourcePosition (P.actual.symm e)) ∧ p e ∧ P.assignedBundle (sourcePosition e) = b})
  let e : P.MotifFiber b ≃ Out ⊕ In :=
    P.cdIncidenceEquiv (fun c _ => P.assignedBundle c = b)
  let f := Equiv.subtypeEquivRight
    (p := fun e => P.thick (sourcePosition (P.actual.symm e)) ∧
      p e ∧ P.assignedBundle (sourcePosition e) = b)
    (q := fun e => q e ∧ P.assignedBundle (sourcePosition e) = b) (fun _ => and_assoc.symm)
  rw [Fintype.card_subtype, Finset.card_filter]
  change (∑ m : P.MotifFiber b, weight m.1.val) = _
  let mw (m : P.MotifFiber b) := weight m.1.val
  change (∑ m, mw m) = _
  rw [← e.symm.sum_comp mw, Fintype.sum_sum_type]
  change (∑ x : {x : Wire V a g // p x ∧ P.assignedBundle (sourcePosition x) = b}, weight x.val) +
    (∑ x : {x : Wire V a g // P.thick (sourcePosition (P.actual.symm x)) ∧
      p x ∧ P.assignedBundle (sourcePosition x) = b}, weight (P.actual.symm x.val)) = _
  let iw (x : {x : Wire V a g // q x ∧ P.assignedBundle (sourcePosition x) = b}) :=
    weight (P.actual.symm x.val)
  change _ + (∑ x, iw (f x)) = _
  rw [f.sum_comp iw, sum_assigned P b p weight]
  rw [show (∑ x, iw x) = ∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
    if q (P.arcAtBundle b i w) then weight (P.actual.symm (P.arcAtBundle b i w)) else 0
      from sum_assigned P b q (fun x => weight (P.actual.symm x))]
  simp only [weight, p, q, ite_and]

end Ranks

section Widths

variable {a g : ℕ}

/-- Read the old arc key in the same convention as `keyOf`. -/
def wireOf (a g : ℕ) (Y key : ℕ) : Wire ℕ a g :=
  packingArcEquiv ℕ a g
    ((Y, ⟨key % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩), laneWord a g (key / (2 ^ a)))

theorem wireOf_keyOf (Y : ℕ) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    wireOf a g Y (keyOf a g k w) = packingArcEquiv ℕ a g ((Y, k), w) := by
  have hk : keyOf a g k w % (2 ^ a) = k := by
    rw [keyOf, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt k.isLt]
  have hw : keyOf a g k w / (2 ^ a) = (bitWordFinEquiv _ w : ℕ) := by
    rw [keyOf, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt k.isLt, Nat.add_zero]
  unfold wireOf
  rw [hw]
  have hslot : (⟨keyOf a g k w % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩ : Fin (2 ^ a)) = k :=
    Fin.ext hk
  rw [hslot]
  simp only [laneWord, finOr0_fin, Equiv.symm_apply_apply]

def thinWire (D : Dims) (u : List Bool) (ℓ : ℕ) (e : Wire ℕ a g) : Wire ℕ a g :=
  if sThick D u ℓ e then sOut a g D u ℓ e else e

def atThin {V : Type*} (t : Wire V a g) (i : Fin (2 ^ a)) (w : ColorWord a) : Wire V a g :=
  ((t.1.1, i), w, t.2.2)

def sRank (D : Dims) (u : List Bool) (ℓ : ℕ) (t e : Wire ℕ a g) : ℕ :=
  (∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
    let z := atThin t i w
    if ¬ sThick D u ℓ z ∧ sKey z < sKey e then 1 else 0) +
  (∑ i : Fin (2 ^ a), ∑ w : ColorWord a,
    let z := atThin t i w
    let p := sIn a g D u ℓ z
    if sThick D u ℓ p ∧ ¬ sThick D u ℓ z ∧ sKey p < sKey e then 1 else 0)

def sTotal (D : Dims) (u : List Bool) (ℓ : ℕ) (t : Wire ℕ a g) (off : TagWord a) : ℕ :=
  ∑ uh : ColorWord a × BitWord a,
    let e : Wire ℕ a g :=
      (((t.1.1.1, (t.1.1.2.1 + off, t.1.1.2.2)), bitWordFinEquiv a t.2.2), uh)
    if sThick D u ℓ e ∧ sThick D u ℓ (sOut a g D u ℓ e) then sWidth D u ℓ e else 0

def widthsAt (D : Dims) (u : List Bool) (ℓ : ℕ) (off : ℕ → TagWord a)
    (e : Wire ℕ a g) : Bool → ℕ :=
  let t := thinWire D u ℓ e
  let total := sTotal D u ℓ t (off t.1.1.1)
  let q := PackingData.pieceCount (2 ^ a) (2 * 2 ^ a + 1)
  let rank := sRank D u ℓ t e
  demandWidths (if rank < total % q then total / q + 1 else total / q) (sWidth D u ℓ e)

attribute [local instance] P1P7.instDecEqBase

variable {D : Dims} {u : List Bool} {ℓ : ℕ} {X : State a (packingLaneBits a g)}

set_option maxHeartbeats 1000000 in
theorem widthsAt_correct
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hcol : ∀ z, rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (off : ℕ → TagWord a) (hoff : ∀ z, off (P1P7.addr X z) = X.packingData.offset z)
    (m : X.packingData.Motif) :
    widthsAt D u ℓ off (mapWire (P1P7.addr X) m.val) = demandW X m := by
  let t : Wire X.Base a g :=
    if X.packingData.thick (sourcePosition m.val) then X.packingData.actual m.val else m.val
  have ht : sourcePosition t = X.packingData.C m := by
    unfold t PackingData.C
    split_ifs <;> rfl
  have hthin : thinWire D u ℓ (mapWire (P1P7.addr X) m.val) = mapWire (P1P7.addr X) t := by
    have hh := sThick_iff hcol m.val
    by_cases hs : X.packingData.thick (sourcePosition m.val)
    · rw [thinWire, ite_eq_left (hh.mpr hs), sOut_eq hpan m.val]
      simp only [t, ite_eq_left hs]
    · rw [thinWire, ite_eq_right (fun h => hs (hh.mp h))]
      simp only [t, ite_eq_right hs]
  let b := X.packingData.bundle m
  have hb : b = ((t.1.1.1, (t.1.1.2.1 + X.packingData.offset t.1.1.1, t.1.1.2.2)),
      bitWordFinEquiv a t.2.2) := by
    change X.packingData.assignedBundle (X.packingData.C m) = _
    rw [← ht]
    rfl
  have hat (i : Fin (2 ^ a)) (w : ColorWord a) : X.packingData.arcAtBundle b i w = atThin t i w := by
    rw [hb]
    change (((t.1.1.1, (t.1.1.2.1 + X.packingData.offset t.1.1.1 - X.packingData.offset t.1.1.1, t.1.1.2.2)), i),
        w, (bitWordFinEquiv a).symm (bitWordFinEquiv a t.2.2)) = atThin t i w
    rw [add_sub_cancel_right, Equiv.symm_apply_apply]
    rfl
  have htotal : sTotal D u ℓ (mapWire (P1P7.addr X) t) (off (P1P7.addr X t.1.1.1)) = X.packingData.bundleWidth X.packingWidth b := by
    rw [P1P7.bundleWidth_sum X, hb]
    unfold sTotal
    rw [hoff]
    refine Finset.sum_congr rfl fun uh _ => ?_
    let z : Wire X.Base a g :=
      (((t.1.1.1, (t.1.1.2.1 + X.packingData.offset t.1.1.1, t.1.1.2.2)), bitWordFinEquiv a t.2.2), uh)
    change (if sThick D u ℓ (mapWire (P1P7.addr X) z) ∧ sThick D u ℓ (sOut a g D u ℓ (mapWire (P1P7.addr X) z))
      then sWidth D u ℓ (mapWire (P1P7.addr X) z) else 0) =
      if X.packingData.thick (sourcePosition z) ∧ X.packingData.thick (sourcePosition (X.packingData.actual z)) then X.packingWidth z else 0
    rw [sOut_eq hpan z, sWidth_eq hpan z]
    simp only [sThick_iff hcol]
  have hrank : sRank D u ℓ (mapWire (P1P7.addr X) t) (mapWire (P1P7.addr X) m.val) =
      (X.shrinkNumber b ⟨m, rfl⟩ : ℕ) := by
    rw [P1P7.bundle_rank X b ⟨m, rfl⟩]
    change _ = Fintype.card {y : X.packingData.MotifFiber b // P1P7.arcKey X y.1.val < P1P7.arcKey X m.val}
    rw [rank_sum X.packingData b (P1P7.arcKey X) (P1P7.arcKey X m.val)]
    simp only [hat]
    unfold sRank
    apply congrArg₂ Nat.add
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => ?_
      change (if ¬ sThick D u ℓ (mapWire (P1P7.addr X) (atThin t i w)) ∧
          sKey (mapWire (P1P7.addr X) (atThin t i w)) < sKey (mapWire (P1P7.addr X) m.val) then 1 else 0) = _
      simp only [sThick_iff hcol, sKey_eq]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => ?_
      change (if sThick D u ℓ (sIn a g D u ℓ (mapWire (P1P7.addr X) (atThin t i w))) ∧
          ¬ sThick D u ℓ (mapWire (P1P7.addr X) (atThin t i w)) ∧
          sKey (sIn a g D u ℓ (mapWire (P1P7.addr X) (atThin t i w))) < sKey (mapWire (P1P7.addr X) m.val) then 1 else 0) = _
      simp only [sIn_eq hpan, sThick_iff hcol, sKey_eq]
  unfold widthsAt
  dsimp only
  rw [hthin]
  change demandWidths
      (if sRank D u ℓ (mapWire (P1P7.addr X) t) (mapWire (P1P7.addr X) m.val) <
          sTotal D u ℓ (mapWire (P1P7.addr X) t) (off (P1P7.addr X t.1.1.1)) % _ then _ else _)
      (sWidth D u ℓ (mapWire (P1P7.addr X) m.val)) = _
  have he : (mapWire (P1P7.addr X) t).1.1.1 = P1P7.addr X t.1.1.1 := rfl
  simp only [he, htotal, hrank, sWidth_eq hpan]
  rfl

end Widths

end P1SolGreedy.SolDemand

namespace P1SolGreedy

open SolDemand

/-- Demand widths reconstructed from the complete stored panels and colours. -/
def DW {a g : ℕ} {D : Dims} (u : List Bool) (ℓ Y key : ℕ) : Bool → ℕ :=
  widthsAt D u ℓ (fun Z => offsets a g D u ℓ (Z + 1) Z) (wireOf a g Y key)

/-- Radius-two implementation using the tag offset certified by the preceding C6 family. -/
def DWLocal {a g : ℕ} {D : Dims} (u : List Bool) (ℓ Y key : ℕ) : Bool → ℕ :=
  widthsAt D u ℓ (fun Z => P1ChkFinal.bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ Z))
    (wireOf a g Y key)

attribute [local instance] P1P7.instDecEqBase

theorem dw_correct_from_panels {a g : ℕ} (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
    (hm : P1ChkGreedy.IsMotif X (packingArcEquiv X.Base a g ((y, k), w))) :
    P1SolGreedy.DW (a := a) (g := g) (D := D) u ℓ (P1P7.addr X y) (P1ChkGreedy.keyOf a g k w) =
      P1ChkGreedy.demandW X ⟨_, hm⟩ := by
  unfold DW
  rw [wireOf_keyOf, ← mapWire_pack (P1P7.addr X) (y, k) w]
  refine widthsAt_correct hpan hcol _ (fun z => ?_) ⟨_, hm⟩
  rw [offsets_eq (recTrue_of_panelMatch hpan), ite_eq_left (Nat.lt_succ_self _)]

theorem dwLocal_correct {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hcol : ∀ z, rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (hoff : ∀ z, rdOffset D u ℓ (P1P7.addr X z) = P1ChkFinal.bwNum (X.packingData.offset z))
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
    (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))) :
    DWLocal (a := a) (g := g) (D := D) u ℓ (P1P7.addr X y) (keyOf a g k w) = demandW X ⟨_, hm⟩ := by
  unfold DWLocal
  rw [wireOf_keyOf, ← mapWire_pack (P1P7.addr X) (y, k) w]
  exact widthsAt_correct hpan hcol _ (fun z => (hoff z).symm ▸ P1ChkFinal.bwOf_bwNum _) ⟨_, hm⟩

#print axioms dw_correct_from_panels
#print axioms dwLocal_correct

end P1SolGreedy
