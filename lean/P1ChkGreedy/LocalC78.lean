import P1ChkGreedy.LocalC6

/-!
# P1ChkGreedy.LocalC78: checks C7 and C8 on the STORED fields, with the demand widths as a parameter

Lane P1-lean-W2-chkgreedy. A term slot of a shrinking level is keyed by (base address `Y`, out-slot `k`, lane word
`w`), key number `keyOf k w = laneNumber w * 2^a + k` (as `arcKey` of `P1ChkGreedy.Bind`). On the stored fields:
* the motif test `IsMotifAt` (OpenAI `PackingData.Motif`: the wire is not thick at both ends) reads the stored colour
  of `Y`, the stored out-neighbour address and colour, and the colour-bit part of the stored displacement;
* the DEMAND WIDTHS are given by a function `DW u ℓ Y key : Bool → ℕ` of the stored fields (parameter). Its
  agreement with OpenAI's `demandW X m` (= `shrinkDemandWidths X.shrinkNumber X.packingWidth m`) is the named
  hypothesis `hdw` of the links. Writing `DW` (the AB width needs the bundle numbering, radius 2) is OPEN.
LINKS (stage step; base records true = `RecTrue`, colours true = `hcol`, `hdw`):
`C7at_iff`: `C7at … (addr y) k w ↔ C7u B D u ℓ X (packingArcEquiv _ a g ((y, k), w))`;
`C8chk_iff`: `C8chk … (addr y) ↔ C8u B D u ℓ X y` (the energy sum over stored keys equals `energyAt`).
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

noncomputable section

/-! ## Stored-field definitions -/

section Stored

variable (a g : ℕ) (D : P1Wit.Dims) (u : List Bool) (ℓ : ℕ)

/-- A stored lane number (or displacement number), decoded into a lane word. -/
def laneWord (v : ℕ) : BitWord (packingLaneBits a g) := (bitWordFinEquiv _).symm (finOr0 _ v)

/-- The stored colour of address `Z`, decoded. -/
def colS (Z : ℕ) : Fin (2 * 2 ^ a + 1) := finOr0 _ (P1Wit.rdColour D u ℓ Z)

/-- **Motif test on the stored fields** for the old wire at (address `Y`, out-slot `k`, lane word `w`): not thick
at both ends (thick = the colour-bit word of the position has a `1` at the colour of its base). -/
def IsMotifAt (Y : ℕ) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) : Prop :=
  ¬ ((packingFields a g w).1 (colS a D u ℓ Y) = 1 ∧
    ((packingFields a g w).1 + (packingFields a g (laneWord a g (P1Wit.rdOutDisp D u ℓ Y k))).1)
      (colS a D u ℓ (P1Wit.rdOutAddr D u ℓ Y k)) = 1)

instance (Y : ℕ) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) : Decidable (IsMotifAt a g D u ℓ Y k w) := by
  unfold IsMotifAt; infer_instance

/-- Key of the term slot of (out-slot `k`, lane word `w`) at its base. -/
def keyOf (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) : ℕ :=
  (bitWordFinEquiv (packingLaneBits a g) w : ℕ) * 2 ^ a + k

/-- The stored term slot at (address `Y`, key): (flag, the eight numbers). -/
def rawS (Y key : ℕ) : ℕ × (Bool × Fin 4 → ℕ) :=
  (P1Wit.rdTerms D u ℓ Y key 0, fun p => P1Wit.rdTerms D u ℓ Y key (1 + termIdx p))

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (DW : List Bool → ℕ → ℕ → ℕ → Bool → ℕ)

/-- **C7 on the stored fields** at (address `Y`, out-slot `k`, lane word `w`). -/
def C7at (Y : ℕ) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) : Prop :=
  if IsMotifAt a g D u ℓ Y k w then
    (rawS D u ℓ Y (keyOf a g k w)).1 = 1 ∧
      (rawS D u ℓ Y (keyOf a g k w)).2 ∈ MotifConversion.outerIndices B (DW u ℓ Y (keyOf a g k w))
  else rawS D u ℓ Y (keyOf a g k w) = (0, fun _ => 0)

/-- Stored term widths (supply widths of the stored index; `0` for an empty slot). -/
def WS (Y : ℕ) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) (l : Bool) (e : Fin 4) : ℕ :=
  if (rawS D u ℓ Y (keyOf a g k w)).1 = 1 then
    MotifConversion.supplyWidths B (DW u ℓ Y (keyOf a g k w)) (rawS D u ℓ Y (keyOf a g k w)).2 (l, e)
  else 0

/-- The energy of address `Y` in group `l`, from the stored fields. -/
def energyS (Y : ℕ) (l : Bool) : ℕ :=
  ∑ p : Fin (2 ^ a) × BitWord (packingLaneBits a g),
    if IsMotifAt a g D u ℓ Y p.1 p.2 then
      ∑ e, P1P7.layoutCoeff e * WS a g D u ℓ B DW Y p.1 p.2 l e ^ 2
    else 0

/-- **C8 on the stored fields** at address `Y`. -/
def C8chk (Y : ℕ) : Prop :=
  ∀ l : Bool, P1Wit.rdEnergy D u ℓ Y (eCode l) =
    (if 0 < Y then P1Wit.rdEnergy D u ℓ (Y - 1) (eCode l) else 0) + energyS a g D u ℓ B DW Y l

end Stored

/-! ## Links -/

section Links

attribute [local instance] P1P7.instDecEqBase

variable {a g : ℕ} {D : P1Wit.Dims} {u : List Bool} {ℓ : ℕ}
variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (DW : List Bool → ℕ → ℕ → ℕ → Bool → ℕ)

theorem rawOf_eq (X : State a (packingLaneBits a g)) (y : X.Base) (k : Fin (2 ^ a))
    (w : BitWord (packingLaneBits a g)) :
    rawOf D u ℓ X (packingArcEquiv X.Base a g ((y, k), w)) = rawS D u ℓ (P1P7.addr X y) (keyOf a g k w) := by
  simp only [rawOf, arcKey, rawS, keyOf, Equiv.symm_apply_apply]

/-- Under `RecTrue` and true stored colours, the stored motif test is OpenAI's. -/
theorem isMotifAt_iff {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X)
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    IsMotifAt a g D u ℓ (P1P7.addr X y) k w ↔ IsMotif X (packingArcEquiv X.Base a g ((y, k), w)) := by
  have hc : ∀ z, colS a D u ℓ (P1P7.addr X z) = X.packingData.color z := fun z => by
    unfold colS
    rw [hcol z]
    exact ((finOr0_eq_iff _ _).mpr rfl).2
  have hz : P1Wit.rdOutAddr D u ℓ (P1P7.addr X y) k = P1P7.addr X (X.slots.base.target (y, k)).1 :=
    (h y k).1
  have hd : laneWord a g (P1Wit.rdOutDisp D u ℓ (P1P7.addr X y) k) = X.slots.displacement (y, k) := by
    unfold laneWord
    rw [(h y k).2.2.1]
    have h0 : finOr0 _ (bitWordFinEquiv _ (P1P7.outNbr X y k).2 : ℕ) = bitWordFinEquiv _ (P1P7.outNbr X y k).2 :=
      ((finOr0_eq_iff _ _).mpr rfl).2
    rw [h0, Equiv.symm_apply_apply]
    rfl
  unfold IsMotifAt
  rw [hz, hd, hc, hc]
  exact Iff.rfl

/-- **Link C7.** -/
theorem C7at_iff {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X)
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (hdw : ∀ (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
      (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))),
      DW u ℓ (P1P7.addr X y) (keyOf a g k w) = demandW X ⟨_, hm⟩)
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    C7at a g D u ℓ B DW (P1P7.addr X y) k w ↔ C7u B D u ℓ X (packingArcEquiv X.Base a g ((y, k), w)) := by
  unfold C7at C7u
  rw [rawOf_eq]
  by_cases hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))
  · rw [if_pos ((isMotifAt_iff h hcol y k w).mpr hm), dif_pos hm, hdw y k w hm]
  · rw [if_neg (fun h' => hm ((isMotifAt_iff h hcol y k w).mp h')), dif_neg hm]

theorem storedWidths_eq (X : State a (packingLaneBits a g))
    (hdw : ∀ (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
      (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))),
      DW u ℓ (P1P7.addr X y) (keyOf a g k w) = demandW X ⟨_, hm⟩)
    (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
    (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))) (l : Bool) (e : Fin 4) :
    storedWidths B X (tmOf D u ℓ X) ⟨_, hm⟩ l e = WS a g D u ℓ B DW (P1P7.addr X y) k w l e := by
  unfold storedWidths tmOf WS
  simp only [rawOf_eq]
  by_cases hf : (rawS D u ℓ (P1P7.addr X y) (keyOf a g k w)).1 = 1
  · simp only [if_pos hf, Option.elim_some, hdw y k w hm]
  · simp only [if_neg hf, Option.elim_none]

/-- The stored energy of `addr y` is OpenAI's grouped energy `energyAt` of the stored widths. -/
theorem energyS_eq {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X)
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (hdw : ∀ (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
      (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))),
      DW u ℓ (P1P7.addr X y) (keyOf a g k w) = demandW X ⟨_, hm⟩)
    (y : X.Base) (l : Bool) :
    energyS a g D u ℓ B DW (P1P7.addr X y) l = energyAt X (storedWidths B X (tmOf D u ℓ X)) y l := by
  have hfact : ∀ m : X.packingData.Motif, motifBase X m = y →
      packingArcEquiv X.Base a g ((y, ((packingArcEquiv X.Base a g).symm m.val).1.2),
        ((packingArcEquiv X.Base a g).symm m.val).2) = m.val := by
    intro m hm
    have h1 : ((packingArcEquiv X.Base a g).symm m.val).1.1 = y := hm
    rw [← h1]
    exact Equiv.apply_symm_apply _ _
  unfold energyS energyAt
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun p hp => (⟨packingArcEquiv X.Base a g ((y, p.1), p.2),
      (isMotifAt_iff h hcol y p.1 p.2).mp (Finset.mem_filter.mp hp).2⟩ : X.packingData.Motif))
    (fun m _ => (((packingArcEquiv X.Base a g).symm m.val).1.2, ((packingArcEquiv X.Base a g).symm m.val).2))
    ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro m hm
    have hm' : motifBase X m = y := (Finset.mem_filter.mp hm).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show IsMotifAt a g D u ℓ (P1P7.addr X y) ((packingArcEquiv X.Base a g).symm m.val).1.2
      ((packingArcEquiv X.Base a g).symm m.val).2
    rw [isMotifAt_iff h hcol, hfact m hm']
    exact m.property
  · intro p _
    simp
  · intro m hm
    exact Subtype.ext (hfact m (Finset.mem_filter.mp hm).2)
  · intro p hp
    apply Finset.sum_congr rfl
    intro e _
    rw [storedWidths_eq B DW X hdw y p.1 p.2]

/-- **Link C8.** -/
theorem C8chk_iff {X : State a (packingLaneBits a g)} (h : RecTrue D u ℓ X)
    (hcol : ∀ z, P1Wit.rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
    (hdw : ∀ (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g))
      (hm : IsMotif X (packingArcEquiv X.Base a g ((y, k), w))),
      DW u ℓ (P1P7.addr X y) (keyOf a g k w) = demandW X ⟨_, hm⟩)
    (y : X.Base) :
    C8chk a g D u ℓ B DW (P1P7.addr X y) ↔ C8u B D u ℓ X y := by
  unfold C8chk C8u C8 EOf
  have hp : P1P7.addr X (prevBase X y) = P1P7.addr X y - 1 := prevBase_index X y
  apply forall_congr'
  intro l
  rw [hp, energyS_eq B DW h hcol hdw y l]
  exact Iff.rfl

end Links

end

end P1ChkGreedy
