import P1SolGreedy.GreedyFamilies

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1Wit P1ChkGreedy

namespace P1SolGreedy

set_option maxRecDepth 4096

open SolDemand

section Earlier

variable {a g : ℕ} {D : Dims} {ℓ : ℕ} {X : State a (packingLaneBits a g)}

theorem addr_lt_bases (hN : (D.lv ℓ).bases = Fintype.card X.Base) (y : X.Base) :
    P1P7.addr X y < (D.lv ℓ).bases := by
  rw [hN]
  exact (X.baseIndex y).isLt

theorem colours_of_C5fam (Dn : ℕ → Dims) (x u : List Bool) (hℓ : ℓ ≤ (Dn x.length).top)
    (hS : ((Dn x.length).lv ℓ).shrink = true)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base)
    (hslots : ((Dn x.length).lv ℓ).slots = 2 ^ a)
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC5 : ∀ Y < ((Dn x.length).lv ℓ).bases, C5fam Dn x u (encIdx (Dn x.length) ℓ Y)) :
    ∀ z, rdColour (Dn x.length) u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ) := by
  apply (C5u_iff (Dn x.length) u ℓ X).mp
  intro y
  apply (C5chk_iff' (recTrue_of_panelMatch hpan) hslots y).mp
  exact (C5fam_level Dn x u hℓ hS).mp hC5 _ (addr_lt_bases hN y)

theorem C6checks_of_C6fam (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool)
    (hℓ : ℓ ≤ (Dn x.length).top) (hS : ((Dn x.length).lv ℓ).shrink = true)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hag : ag x.length ℓ = (a, g))
    (hC6 : ∀ Y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ Y)) :
    ∀ z : X.Base, C6chk a g (Dn x.length) u ℓ (P1P7.addr X z) := by
  have H := (C6fam_level Dn ag x u hℓ hS).mp hC6
  rw [hag] at H
  exact fun y => H _ (addr_lt_bases hN y)

theorem offsets_of_C6fam (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool)
    (hℓ : ℓ ≤ (Dn x.length).top) (hS : ((Dn x.length).lv ℓ).shrink = true)
    (hN : ((Dn x.length).lv ℓ).bases = Fintype.card X.Base) (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch (Dn x.length) u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC6 : ∀ Y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ Y)) :
    ∀ z, rdOffset (Dn x.length) u ℓ (P1P7.addr X z) = P1ChkFinal.bwNum (X.packingData.offset z) :=
  offset_of_C6 hpan (C6checks_of_C6fam Dn ag x u hℓ hS hN hag hC6)

end Earlier

section Terms

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem keyOf_lt {a g : ℕ} (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    keyOf a g k w < 2 ^ packingLaneBits a g * 2 ^ a := by
  let j := (bitWordFinEquiv (packingLaneBits a g) w : ℕ)
  change j * 2 ^ a + (k : ℕ) < _
  calc
    _ < j * 2 ^ a + 2 ^ a := Nat.add_lt_add_left k.isLt _
    _ = (j + 1) * 2 ^ a := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (bitWordFinEquiv (packingLaneBits a g) w).isLt

theorem C7key_keyOf {a g : ℕ} (D : Dims) (u : List Bool) (ℓ Y : ℕ)
    (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    C7key B a g D u ℓ Y (keyOf a g k w) ↔
      C7at a g D u ℓ B (@DWLocal a g D) Y k w := by
  have he := (packingArcEquiv ℕ a g).injective (wireOf_keyOf Y k w)
  have hk := congrArg (fun p : (ℕ × Fin (2 ^ a)) × BitWord (packingLaneBits a g) => p.1.2) he
  have hw := congrArg Prod.snd he
  change (⟨keyOf a g k w % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩ : Fin (2 ^ a)) = k at hk
  change laneWord a g (keyOf a g k w / (2 ^ a)) = w at hw
  simp only [C7key, hk, hw]

section Certificates

attribute [local instance] P1P7.instDecEqBase

variable {a g : ℕ} (D : Dims) (u : List Bool) (ℓ : ℕ) (X : State a (packingLaneBits a g))

theorem C7u_certifies :
    (∀ e : OldArc X, C7u B D u ℓ X e) ↔
      ∃ s : X.ShrinkSelection B, ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e) := by
  constructor
  · intro h
    have H (e : OldArc X) := (C7u_iff B D u ℓ X e).mp (h e)
    obtain ⟨s, hs, _⟩ := C7_unique B X (fun e => (H e).1)
    exact ⟨s, fun e => hs ▸ (H e).2⟩
  · rintro ⟨s, h⟩ e
    have hs : tmOf D u ℓ X = trueTerms B X s :=
      funext fun t => tmOf_of_raw D u ℓ X t _ (h t)
    refine (C7u_iff B D u ℓ X e).mpr ⟨?_, ?_⟩
    · rw [hs]
      exact C7_true B X s e
    · rw [hs]
      exact h e

theorem C8u_certifies (s : X.ShrinkSelection B)
    (hs : ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e)) :
    (∀ y : X.Base, C8u B D u ℓ X y) ↔
      ∀ y l, rdEnergy D u ℓ (P1P7.addr X y) (eCode l) = truePrefix X (termW B X s) y l := by
  have htm : tmOf D u ℓ X = trueTerms B X s :=
    funext fun e => tmOf_of_raw D u ℓ X e _ (hs e)
  simp only [C8u, htm, storedWidths_trueTerms]
  exact (C8_iff X _ _).trans ⟨fun h y l => congrFun (congrFun h y) l, fun h => funext fun y => funext (h y)⟩

end Certificates

section Correct

variable {a g ℓ : ℕ} {X : State a (packingLaneBits a g)}
variable (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool)

local notation "D" => (Dn x.length)

set_option maxHeartbeats 1000000 in
theorem C7fam_stage
    (hℓ : ℓ ≤ (D).top) (hS : ((D).lv ℓ).shrink = true)
    (hN : ((D).lv ℓ).bases = Fintype.card X.Base) (hslots : ((D).lv ℓ).slots = 2 ^ a)
    (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC5 : ∀ Y < ((D).lv ℓ).bases, C5fam Dn x u (encIdx D ℓ Y))
    (hC6 : ∀ Y < ((D).lv ℓ).bases, C6fam Dn ag x u (encIdx D ℓ Y)) :
    (∀ Y < ((D).lv ℓ).bases, ∀ key < termStride (ag x.length) ℓ,
      C7fam B Dn ag x u (encTermIdx D (ag x.length) ℓ Y key)) ↔
      ∀ e : OldArc X, C7u B D u ℓ X e := by
  have hc := colours_of_C5fam Dn x u hℓ hS hN hslots hpan hC5
  have h6 := C6checks_of_C6fam Dn ag x u hℓ hS hN hag hC6
  have H := C7at_local_iff B hpan hc h6
  have W {Y key : ℕ} (hy : Y < ((D).lv ℓ).bases) (hk : key < termStride (ag x.length) ℓ) :
      C7fam B Dn ag x u (encTermIdx D (ag x.length) ℓ Y key) ↔ C7key B a g D u ℓ Y key := by
    simpa only [hag] using C7fam_key B Dn ag x u hℓ hS hy hk
  constructor
  · intro h e
    obtain ⟨⟨⟨y, k⟩, w⟩, rfl⟩ := (packingArcEquiv X.Base a g).surjective e
    have hy := addr_lt_bases hN y
    have hk : keyOf a g k w < termStride (ag x.length) ℓ := by
      unfold termStride
      rw [hag]
      exact keyOf_lt k w
    exact (H y k w).mp ((C7key_keyOf B D u ℓ (P1P7.addr X y) k w).mp
      ((W hy hk).mp (h _ hy _ hk)))
  · intro h Y hY key hk
    obtain ⟨y, rfl⟩ := P1ChkFinal.exists_addr_eq X (hY.trans_le hN.le)
    refine (W hY hk).mpr ?_
    let k : Fin (2 ^ a) := ⟨key % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩
    let w := laneWord a g (key / (2 ^ a))
    exact (H y k w).mpr (h (packingArcEquiv X.Base a g ((y, k), w)))

set_option maxHeartbeats 1000000 in
theorem C8fam_stage
    (hℓ : ℓ ≤ (D).top) (hS : ((D).lv ℓ).shrink = true)
    (hN : ((D).lv ℓ).bases = Fintype.card X.Base) (hslots : ((D).lv ℓ).slots = 2 ^ a)
    (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC5 : ∀ Y < ((D).lv ℓ).bases, C5fam Dn x u (encIdx D ℓ Y))
    (hC6 : ∀ Y < ((D).lv ℓ).bases, C6fam Dn ag x u (encIdx D ℓ Y)) :
    (∀ Y < ((D).lv ℓ).bases, C8fam B Dn ag x u (encIdx D ℓ Y)) ↔
      ∀ y : X.Base, C8u B D u ℓ X y := by
  have hc := colours_of_C5fam Dn x u hℓ hS hN hslots hpan hC5
  have h6 := C6checks_of_C6fam Dn ag x u hℓ hS hN hag hC6
  have H := C8chk_local_iff B hpan hc h6
  have W {Y : ℕ} (hy : Y < ((D).lv ℓ).bases) :
      C8fam B Dn ag x u (encIdx D ℓ Y) ↔
        C8chk a g D u ℓ B (@DWLocal a g D) Y := by
    simpa only [hag] using C8fam_level B Dn ag x u hℓ hS Y hy
  constructor
  · intro h y
    have hy := addr_lt_bases hN y
    exact (H y).mp ((W hy).mp (h _ hy))
  · intro h Y hY
    obtain ⟨y, rfl⟩ := P1ChkFinal.exists_addr_eq X (hY.trans_le hN.le)
    exact (W hY).mpr ((H y).mpr (h y))

attribute [local instance] P1P7.instDecEqBase

theorem C7fam_certifies
    (hℓ : ℓ ≤ (D).top) (hS : ((D).lv ℓ).shrink = true)
    (hN : ((D).lv ℓ).bases = Fintype.card X.Base) (hslots : ((D).lv ℓ).slots = 2 ^ a)
    (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC5 : ∀ Y < ((D).lv ℓ).bases, C5fam Dn x u (encIdx D ℓ Y))
    (hC6 : ∀ Y < ((D).lv ℓ).bases, C6fam Dn ag x u (encIdx D ℓ Y)) :
    (∀ Y < ((D).lv ℓ).bases, ∀ key < termStride (ag x.length) ℓ,
      C7fam B Dn ag x u (encTermIdx D (ag x.length) ℓ Y key)) ↔
      ∃ s : X.ShrinkSelection B, ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e) :=
  (C7fam_stage B Dn ag x u hℓ hS hN hslots hag hpan hC5 hC6).trans (C7u_certifies B D u ℓ X)

theorem C8fam_certifies
    (hℓ : ℓ ≤ (D).top) (hS : ((D).lv ℓ).shrink = true)
    (hN : ((D).lv ℓ).bases = Fintype.card X.Base) (hslots : ((D).lv ℓ).slots = 2 ^ a)
    (hag : ag x.length ℓ = (a, g))
    (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
    (hC5 : ∀ Y < ((D).lv ℓ).bases, C5fam Dn x u (encIdx D ℓ Y))
    (hC6 : ∀ Y < ((D).lv ℓ).bases, C6fam Dn ag x u (encIdx D ℓ Y))
    (s : X.ShrinkSelection B)
    (hterm : ∀ e, rawOf D u ℓ X e = termCode (trueTerms B X s e)) :
    (∀ Y < ((D).lv ℓ).bases, C8fam B Dn ag x u (encIdx D ℓ Y)) ↔
      ∀ y l, rdEnergy D u ℓ (P1P7.addr X y) (eCode l) = truePrefix X (termW B X s) y l :=
  (C8fam_stage B Dn ag x u hℓ hS hN hslots hag hpan hC5 hC6).trans (C8u_certifies B D u ℓ X s hterm)

end Correct

end Terms

#print axioms colours_of_C5fam
#print axioms offsets_of_C6fam
#print axioms C7fam_stage
#print axioms C8fam_stage
#print axioms C7fam_certifies
#print axioms C8fam_certifies

end P1SolGreedy
