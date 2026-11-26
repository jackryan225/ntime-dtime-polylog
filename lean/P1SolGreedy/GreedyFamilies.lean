import P1SolGreedy.DemandWidthCore

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1Wit P1ChkGreedy

namespace P1SolGreedy

open SolDemand

/-- Number of outgoing wire keys at one base at level `ℓ`. -/
def termStride (ag : ℕ → ℕ × ℕ) (ℓ : ℕ) : ℕ :=
  let (a, g) := ag ℓ
  2 ^ packingLaneBits a g * 2 ^ a

theorem termStride_pos (ag : ℕ → ℕ × ℕ) (ℓ : ℕ) : 0 < termStride ag ℓ :=
  Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)

/-- Use the same index validity test as for bases, with one entry per term slot. -/
def termDims (D : Dims) (ag : ℕ → ℕ × ℕ) : Dims :=
  { D with lv := fun ℓ => { D.lv ℓ with bases := (D.lv ℓ).bases * termStride ag ℓ } }

def cntTerm (D : Dims) (ag : ℕ → ℕ × ℕ) : ℕ := cntBase (termDims D ag)

def encTermIdx (D : Dims) (ag : ℕ → ℕ × ℕ) (ℓ Y key : ℕ) : ℕ :=
  encIdx D ℓ (key + termStride ag ℓ * Y)

section Families

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- The C7 term check at a numeric key in the level's term slot. -/
def C7key (a g : ℕ) (D : Dims) (u : List Bool) (ℓ Y key : ℕ) : Prop :=
  let k : Fin (2 ^ a) := ⟨key % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩
  C7at a g D u ℓ B (DWLocal (a := a) (g := g) (D := D))
    Y k (laneWord a g (key / (2 ^ a)))

/-- D5 family 6 is C7, indexed by level, base address and outgoing wire key. -/
def C7fam (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ) : Prop :=
  let D := Dn x.length
  let ℓ := i % 2 ^ levBits D
  let j := i / 2 ^ levBits D
  let stride := termStride (ag x.length) ℓ
  ShrinkIdx (termDims D (ag x.length)) i →
    C7key B (ag x.length ℓ).1 (ag x.length ℓ).2 D u ℓ (j / stride) (j % stride)

/-- D5 family 7 is the two C8 energy recurrence checks at a shrinking base. -/
def C8fam (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) (i : ℕ) : Prop :=
  let D := Dn x.length
  let ℓ := i % 2 ^ levBits D
  let a := (ag x.length ℓ).1
  let g := (ag x.length ℓ).2
  ShrinkIdx D i → C8chk a g D u ℓ B (DWLocal (a := a) (g := g) (D := D)) (i / 2 ^ levBits D)

theorem C7fam_out (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {i : ℕ}
    (hi : cntTerm (Dn x.length) (ag x.length) ≤ i) : C7fam B Dn ag x u i :=
  fun h => absurd h (not_shrinkIdx_of_ge _ hi)

theorem C8fam_out (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {i : ℕ}
    (hi : cntBase (Dn x.length) ≤ i) : C8fam B Dn ag x u i :=
  fun h => absurd h (not_shrinkIdx_of_ge _ hi)

theorem C7fam_key (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ Y key : ℕ}
    (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = true)
    (hY : Y < ((Dn x.length).lv ℓ).bases) (hk : key < termStride (ag x.length) ℓ) :
    C7fam B Dn ag x u (encTermIdx (Dn x.length) (ag x.length) ℓ Y key) ↔
      C7key B (ag x.length ℓ).1 (ag x.length ℓ).2 (Dn x.length) u ℓ Y key := by
  let D := Dn x.length
  let s := termStride (ag x.length) ℓ
  have hsd : 0 < s := termStride_pos _ _
  have hmod : (key + s * Y) % s = key := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hdiv : (key + s * Y) / s = Y := by
    rw [Nat.add_mul_div_left _ _ hsd, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hi : key + s * Y < (D.lv ℓ).bases * s := by
    calc
      key + s * Y < s + s * Y := Nat.add_lt_add_right hk _
      _ = (Y + 1) * s := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Y s, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hY)
  change (ShrinkIdx (termDims D (ag x.length)) (encIdx D ℓ (key + s * Y)) → _) ↔ _
  have hsidx : ShrinkIdx (termDims D (ag x.length)) (encIdx D ℓ (key + s * Y)) := by
    unfold ShrinkIdx
    change _ % 2 ^ levBits D ≤ D.top ∧
      (D.lv (_ % 2 ^ levBits D)).shrink = true ∧
      _ / 2 ^ levBits D < (D.lv (_ % 2 ^ levBits D)).bases *
        termStride (ag x.length) (_ % 2 ^ levBits D)
    rw [encIdx_mod D hℓ, encIdx_div D hℓ]
    exact ⟨hℓ, hs, hi⟩
  unfold encTermIdx
  rw [encIdx_mod _ hℓ, encIdx_div _ hℓ]
  rw [show termStride (ag x.length) ℓ = s from rfl, hmod, hdiv]
  exact ⟨fun h => h hsidx, fun h _ => h⟩

theorem C8fam_level (Dn : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (x u : List Bool) {ℓ : ℕ}
    (hℓ : ℓ ≤ (Dn x.length).top) (hs : ((Dn x.length).lv ℓ).shrink = true) (Y : ℕ)
    (hY : Y < ((Dn x.length).lv ℓ).bases) :
    C8fam B Dn ag x u (encIdx (Dn x.length) ℓ Y) ↔
      C8chk (ag x.length ℓ).1 (ag x.length ℓ).2 (Dn x.length) u ℓ B
        (DWLocal (a := (ag x.length ℓ).1) (g := (ag x.length ℓ).2) (D := Dn x.length)) Y := by
  unfold C8fam ShrinkIdx
  dsimp only
  rw [encIdx_mod _ hℓ, encIdx_div _ hℓ]
  exact ⟨fun h => h ⟨hℓ, hs, hY⟩, fun h _ => h⟩

section Stage

variable {a g : ℕ} {D : Dims} {u : List Bool} {ℓ : ℕ} {X : State a (packingLaneBits a g)}
variable (hpan : ∀ z : X.Base, P1ChkFinal.PanelMatch D u ℓ (P1P7.addr X z) (P1P7.panel X z))
variable (hcol : ∀ z, rdColour D u ℓ (P1P7.addr X z) = (X.packingData.color z : ℕ))
variable (h6 : ∀ z, C6chk a g D u ℓ (P1P7.addr X z))

include hpan h6 in
theorem offset_of_C6 (z : X.Base) :
    rdOffset D u ℓ (P1P7.addr X z) = P1ChkFinal.bwNum (X.packingData.offset z) :=
  (C6u_iff D u ℓ X).mp (fun v => (C6chk_iff (recTrue_of_panelMatch hpan) v).mp (h6 v)) z

include hpan hcol h6 in
theorem C7at_local_iff (y : X.Base) (k : Fin (2 ^ a)) (w : BitWord (packingLaneBits a g)) :
    C7at a g D u ℓ B (DWLocal (a := a) (g := g) (D := D)) (P1P7.addr X y) k w ↔
      C7u B D u ℓ X (packingArcEquiv X.Base a g ((y, k), w)) :=
  C7at_iff B _ (recTrue_of_panelMatch hpan) hcol
    (dwLocal_correct D u ℓ X hpan hcol (offset_of_C6 hpan h6)) y k w

include hpan hcol h6 in
theorem C8chk_local_iff (y : X.Base) :
    C8chk a g D u ℓ B (DWLocal (a := a) (g := g) (D := D)) (P1P7.addr X y) ↔
      C8u B D u ℓ X y :=
  C8chk_iff B _ (recTrue_of_panelMatch hpan) hcol
    (dwLocal_correct D u ℓ X hpan hcol (offset_of_C6 hpan h6)) y

end Stage

end Families

#print axioms C7fam_key
#print axioms C8fam_level
#print axioms C7at_local_iff
#print axioms C8chk_local_iff

end P1SolGreedy
