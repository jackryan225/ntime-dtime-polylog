import P1P7.KernelRes

/-!
# P7 kernel locality, layer 5: the AB bit correspondence (`demandBitEquiv`)

* `sortedThick_lt'`, `thick_rank`, `thick_rank_eq`: OpenAI's thick numbering of a bundle compares by the key
  (colour bits, slot label) (same proof as OpenAI's `sortedThick_lt`, CompressorRecordsBundleRank.lean:106, which is
  not in our build closure), and the ranks are transported.
* `orderedBits_transport`: a concatenation order is transported by a rank- and width-preserving map.
* `demandBit_tA`: the old thick wire and bit that `demandBitEquiv` assigns to bit `i` of the AB slice of a motif are
  transported to those of the partner motif.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.NetworkKernel


section Generic

theorem finSigma_congr {m : ℕ} (f f' : Fin m → ℕ) (h : f = f') (k k' : Fin m) (hk : k = k')
    (j : Fin (f k)) (j' : Fin (f' k')) (hj : (j : ℕ) = j') :
    (finSigmaFinEquiv (⟨k, j⟩ : (i : Fin m) × Fin (f i)) : ℕ) =
      (finSigmaFinEquiv (⟨k', j'⟩ : (i : Fin m) × Fin (f' i)) : ℕ) := by
  subst h
  subst hk
  obtain rfl : j = j' := Fin.ext hj
  rfl

theorem orderedBits_val {A : Type*} [Fintype A] {n : ℕ} (o : A ≃ Fin n) (w : A → ℕ) (x : A) (i : Fin (w x)) :
    (PackingData.orderedBits o w ⟨x, i⟩ : ℕ) =
      (finSigmaFinEquiv (⟨o x, Fin.cast (by simp) i⟩ : (k : Fin n) × Fin (w (o.symm k))) : ℕ) := rfl

/-- A concatenation order is transported by a map that keeps ranks and widths. -/
theorem orderedBits_transport {A A' : Type*} {iA : Fintype A} {iA' : Fintype A'} {n : ℕ} (o : A ≃ Fin n) (o' : A' ≃ Fin n)
    (w : A → ℕ) (w' : A' → ℕ) (τ : A → A') (hτ : ∀ x, o' (τ x) = o x) (hw : ∀ x, w' (τ x) = w x)
    (x : A) (i : Fin (w x)) (i' : Fin (w' (τ x))) (hi : (i : ℕ) = i') :
    (PackingData.orderedBits o' w' ⟨τ x, i'⟩ : ℕ) = PackingData.orderedBits o w ⟨x, i⟩ := by
  have hsymm : ∀ k, o'.symm k = τ (o.symm k) := fun k => by
    rw [Equiv.symm_apply_eq, hτ, Equiv.apply_symm_apply]
  rw [orderedBits_val, orderedBits_val]
  exact finSigma_congr _ _ (funext fun k => by rw [hsymm, hw]) _ _ (hτ x) _ _ (by simpa using hi.symm)

/-- The inverse of a transported concatenation order. -/
theorem orderedBits_symm_transport {A A' : Type*} {iA : Fintype A} {iA' : Fintype A'} {n : ℕ} (o : A ≃ Fin n)
    (o' : A' ≃ Fin n) (w : A → ℕ) (w' : A' → ℕ) (τ : A → A') (hτ : ∀ x, o' (τ x) = o x)
    (hw : ∀ x, w' (τ x) = w x) (N : Fin (∑ x, w x)) (N' : Fin (∑ x, w' x)) (hN : (N : ℕ) = N') :
    ((PackingData.orderedBits o' w').symm N').1 = τ ((PackingData.orderedBits o w).symm N).1 ∧
      (((PackingData.orderedBits o' w').symm N').2 : ℕ) = ((PackingData.orderedBits o w).symm N).2 := by
  set z := (PackingData.orderedBits o w).symm N with hz
  let i' : Fin (w' (τ z.1)) := ⟨z.2, (hw z.1).symm ▸ z.2.isLt⟩
  have key : PackingData.orderedBits o' w' ⟨τ z.1, i'⟩ = N' := by
    apply Fin.ext
    rw [orderedBits_transport o o' w w' τ hτ hw z.1 z.2 i' rfl, ← hN]
    change ((PackingData.orderedBits o w) ((PackingData.orderedBits o w).symm N) : ℕ) = N
    rw [Equiv.apply_symm_apply]
  rw [← key, Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

/-- `orderedBits_symm_transport` after a cast of the index type. -/
theorem orderedBits_symm_transport' {A A' : Type*} {iA : Fintype A} {iA' : Fintype A'} {n : ℕ} (o : A ≃ Fin n)
    (o' : A' ≃ Fin n) (w : A → ℕ) (w' : A' → ℕ) (τ : A → A') (hτ : ∀ x, o' (τ x) = o x)
    (hw : ∀ x, w' (τ x) = w x) {K K' : ℕ} (h1 : K = ∑ x, w x) (h2 : K' = ∑ x, w' x) (M : Fin K) (M' : Fin K')
    (hM : (M : ℕ) = M') :
    ((PackingData.orderedBits o' w').symm (finCongr h2 M')).1 =
        τ ((PackingData.orderedBits o w).symm (finCongr h1 M)).1 ∧
      (((PackingData.orderedBits o' w').symm (finCongr h2 M')).2 : ℕ) =
        ((PackingData.orderedBits o w).symm (finCongr h1 M)).2 :=
  orderedBits_symm_transport o o' w w' τ hτ hw _ _ hM

end Generic

section GenericDB

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
  (w : Arc V H Tag L d c → ℕ)

/-- `demandBitEquiv` by the offsets of the two concatenations (generic, so that no instance is re-synthesized). -/
theorem demandBitEquiv_eq_iff (b : Site V Tag L × Fin d) (y : P.MotifFiber b) (i : Fin (P.abWidth number w y.1))
    (t : P.ThickFiber b) (bit : Fin (w t.1.1)) :
    P.demandBitEquiv hc hd number order w b ⟨y, i⟩ = ⟨t, bit⟩ ↔
      (PackingData.orderedBits (number b) (fun m => P.abWidth number w m.1) ⟨y, i⟩ : ℕ) =
        (PackingData.orderedBits (order b) (fun a => w a.1.1) ⟨t, bit⟩ : ℕ) := by
  change (PackingData.orderedBits (order b) (fun a => w a.1.1)).symm
      (finCongr (P.sum_abWidth hc hd number w b)
        (PackingData.orderedBits (number b) (fun m => P.abWidth number w m.1) ⟨y, i⟩)) = ⟨t, bit⟩ ↔ _
  refine (Equiv.symm_apply_eq _).trans ?_
  exact ⟨fun h => by simpa using congrArg Fin.val h, fun h => Fin.ext (by simpa using h)⟩

end GenericDB

section Thick

variable {a g : ℕ}

/-- The key of OpenAI's thick numbering: colour bits and slot label of the old wire. -/
def tkey (X : State a (packingLaneBits a g)) (α : X.packingData.ThickWire) : ℕ :=
  (X.packingData.thickFiberIndex α.1.1 ⟨α, rfl⟩ : ℕ)

theorem sortedThick_lt' (X : State a (packingLaneBits a g))
    (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (x y : X.packingData.ThickFiber b) :
    X.shrinkOrder b x < X.shrinkOrder b y ↔ tkey X x.1 < tkey X y.1 := by
  let z : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a) := ((b.1.1, b.1.2.1, 0), b.2)
  let toZero (u : X.packingData.ThickFiber b) : X.packingData.ThickFiber z :=
    ⟨X.packingData.translateThickWire u.1 (-b.1.2.2), by
      change (translateSite u.1.1.1.1 _, u.1.1.1.2) = _
      simp [z, u.2, translateSite]⟩
  let := LinearOrder.lift' (X.packingData.thickFiberIndex z) (X.packingData.thickFiberIndex_injective z)
  let e := (Fintype.orderIsoFinOfCardEq (X.packingData.ThickFiber z)
    (X.packingData.card_thick_fiber (State.two_le_packingColors a) z)).symm
  change e (toZero x) < e (toZero y) ↔ _
  rw [e.lt_iff_lt]
  rfl

theorem thick_rank (X : State a (packingLaneBits a g))
    (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (x : X.packingData.ThickFiber b) :
    ((X.shrinkOrder b x : ℕ)) = Fintype.card {y : X.packingData.ThickFiber b // tkey X y.1 < tkey X x.1} :=
  rank_of_lt (X.shrinkOrder b) (fun y => tkey X y.1) (fun y x => sortedThick_lt' X b y x) x

theorem tkey_injective (X : State a (packingLaneBits a g))
    (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) :
    Function.Injective (fun y : X.packingData.ThickFiber b => tkey X y.1) := by
  intro y1 y2 h
  apply X.packingData.thickFiberIndex_injective b
  apply Fin.ext
  have e1 : (X.packingData.thickFiberIndex b y1 : ℕ) = tkey X y1.1 := by
    obtain ⟨y, rfl⟩ := y1; rfl
  have e2 : (X.packingData.thickFiberIndex b y2 : ℕ) = tkey X y2.1 := by
    obtain ⟨y, rfl⟩ := y2; rfl
  rw [e1, e2]
  exact h

variable {X X' : State a (packingLaneBits a g)}

/-- The ends of a thick wire of bundle `b` are the bundle's base and head. -/
theorem thick_ends (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (y : X.packingData.ThickFiber b)
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1) :
    EndsGood X X' y.1.1 := by
  obtain ⟨⟨α, hα⟩, rfl⟩ := y
  exact ⟨h1, h2⟩

/-- The partner thick wire. -/
noncomputable abbrev tThick (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (y : X.packingData.ThickFiber b) : X'.packingData.ThickFiber (tS X X' b.1, b.2) :=
  ⟨⟨tA X X' y.1.1, (thickThick_tA X X' y.1.1 (thick_ends b y h1 h2)).mpr y.1.2⟩, by
    obtain ⟨⟨α, hα⟩, rfl⟩ := y
    rfl⟩

theorem tkey_tThick (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (y : X.packingData.ThickFiber b) : tkey X' (tThick b h1 h2 y).1 = tkey X y.1 := rfl

theorem thick_rank_eq (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (y : X.packingData.ThickFiber b) :
    X'.shrinkOrder (tS X X' b.1, b.2) (tThick b h1 h2 y) = X.shrinkOrder b y := by
  apply Fin.ext
  rw [thick_rank, thick_rank, tkey_tThick]
  refine (card_lt_transport (fun z : X.packingData.ThickFiber b => tkey X z.1)
    (fun z : X'.packingData.ThickFiber (tS X X' b.1, b.2) => tkey X' z.1) (tkey_injective X b)
    (tkey_injective X' _) ?_ (fun z => ⟨tThick b h1 h2 z, tkey_tThick b h1 h2 z⟩) _).symm
  rw [X.packingData.card_thick_fiber (State.two_le_packingColors a),
    X'.packingData.card_thick_fiber (State.two_le_packingColors a)]

end Thick

section Bits

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}

/-- The partner of a motif of a bundle all of whose motifs have good ends. -/
noncomputable abbrev tMF (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val) (y : X.packingData.MotifFiber b) :
    X'.packingData.MotifFiber (tS X X' b.1, b.2) :=
  ⟨tM y.1 (hall y), by rw [bundle_tA y.1 (tM y.1 (hall y)) rfl (hall y), y.2]⟩

theorem fib_number_congr (X : State a (packingLaneBits a g)) {b1 b2 : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)}
    (h : b1 = b2) (y1 : X.packingData.MotifFiber b1) (y2 : X.packingData.MotifFiber b2) (hy : y1.1 = y2.1) :
    (X.shrinkNumber b1 y1 : ℕ) = X.shrinkNumber b2 y2 := by
  subst h
  rw [Subtype.ext hy]

theorem number_tMF (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val) (y : X.packingData.MotifFiber b) :
    X'.shrinkNumber (tS X X' b.1, b.2) (tMF b hall y) = X.shrinkNumber b y := by
  obtain ⟨m2, rfl⟩ := y
  apply Fin.ext
  rw [bundle_rank_eq m2 (tM m2 (hall ⟨m2, rfl⟩)) rfl (hall ⟨m2, rfl⟩) (fun m4 h4 => hall ⟨m4, h4⟩)]
  exact fib_number_congr X' (bundle_tA m2 _ rfl (hall ⟨m2, rfl⟩)).symm _ _ rfl

theorem abWidth_tMF (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val)
    (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1) (y : X.packingData.MotifFiber b) :
    X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (tMF b hall y).1 =
      X.packingData.abWidth X.shrinkNumber X.packingWidth y.1 := by
  obtain ⟨m2, rfl⟩ := y
  exact (abWidth_eq m2 _ rfl (hall ⟨m2, rfl⟩) (fun m4 h4 => hall ⟨m4, h4⟩) h2).symm

/-- **AB bits.** `demandBitEquiv` of a bundle and of its partner bundle agree on partner motifs. -/
theorem demandBit_tA (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a))
    (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val) (y : X.packingData.MotifFiber b)
    (i : Fin (X.packingData.abWidth X.shrinkNumber X.packingWidth y.1))
    (i' : Fin (X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (tMF b hall y).1))
    (hi : (i : ℕ) = i') :
    (X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth (tS X X' b.1, b.2) ⟨tMF b hall y, i'⟩).1.1.1 =
      tA X X' (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩).1.1.1 ∧
    ((X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth (tS X X' b.1, b.2) ⟨tMF b hall y, i'⟩).2 : ℕ) =
      (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩).2 := by
  obtain ⟨z, hz⟩ : ∃ z, X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩ = z := ⟨_, rfl⟩
  rw [hz]
  have hzw : X'.packingWidth (tThick b h1 h2 z.1).1.1 = X.packingWidth z.1.1.1 :=
    packingWidth_tA z.1.1.1 (thick_ends b z.1 h1 h2).1
  let bit' : Fin (X'.packingWidth (tThick b h1 h2 z.1).1.1) := ⟨z.2, lt_of_lt_of_eq z.2.isLt hzw.symm⟩
  have hz' : X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
      X'.shrinkOrder X'.packingWidth (tS X X' b.1, b.2) ⟨tMF b hall y, i'⟩ = ⟨tThick b h1 h2 z.1, bit'⟩ := by
    rw [demandBitEquiv_eq_iff]
    refine (orderedBits_transport (iA := inferInstance) (X.shrinkNumber b) (X'.shrinkNumber (tS X X' b.1, b.2))
      (fun m => X.packingData.abWidth X.shrinkNumber X.packingWidth m.1)
      (fun m => X'.packingData.abWidth X'.shrinkNumber X'.packingWidth m.1) (tMF b hall)
      (number_tMF b hall) (abWidth_tMF b hall h2) y i i' hi).trans ?_
    refine ((demandBitEquiv_eq_iff X.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth b y i z.1 z.2).mp (hz.trans (Sigma.eta z).symm)).trans ?_
    exact (orderedBits_transport (X.shrinkOrder b) (X'.shrinkOrder (tS X X' b.1, b.2))
      (fun t => X.packingWidth t.1.1) (fun t => X'.packingWidth t.1.1) (tThick b h1 h2)
      (thick_rank_eq b h1 h2) (fun t => packingWidth_tA t.1.1 (thick_ends b t h1 h2).1) z.1 z.2 bit' rfl).symm
  rw [hz']
  exact ⟨rfl, rfl⟩

theorem orderedBits_transport' {A A' : Type*} {iA : Fintype A} {iA' : Fintype A'} {n : ℕ} (o : A ≃ Fin n)
    (o' : A' ≃ Fin n) (w : A → ℕ) (w' : A' → ℕ) (τ : A → A') (hτ : ∀ x, o' (τ x) = o x)
    (hw : ∀ x, w' (τ x) = w x) (x : A) (i : Fin (w x)) (x' : A') (hx' : x' = τ x) (i' : Fin (w' x'))
    (hi : (i : ℕ) = i') :
    (PackingData.orderedBits o' w' ⟨x', i'⟩ : ℕ) = PackingData.orderedBits o w ⟨x, i⟩ := by
  subst hx'
  exact orderedBits_transport o o' w w' τ hτ hw x i i' hi

section Gen

/-- Partner motifs of a bundle, into any equal bundle index. -/
noncomputable abbrev τM (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (y : X.packingData.MotifFiber b) : X'.packingData.MotifFiber b' :=
  ⟨tM y.1 (hall y), (bundle_tA y.1 (tM y.1 (hall y)) rfl (hall y)).trans (by rw [y.2, hb'])⟩

/-- Partner thick wires of a bundle, into any equal bundle index. -/
noncomputable abbrev τT (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (t : X.packingData.ThickFiber b) : X'.packingData.ThickFiber b' :=
  ⟨(tThick b h1 h2 t).1, (tThick b h1 h2 t).2.trans hb'.symm⟩

theorem number_τ (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (y : X.packingData.MotifFiber b) :
    X'.shrinkNumber b' (τM b hall b' hb' y) = X.shrinkNumber b y := by
  subst hb'
  exact number_tMF b hall y

theorem order_τ (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (t : X.packingData.ThickFiber b) :
    X'.shrinkOrder b' (τT b h1 h2 b' hb' t) = X.shrinkOrder b t := by
  subst hb'
  exact thick_rank_eq b h1 h2 t

theorem abW_τ (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1) (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (y : X.packingData.MotifFiber b) :
    X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (τM b hall b' hb' y).1 =
      X.packingData.abWidth X.shrinkNumber X.packingWidth y.1 := by
  subst hb'
  exact abWidth_tMF b hall h2 y

/-- **AB bits**, general form: the partner bundle `b'` and the partner motif `y'` are given by equations. -/
theorem demandBit_gen (b : Site X.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (h1 : SGood X X' b.1.1) (h2 : SGood X X' (X.slots.base.target (b.1.1, b.2)).1) (hall : ∀ y : X.packingData.MotifFiber b, EndsGood X X' y.1.val)
    (b' : Site X'.Base (TagW a) (BitWord g) × Fin (2 ^ a)) (hb' : b' = (tS X X' b.1, b.2)) (y : X.packingData.MotifFiber b)
    (i : Fin (X.packingData.abWidth X.shrinkNumber X.packingWidth y.1))
    (y' : X'.packingData.MotifFiber b') (hy' : y'.1 = tM y.1 (hall y))
    (i' : Fin (X'.packingData.abWidth X'.shrinkNumber X'.packingWidth y'.1)) (hi : (i : ℕ) = i') :
    (X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth b' ⟨y', i'⟩).1.1.1 =
      tA X X' (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩).1.1.1 ∧
    ((X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth b' ⟨y', i'⟩).2 : ℕ) =
      (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩).2 ∧
    SGood X X' (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩).1.1.1.1.1.1 := by
  obtain ⟨z, hz⟩ : ∃ z, X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth b ⟨y, i⟩ = z := ⟨_, rfl⟩
  rw [hz]
  have hzw : X'.packingWidth (τT b h1 h2 b' hb' z.1).1.1 = X.packingWidth z.1.1.1 :=
    packingWidth_tA z.1.1.1 (thick_ends b z.1 h1 h2).1
  let bit' : Fin (X'.packingWidth (τT b h1 h2 b' hb' z.1).1.1) := ⟨z.2, lt_of_lt_of_eq z.2.isLt hzw.symm⟩
  have hz' : X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
      X'.shrinkOrder X'.packingWidth b' ⟨y', i'⟩ = ⟨τT b h1 h2 b' hb' z.1, bit'⟩ := by
    rw [demandBitEquiv_eq_iff]
    refine (orderedBits_transport' (iA := inferInstance) (X.shrinkNumber b) (X'.shrinkNumber b')
      (fun m => X.packingData.abWidth X.shrinkNumber X.packingWidth m.1)
      (fun m => X'.packingData.abWidth X'.shrinkNumber X'.packingWidth m.1) (τM b hall b' hb')
      (number_τ b hall b' hb') (abW_τ b h2 hall b' hb') y i y' (Subtype.ext hy') i' hi).trans ?_
    refine ((demandBitEquiv_eq_iff X.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth b y i z.1 z.2).mp (hz.trans (Sigma.eta z).symm)).trans ?_
    exact (orderedBits_transport (X.shrinkOrder b) (X'.shrinkOrder b')
      (fun t => X.packingWidth t.1.1) (fun t => X'.packingWidth t.1.1) (τT b h1 h2 b' hb')
      (order_τ b h1 h2 b' hb') (fun t => packingWidth_tA t.1.1 (thick_ends b t h1 h2).1) z.1 z.2 bit' rfl).symm
  rw [hz']
  exact ⟨rfl, rfl, (thick_ends b z.1 h1 h2).1⟩

end Gen

/-- **AB bits of a motif and its partner**, in the form used by `localAWord` and `localBWord`. -/
theorem demandBit_motif (m : X.packingData.Motif) (hE : EndsGood X X' m.val)
    (hball : ∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m → EndsGood X X' m2.val)
    (hBg : SGood X X' (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1)
    (i : Fin (X.packingData.abWidth X.shrinkNumber X.packingWidth m))
    (i' : Fin (X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (tM m hE))) (hi : (i : ℕ) = i') :
    (X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth (X'.packingData.bundle (tM m hE)) ⟨⟨tM m hE, rfl⟩, i'⟩).1.1.1 =
      tA X X' (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth (X.packingData.bundle m) ⟨⟨m, rfl⟩, i⟩).1.1.1 ∧
    ((X'.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a) X'.shrinkNumber
        X'.shrinkOrder X'.packingWidth (X'.packingData.bundle (tM m hE)) ⟨⟨tM m hE, rfl⟩, i'⟩).2 : ℕ) =
      (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth (X.packingData.bundle m) ⟨⟨m, rfl⟩, i⟩).2 ∧
    SGood X X' (X.packingData.demandBitEquiv (State.two_le_packingColors a) (Nat.two_pow_pos a)
        X.shrinkNumber X.shrinkOrder X.packingWidth (X.packingData.bundle m) ⟨⟨m, rfl⟩, i⟩).1.1.1.1.1.1 :=
  demandBit_gen (X.packingData.bundle m) (C_good m hE) hBg (fun y => hball y.1 y.2)
    (X'.packingData.bundle (tM m hE)) (bundle_tA m (tM m hE) rfl hE) ⟨m, rfl⟩ i ⟨tM m hE, rfl⟩ rfl i' hi

end Bits

end P1P7
