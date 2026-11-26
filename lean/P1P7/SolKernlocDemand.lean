import P1P7.SolKernlocBits

namespace P1P7.SolKernloc

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.MotifDemandPadding

theorem placed_at {U V : Type} {p : U → V} {F : U → Type}
    {v w : V} (e : v = w) (f : Placed p F v) (u : U) (h : w = p u) :
    (e ▸ f) u h = f u (e.trans h) := by
  subst e
  rfl

def placedAlong {U V : Type} {p : U → V} {F : U → Type}
    {v w : V} (e : v = w) (f : Placed p F v) : Placed p F w :=
  fun u h => f u (e.trans h)

theorem placed_cast_eq {U V : Type} {p : U → V} {F : U → Type}
    {v w : V} (e : v = w) (f : Placed p F v) :
    (e ▸ f) = placedAlong e f := by
  subst e
  rfl

attribute [local instance] instDecEqBaseT

section Generic

theorem heq_fun_apply {n n' : ℕ} (h : n' = n) {f' : Fin n' → Bool} {f : Fin n → Bool} (hf : HEq f' f)
    (i' : Fin n') (i : Fin n) (hi : (i' : ℕ) = i) : f' i' = f i := by
  subst h
  cases hf
  rw [Fin.ext hi]

theorem halfBits_heq {D J : Type*} {src dst : D → J} {w w' : D → ℕ} (hw : w' = w) {j : J}
    (x' : HalfBits src dst w' j) (x : HalfBits src dst w j)
    (h1 : ∀ e he, ((x'.1 e he : Fin (2 ^ w' e)) : ℕ) = (x.1 e he : Fin (2 ^ w e)))
    (h2 : ∀ e he, ((x'.2 e he : Fin (2 ^ w' e)) : ℕ) = (x.2 e he : Fin (2 ^ w e))) : HEq x' x := by
  subst hw
  exact heq_of_eq (Prod.ext (funext fun e => funext fun he => Fin.ext (h1 e he))
    (funext fun e => funext fun he => Fin.ext (h2 e he)))

theorem wordBits_symm_val {n n' : ℕ} (h : n' = n) (b' : Fin n' → Bool) (b : Fin n → Bool)
    (hb : ∀ (i' : Fin n') (i : Fin n), (i' : ℕ) = i → b' i' = b i) :
    ((RAMSerialization.wordBits n').symm b' : ℕ) = ((RAMSerialization.wordBits n).symm b : ℕ) := by
  subst h
  have : b' = b := funext fun i => hb i i rfl
  rw [this]

end Generic

section Canon

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}

/-- Old half-wires placed at `v` in packed coordinates. -/
abbrev PH (X : State a (packingLaneBits a g)) (L : Bool) (v : (X.Base × TagW a) × BitWord g) :=
  Placed (U := (X.packingData.oldWireNetwork X.packingWidth).Site) (X.packingData.shrinkPlace L)
    (X.packingData.oldWireNetwork X.packingWidth).Half v

/-- Out-halves of partner wires at partner positions carry the same word. -/
def OutCanon {L L' : Bool} {v : (X.Base × TagW a) × BitWord g} {v' : (X'.Base × TagW a) × BitWord g}
    (f : PH X L v) (f' : PH X' L' v') : Prop :=
  ∀ (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (hp : v = X.packingData.shrinkPlace L p) (hp' : v' = X'.packingData.shrinkPlace L' (tP X X' p))
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)) (hα : p = sourcePosition α),
    HEq ((f' (tP X X' p) hp').1 (tA X X' α) (congrArg (tP X X') hα)) ((f p hp).1 α hα)

/-- In-halves of partner wires at partner positions carry the same word. -/
def InCanon {L L' : Bool} {v : (X.Base × TagW a) × BitWord g} {v' : (X'.Base × TagW a) × BitWord g}
    (f : PH X L v) (f' : PH X' L' v') : Prop :=
  ∀ (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (hp : v = X.packingData.shrinkPlace L p) (hp' : v' = X'.packingData.shrinkPlace L' (tP X X' p))
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (hα : p = sourcePosition (X.packingData.actual α))
    (hα' : tP X X' p = sourcePosition (X'.packingData.actual (tA X X' α))),
    HEq ((f' (tP X X' p) hp').2 (tA X X' α) hα') ((f p hp).2 α hα)

variable {L L' : Bool} {v : (X.Base × TagW a) × BitWord g} {v' : (X'.Base × TagW a) × BitWord g}

theorem read_out {f : PH X L v} {f' : PH X' L' v'} (hc : OutCanon f f')
    (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1)) (hp : v = X.packingData.shrinkPlace L p)
    (p' : Position X'.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (hp' : v' = X'.packingData.shrinkPlace L' p')
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (α' : Arc X'.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (hα : p = sourcePosition α) (hα' : p' = sourcePosition α') (hpp : p' = tP X X' p) (haa : α' = tA X X' α)
    (hw : X'.packingWidth (tA X X' α) = X.packingWidth α)
    (b : Fin (X.packingWidth α)) (b' : Fin (X'.packingWidth α')) (hb : (b' : ℕ) = b) :
    (f' p' hp').1 α' hα' b' = (f p hp).1 α hα b := by
  subst hpp
  subst haa
  exact heq_fun_apply hw (hc p hp hp' α hα) b' b hb

theorem read_in {f : PH X L v} {f' : PH X' L' v'} (hc : InCanon f f')
    (p : Position X.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1)) (hp : v = X.packingData.shrinkPlace L p)
    (p' : Position X'.Base (BitWord a) (TagW a) (BitWord g) (2 * 2 ^ a + 1))
    (hp' : v' = X'.packingData.shrinkPlace L' p')
    (α : Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (α' : Arc X'.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1))
    (hα : p = sourcePosition (X.packingData.actual α)) (hα' : p' = sourcePosition (X'.packingData.actual α'))
    (hpp : p' = tP X X' p) (haa : α' = tA X X' α)
    (hw : X'.packingWidth (tA X X' α) = X.packingWidth α)
    (b : Fin (X.packingWidth α)) (b' : Fin (X'.packingWidth α')) (hb : (b' : ℕ) = b) :
    (f' p' hp').2 α' hα' b' = (f p hp).2 α hα b := by
  subst hpp
  subst haa
  exact heq_fun_apply hw (hc p hp hp' α hα hα') b' b hb

end Canon


section Lookup

variable {V H Tag G : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup G]
variable (P : PackingData V H Tag G d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype G]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq G]
variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag G d c → ℕ) (L : Bool) (m : P.Motif)
variable (i : Fin (P.abWidth number w m))
variable (z : (t : P.ThickFiber (P.bundle m)) × Fin (w t.1.1))
variable (hz : P.demandBitEquiv hc hd number order w (P.bundle m) ⟨⟨m, rfl⟩, i⟩ = z)

include hz in
private theorem localA_lookup (f : P.PlacedHalf w L (P.roleA m)) :
    P.localAWord hc hd number order w L m f i =
      (f (sourcePosition z.1.1.1) ((congrArg Prod.fst z.1.2.symm).trans
        (P.place_thick_source L z.1.1).symm)).1 z.1.1.1 rfl z.2 := by
  subst z
  rfl

include hz in
private theorem localB_lookup (f : P.PlacedHalf w L (P.roleB m)) :
    P.localBWord hc hd number order w L m f i =
      (f (sourcePosition (P.actual z.1.1.1))
        ((congrArg (fun b => (P.siteGraph.target b).1) z.1.2.symm).trans
          (P.place_thick_target L z.1.1).symm)).2 z.1.1.1 rfl z.2 := by
  subst z
  rfl

end Lookup

section Demand

variable {a g : ℕ} {X X' : State a (packingLaneBits a g)}
variable {L L' : Bool} {v : (X.Base × TagW a) × BitWord g} {v' : (X'.Base × TagW a) × BitWord g}
variable {f : PH X L v} {f' : PH X' L' v'}
variable {m : X.packingData.Motif} (hE : EndsGood X X' m.val)

private abbrev PackedArc (X : State a (packingLaneBits a g)) :=
  Arc X.Base (BitWord a) (TagW a) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)

private theorem demandOut (hc : OutCanon f f')
    (α : PackedArc X) (α' : PackedArc X') (hα : α' = tA X X' α) (h : SGood X X' α.1.1.1)
    (hp : v = X.packingData.shrinkPlace L (sourcePosition α))
    (hp' : v' = X'.packingData.shrinkPlace L' (sourcePosition α'))
    (i : Fin (X.packingWidth α)) (i' : Fin (X'.packingWidth α')) (hi : (i' : ℕ) = i) :
    (f' (sourcePosition α') hp').1 α' rfl i' = (f (sourcePosition α) hp).1 α rfl i :=
  read_out hc _ hp _ hp' _ _ rfl rfl (congrArg sourcePosition hα) hα (packingWidth_tA α h) i i' hi

private theorem demandIn (hc : InCanon f f')
    (α : PackedArc X) (α' : PackedArc X') (hα : α' = tA X X' α) (h : SGood X X' α.1.1.1)
    (hp : v = X.packingData.shrinkPlace L (sourcePosition (X.packingData.actual α)))
    (hp' : v' = X'.packingData.shrinkPlace L' (sourcePosition (X'.packingData.actual α')))
    (i : Fin (X.packingWidth α)) (i' : Fin (X'.packingWidth α')) (hi : (i' : ℕ) = i) :
    (f' (sourcePosition (X'.packingData.actual α')) hp').2 α' rfl i' =
      (f (sourcePosition (X.packingData.actual α)) hp).2 α rfl i := by
  have hpos : sourcePosition (X'.packingData.actual α') =
      tP X X' (sourcePosition (X.packingData.actual α)) :=
    congrArg sourcePosition ((congrArg X'.packingData.actual hα).trans (actual_tA X X' α h))
  exact read_in hc _ hp _ hp' _ _ rfl rfl hpos hα (packingWidth_tA α h) i i' hi

variable (hball : ∀ m₂ : X.packingData.Motif,
  X.packingData.bundle m₂ = X.packingData.bundle m → EndsGood X X' m₂.val)
variable (hBg : SGood X X' (X.slots.base.target
  ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1)

private theorem placeABOut {Y : State a (packingLaneBits a g)} {M : Y.packingData.Motif}
    {L : Bool} {v : (Y.Base × TagW a) × BitWord g}
    (hv : v = Y.packingData.shrinkPartySite L M 0)
    (t : Y.packingData.ThickFiber (Y.packingData.bundle M)) :
    v = Y.packingData.shrinkPlace L (sourcePosition t.1.1) :=
  hv.trans (congrArg packedSiteEquiv
    ((congrArg Prod.fst t.2.symm).trans
      (Y.packingData.place_thick_source L t.1).symm))

private theorem placeABIn {Y : State a (packingLaneBits a g)} {M : Y.packingData.Motif}
    {L : Bool} {v : (Y.Base × TagW a) × BitWord g}
    (hv : v = Y.packingData.shrinkPartySite L M 1)
    (t : Y.packingData.ThickFiber (Y.packingData.bundle M)) :
    v = Y.packingData.shrinkPlace L (sourcePosition (Y.packingData.actual t.1.1)) :=
  hv.trans (congrArg packedSiteEquiv
    ((congrArg (fun b => (Y.packingData.siteGraph.target b).1) t.2.symm).trans
      (Y.packingData.place_thick_target L t.1).symm))

include hball hBg in
private theorem localA (hc : OutCanon f f')
    (hv : v = X.packingData.shrinkPartySite L m 0)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) 0)
    (i : Fin (X.packingData.abWidth X.shrinkNumber X.packingWidth m))
    (i' : Fin (X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (tM m hE)))
    (hi : (i' : ℕ) = i) :
    X'.packingData.localAWord (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE)
      (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _ rfl (placedAlong hv' f')) i' =
    X.packingData.localAWord (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth L m
      (X.packingData.shrinkPlacedHalf X.packingWidth L _ rfl (placedAlong hv f)) i := by
  obtain ⟨z, z', hz, hz', ha, hb, hg⟩ := demandBit_motif m hE hball hBg i i' hi.symm
  have h := localA_lookup X.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X.shrinkNumber X.shrinkOrder X.packingWidth L m i z hz
    (X.packingData.shrinkPlacedHalf X.packingWidth L _ rfl (placedAlong hv f))
  have h' := localA_lookup X'.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE) i' z' hz'
    (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _ rfl (placedAlong hv' f'))
  have hread := demandOut (X := X) (X' := X') hc z.1.1.1 z'.1.1.1
    ha hg (placeABOut hv z.1) (placeABOut hv' z'.1) z.2 z'.2 hb
  exact h'.trans (hread.trans h.symm)

include hball hBg in
private theorem localB (hc : InCanon f f')
    (hv : v = X.packingData.shrinkPartySite L m 1)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) 1)
    (i : Fin (X.packingData.abWidth X.shrinkNumber X.packingWidth m))
    (i' : Fin (X'.packingData.abWidth X'.shrinkNumber X'.packingWidth (tM m hE)))
    (hi : (i' : ℕ) = i) :
    X'.packingData.localBWord (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE)
      (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _ rfl (placedAlong hv' f')) i' =
    X.packingData.localBWord (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth L m
      (X.packingData.shrinkPlacedHalf X.packingWidth L _ rfl (placedAlong hv f)) i := by
  obtain ⟨z, z', hz, hz', ha, hb, hg⟩ := demandBit_motif m hE hball hBg i i' hi.symm
  have h := localB_lookup X.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X.shrinkNumber X.shrinkOrder X.packingWidth L m i z hz
    (X.packingData.shrinkPlacedHalf X.packingWidth L _ rfl (placedAlong hv f))
  have h' := localB_lookup X'.packingData (State.two_le_packingColors a) (Nat.two_pow_pos a)
    X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE) i' z' hz'
    (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _ rfl (placedAlong hv' f'))
  have hread := demandIn (X := X) (X' := X') hc z.1.1.1 z'.1.1.1
    ha hg (placeABIn hv z.1) (placeABIn hv' z'.1) z.2 z'.2 hb
  exact h'.trans (hread.trans h.symm)

private theorem localC (ho : OutCanon f f') (hn : InCanon f f')
    (hv : v = X.packingData.shrinkPartySite L m 2)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) 2)
    (i : Fin (X.packingWidth m.val)) (i' : Fin (X'.packingWidth (tM m hE).val))
    (hi : (i' : ℕ) = i) :
    X'.packingData.localCWord X'.packingWidth L' (tM m hE)
      (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _
        (X'.packingData.shrinkPartySite_C L' (tM m hE)) (placedAlong hv' f')) i' =
    X.packingData.localCWord X.packingWidth L m
      (X.packingData.shrinkPlacedHalf X.packingWidth L _
        (X.packingData.shrinkPartySite_C L m) (placedAlong hv f)) i := by
  have hh := thick_tP X X' (sourcePosition m.val) hE.1
  have hd := hv.trans (X.packingData.shrinkPartySite_C L m)
  have hd' := hv'.trans (X'.packingData.shrinkPartySite_C L' (tM m hE))
  by_cases ht : X.packingData.thick (sourcePosition m.val)
  · have ht' : X'.packingData.thick (sourcePosition (tM m hE).val) := hh.mpr ht
    have h := hd.trans (congrArg (X.packingData.shrinkPlace L)
      (by exact ite_eq_left ht : X.packingData.C m = _))
    have h' := hd'.trans (congrArg (X'.packingData.shrinkPlace L')
      (by exact ite_eq_left ht' : X'.packingData.C (tM m hE) = _))
    unfold PackingData.localCWord PackingData.shrinkPlacedHalf placedAlong
    erw [dite_eq_left ht', dite_eq_left ht]
    exact demandIn hn m.val (tM m hE).val rfl hE.1 h h' i i' hi
  · have ht' : ¬ X'.packingData.thick (sourcePosition (tM m hE).val) := fun h => ht (hh.mp h)
    have h := hd.trans (congrArg (X.packingData.shrinkPlace L)
      (by exact ite_eq_right ht : X.packingData.C m = _))
    have h' := hd'.trans (congrArg (X'.packingData.shrinkPlace L')
      (by exact ite_eq_right ht' : X'.packingData.C (tM m hE) = _))
    unfold PackingData.localCWord PackingData.shrinkPlacedHalf placedAlong
    erw [dite_eq_right ht', dite_eq_right ht]
    exact demandOut ho m.val (tM m hE).val rfl hE.1 h h' i i' hi

private theorem localD (ho : OutCanon f f') (hn : InCanon f f')
    (hv : v = X.packingData.shrinkPartySite L m 3)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) 3)
    (i : Fin (X.packingWidth m.val)) (i' : Fin (X'.packingWidth (tM m hE).val))
    (hi : (i' : ℕ) = i) :
    X'.packingData.localDWord X'.packingWidth L' (tM m hE)
      (X'.packingData.shrinkPlacedHalf X'.packingWidth L' _ rfl (placedAlong hv' f')) i' =
    X.packingData.localDWord X.packingWidth L m
      (X.packingData.shrinkPlacedHalf X.packingWidth L _ rfl (placedAlong hv f)) i := by
  have hh := thick_tP X X' (sourcePosition m.val) hE.1
  have hd : v = X.packingData.shrinkPlace L (X.packingData.D m) := hv
  have hd' : v' = X'.packingData.shrinkPlace L' (X'.packingData.D (tM m hE)) := hv'
  by_cases ht : X.packingData.thick (sourcePosition m.val)
  · have ht' : X'.packingData.thick (sourcePosition (tM m hE).val) := hh.mpr ht
    have h := hd.trans (congrArg (X.packingData.shrinkPlace L)
      (by exact ite_eq_left ht : X.packingData.D m = _))
    have h' := hd'.trans (congrArg (X'.packingData.shrinkPlace L')
      (by exact ite_eq_left ht' : X'.packingData.D (tM m hE) = _))
    unfold PackingData.localDWord PackingData.shrinkPlacedHalf placedAlong
    erw [dite_eq_left ht', dite_eq_left ht]
    exact demandOut ho m.val (tM m hE).val rfl hE.1 h h' i i' hi
  · have ht' : ¬ X'.packingData.thick (sourcePosition (tM m hE).val) := fun h => ht (hh.mp h)
    have h := hd.trans (congrArg (X.packingData.shrinkPlace L)
      (by exact ite_eq_right ht : X.packingData.D m = _))
    have h' := hd'.trans (congrArg (X'.packingData.shrinkPlace L')
      (by exact ite_eq_right ht' : X'.packingData.D (tM m hE) = _))
    unfold PackingData.localDWord PackingData.shrinkPlacedHalf placedAlong
    erw [dite_eq_right ht', dite_eq_right ht]
    exact demandIn hn m.val (tM m hE).val rfl hE.1 h h' i i' hi

include hball hBg in
private theorem demandArg_along (ho : OutCanon f f') (hn : InCanon f f')
    (j : Fin 6) (hv : v = X.packingData.shrinkPartySite L m j)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) j) :
    HEq (X'.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE) j (placedAlong hv' f'))
      (X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth L m j (placedAlong hv f)) := by
  have hab := (abWidth_eq m (tM m hE) rfl hE hball hBg).symm
  have hcd := packingWidth_tA m.val hE.1
  apply halfBits_heq (funext fun e => by cases e <;> assumption)
  · intro e he
    subst j
    cases e
    · exact wordBits_symm_val hab _ _ (fun i' i hi => localA hE hball hBg ho hv hv' i i' hi)
    · exact wordBits_symm_val hcd _ _ (fun i' i hi => localC hE ho hn hv hv' i i' hi)
  · intro e he
    subst j
    cases e
    · exact wordBits_symm_val hab _ _ (fun i' i hi => localB hE hball hBg hn hv hv' i i' hi)
    · exact wordBits_symm_val hcd _ _ (fun i' i hi => localD hE ho hn hv hv' i i' hi)

include hball hBg in
theorem demandArg_heq (ho : OutCanon f f') (hn : InCanon f f')
    (j : Fin 6) (hv : v = X.packingData.shrinkPartySite L m j)
    (hv' : v' = X'.packingData.shrinkPartySite L' (tM m hE) j) :
    HEq (X'.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE) j (hv' ▸ f'))
      (X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth L m j (hv ▸ f)) := by
  have eh' := placed_cast_eq (p := X'.packingData.shrinkPlace L')
    (F := (X'.packingData.oldWireNetwork X'.packingWidth).Half) hv' f'
  have eh := placed_cast_eq (p := X.packingData.shrinkPlace L)
    (F := (X.packingData.oldWireNetwork X.packingWidth).Half) hv f
  exact (heq_of_eq (congrArg (X'.packingData.shrinkLocalDemandArg (State.two_le_packingColors a)
    (Nat.two_pow_pos a) X'.shrinkNumber X'.shrinkOrder X'.packingWidth L' (tM m hE) j) eh')).trans
      ((demandArg_along hE hball hBg ho hn j hv hv').trans
        (heq_of_eq (congrArg (X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a)
          (Nat.two_pow_pos a) X.shrinkNumber X.shrinkOrder X.packingWidth L m j) eh)).symm)

end Demand

end P1P7.SolKernloc
