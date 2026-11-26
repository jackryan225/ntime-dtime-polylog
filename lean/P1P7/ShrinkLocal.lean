import P1P7.ShrinkWidth

/-!
# P7, shrink half: proof of `shrink_records_local` (radius 3)

`shrink_records_local'` has the statement of `P1P7.shrink_records_local` (P1P7/Statement.lean:174). The proof:
* from `hagree` and `addr_transport`: every base within distance 3 of `x` has a partner, and is `SGood`, and its term
  data agree (`choiceAt`);
* `outNbr_shrink`, `inNbr_shrink` (ShrinkGraph.lean, radius 2);
* `outWidths_shrink` (below, radius 3): genuine arcs via OpenAI's `shrinkSlotWidth_genuine` and `termWidths_eq`;
  padding arcs via `shrinkSlotWidth_padding`.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBaseLocal {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

theorem edist_le_three {a G : ℕ} {X : State a G} {u v w : X.Base} (h1 : (baseGraph X).edist u v ≤ 2)
    (h2 : (baseGraph X).edist v w ≤ 1) : (baseGraph X).edist u w ≤ 3 :=
  (SimpleGraph.edist_triangle (v := v)).trans ((add_le_add h1 h2).trans_eq two_add_one_eq_three)

section Widths

variable {a b g : ℕ} {δ factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- The widths at `(x, j)` (radius 3). -/
theorem outWidths_shrink (X X' : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (s' : X'.ShrinkSelection B) (layout : Bool) (x : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 3 → SGood X X' y)
    (hch : ∀ y, (baseGraph X).edist x y ≤ 3 → choiceAt B X s y = choiceAt B X' s' (pb X X' y)) :
    outWidths (X.shrinkOutputState layout (SD a b)
        (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t)
        (X.shrinkStateIndex ready layout)) (x, j) =
      outWidths (X'.shrinkOutputState layout (SD a b)
        (fun m t ↦ X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m layout t)
        (X'.shrinkStateIndex ready layout)) (pb X X' x, j) := by
  have hgood2 : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y h => hgood y (h.trans (by norm_num))
  funext k l
  rcases out_corr X X' ready layout x j hgood2 k with ⟨⟨t, bm, sidx⟩, hm, h1, h2, hE⟩ | ⟨i, h1, h2⟩
  · -- a genuine arc: the slice of the term width of the actual motif at lane `l`
    have hsrc : endpoint (X.packingData.roleBase layout) (sourceRole layout) ⟨t, bm, sidx⟩ = (x, j) :=
      ((X.shrinkStateIndex ready layout).src_eq (.inl ⟨t, bm, sidx⟩)).symm.trans (congrArg Prod.fst h1)
    have hv : (X.packingData.survivingRole layout (sourceRole layout t) bm.1).1 = x := congrArg Prod.fst hsrc
    obtain ⟨hy1, hy2⟩ := role_ends X layout (sourceRole layout t) bm.1
    rw [hv] at hy1 hy2
    have hCx : (baseGraph X).edist x (X.packingData.C bm.1).1.1 ≤ 2 := by
      rcases C_base X bm.1 with h | h <;> rw [h]
      · exact hy1
      · exact hy2
    have g1 := X.packingData.shrinkSlotWidth_genuine layout (SD a b)
      (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t)
      (X.shrinkStateIndex ready layout).outgoing
      ((X.packingData.survivingLaneEquiv layout (SD a b)).symm (⟨t, bm, sidx⟩, l))
    have g1' := X'.packingData.shrinkSlotWidth_genuine layout (SD a b)
      (fun m t ↦ X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m layout t)
      (X'.shrinkStateIndex ready layout).outgoing
      ((X'.packingData.survivingLaneEquiv layout (SD a b)).symm (tId ⟨t, bm, sidx⟩ hm, l))
    simp only [PackingData.shrinkArcEquiv_genuine, Equiv.apply_symm_apply, h1] at g1
    simp only [PackingData.shrinkArcEquiv_genuine, Equiv.apply_symm_apply, h2] at g1'
    refine g1.trans (Eq.trans ?_ g1'.symm)
    -- the actual motifs at lane `l`
    have hlane : (X'.packingData.survivingRole layout (sourceRole layout t) ⟨tA X X' bm.1.val, hm⟩).2.2 =
        (X.packingData.survivingRole layout (sourceRole layout t) bm.1).2.2 := by
      exact congrArg (fun q => q.2.2)
        (survivingRole_tA layout (sourceRole layout t) bm.1 ⟨tA X X' bm.1.val, hm⟩ rfl hE)
    let m := X.packingData.translateMotif bm.1
      (l - (X.packingData.survivingRole layout (sourceRole layout t) bm.1).2.2)
    let m' := X'.packingData.translateMotif ⟨tA X X' bm.1.val, hm⟩
      (l - (X'.packingData.survivingRole layout (sourceRole layout t) ⟨tA X X' bm.1.val, hm⟩).2.2)
    have hmm : m'.val = tA X X' m.val := by
      show translateArc (tA X X' bm.1.val)
          (l - (X'.packingData.survivingRole layout (sourceRole layout t) ⟨tA X X' bm.1.val, hm⟩).2.2) =
        tA X X' (translateArc bm.1.val (l - (X.packingData.survivingRole layout (sourceRole layout t) bm.1).2.2))
      rw [hlane]; rfl
    have hEm : EndsGood X X' m.val := hE
    have hbm : X.packingData.bundle m =
        (translateSite (X.packingData.bundle bm.1).1
          (l - (X.packingData.survivingRole layout (sourceRole layout t) bm.1).2.2),
          (X.packingData.bundle bm.1).2) :=
      PackingData.bundle_translate _ _ _
    have hball : ∀ m2 : X.packingData.Motif, X.packingData.bundle m2 = X.packingData.bundle m →
        EndsGood X X' m2.val := by
      intro m2 hb
      have hc : (X.packingData.C m2).1.1 = (X.packingData.C bm.1).1.1 :=
        congrArg (fun q => q.1.1) (hb.trans hbm)
      obtain ⟨e1, e2⟩ := ends_of_base X m2 (C_base X m2)
      rw [hc] at e1 e2
      exact ⟨hgood _ (edist_le_three hCx e1), hgood _ (edist_le_three hCx e2)⟩
    have hBg : SGood X X'
        (X.slots.base.target ((X.packingData.bundle m).1.1, (X.packingData.bundle m).2)).1 := by
      rw [hbm]
      exact hgood _ (edist_le_three hCx (edist_target_le X (X.packingData.C bm.1).1.1 _))
    have hchm : choiceAt B X s m.val.1.1.1 = choiceAt B X' s' (pb X X' m.val.1.1.1) :=
      hch _ (hy1.trans (by norm_num))
    have hw := termWidths_eq B s s' m m' hmm hEm hball hBg hchm layout t
    show splitWidth (X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t) (SD a b t) sidx =
      splitWidth (X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m' layout t) (SD a b t) sidx
    rw [hw]
  · -- a padding arc: width 0 on both sides
    have e1 := X.packingData.shrinkSlotWidth_padding layout (SD a b)
      (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t)
      (X.shrinkStateIndex ready layout).outgoing ((x, j), i) l
    rw [h1] at e1
    have e2 := X'.packingData.shrinkSlotWidth_padding layout (SD a b)
      (fun m t ↦ X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m layout t)
      (X'.shrinkStateIndex ready layout).outgoing ((pb X X' x, j), i) l
    rw [h2] at e2
    exact e1.trans e2.symm

end Widths

/-! ## The theorem -/

section Main

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- Agreement of `shrinkData` on a ball gives `SGood` and equal term data on that ball. -/
theorem good_of_agree (X X' : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (s' : X'.ShrinkSelection B) (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x') (r : ℕ)
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ (r + 1 : ℕ) →
      shrinkData B X s y = shrinkData B X' s' y') :
    ∀ y, (baseGraph X).edist x y ≤ (r + 1 : ℕ) →
      SGood X X' y ∧ choiceAt B X s y = choiceAt B X' s' (pb X X' y) := by
  intro y hy
  have hnb : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ r →
      ∀ kk, addr X (X.slots.base.target (y, kk)).1 = addr X' (X'.slots.base.target (y', kk)).1 ∧
        addr X (X.slots.base.target.symm (y, kk)).1 = addr X' (X'.slots.base.target.symm (y', kk)).1 := by
    intro y y' h hd kk
    have hd' : (baseGraph X).edist x y ≤ (r + 1 : ℕ) := hd.trans (by exact_mod_cast Nat.le_succ r)
    have hp : panel X y = panel X' y' := congrArg (fun q => q.1) (hagree y y' h hd')
    have h1 := congrFun (congrArg (fun q => q.1) hp : outNbr X y = outNbr X' y') kk
    have h2 := congrFun (congrArg (fun q => q.2.2.1) hp : inNbr X y = inNbr X' y') kk
    exact ⟨congrArg Prod.fst h1, congrArg Prod.fst h2⟩
  have hy' : (baseGraph X).edist x y ≤ r + 1 := by exact_mod_cast hy
  obtain ⟨y', hy'a, -⟩ := addr_transport X X' x x' hx r hnb y hy'
  have hp : pb X X' y = y' := pb_eq X X' hy'a.symm
  have hd := hagree y y' hy'a.symm hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> rw [hp]
  · exact hy'a
  · exact congrArg (fun q => q.1) hd
  · exact congrArg (fun q => q.2.1) hd
  · exact congrArg (fun q => q.2.2.1) hd
  · exact congrArg (fun q => q.2.2.2) hd

/-- The statement of `P1P7.shrink_records_local` (Statement.lean:174), PROVED. -/
theorem shrink_records_local' (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 3 →
      shrinkData B X s y = shrinkData B X' s' y')
    (hlayout : layoutBit B X s = layoutBit B X' s')
    (j : BitWord (packingTagBits (2 ^ a))) :
    nearPanel (X.shrinkNext B ready s) (x, j) = nearPanel (X'.shrinkNext B ready s') (x', j) := by
  have hg := good_of_agree B X X' s s' x x' hx 2 (fun y y' h hd => hagree y y' h (by simpa using hd))
  have hgood : ∀ y, (baseGraph X).edist x y ≤ 3 → SGood X X' y :=
    fun y hy => (hg y (by simpa using hy)).1
  have hch : ∀ y, (baseGraph X).edist x y ≤ 3 → choiceAt B X s y = choiceAt B X' s' (pb X X' y) :=
    fun y hy => (hg y (by simpa using hy)).2
  have hgood2 : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y h => hgood y (h.trans (by norm_num))
  have hxx : pb X X' x = x' := pb_eq X X' hx
  subst hxx
  have key : ∀ L L' : Bool, L = L' →
      nearPanel (X.shrinkOutputState L (SD a b)
        (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m L t)
        (X.shrinkStateIndex ready L)) (x, j) =
      nearPanel (X'.shrinkOutputState L' (SD a b)
        (fun m t ↦ X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m L' t)
        (X'.shrinkStateIndex ready L')) (pb X X' x, j) := by
    rintro L _ rfl
    unfold nearPanel
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact outNbr_shrink X X' ready L _ _ x j hgood2
    · exact inNbr_shrink X X' ready L _ _ x j hgood2
    · exact outWidths_shrink B ready X X' s s' L x j hgood hch
  exact key _ _ hlayout

end Main

end P1P7
