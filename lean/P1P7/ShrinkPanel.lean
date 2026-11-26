import P1P7.ShrinkLocal

/-!
# P7, shrink half: proof of `shrink_panel_local` (radius 6)

The far slot numbers at `(x, j)` are ranks in the fibres at the other end of each new arc (OpenAI's
`paddedSlot_numbers`). The other end is a role base of the same motif, within distance 4 of `x` (both are within
distance 2 of the old wire), so `rank_eq` at that centre needs good bases within distance 4 + 2 = 6 of `x`.
`shrink_panel_local'` has the statement of `P1P7.shrink_panel_local` (P1P7/Statement.lean:185).
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
noncomputable local instance instDecEqBasePanel {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

section Far

variable {a b g : ℕ} {δ : ℝ}

/-- Two role bases of one motif are within distance 4. -/
theorem roles_near (X : State a (packingLaneBits a g)) (layout : Bool) (r r' : PackedRole)
    (m : X.packingData.Motif) :
    (baseGraph X).edist (X.packingData.survivingRole layout r m).1
      (X.packingData.survivingRole layout r' m).1 ≤ 4 := by
  obtain ⟨a1, -⟩ := role_ends X layout r m
  obtain ⟨b1, -⟩ := role_ends X layout r' m
  calc (baseGraph X).edist (X.packingData.survivingRole layout r m).1 (X.packingData.survivingRole layout r' m).1
      ≤ (baseGraph X).edist (X.packingData.survivingRole layout r m).1 m.val.1.1.1 +
        (baseGraph X).edist m.val.1.1.1 (X.packingData.survivingRole layout r' m).1 :=
          SimpleGraph.edist_triangle
    _ ≤ 2 + 2 := add_le_add a1 (by rw [SimpleGraph.edist_comm]; exact b1)
    _ = 4 := by norm_num

theorem good_near {X X' : State a (packingLaneBits a g)} {x w : X.Base}
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 6 → SGood X X' y) (hw : (baseGraph X).edist x w ≤ 4) :
    ∀ y, (baseGraph X).edist w y ≤ 2 → SGood X X' y := fun y hy =>
  hgood y ((SimpleGraph.edist_triangle (v := w)).trans ((add_le_add hw hy).trans (by norm_num)))

variable (X X' : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
  (layout : Bool)
variable (w : X.packingData.Motif → Fin 4 → ℕ) (w' : X'.packingData.Motif → Fin 4 → ℕ)

/-- Far slot numbers of the out-slots at `(x, j)` (radius 6). -/
theorem outFar_shrink (x : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 6 → SGood X X' y) :
    outFar (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)) (x, j) =
      outFar (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)) (pb X X' x, j) := by
  have hgood2 : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y h => hgood y (h.trans (by norm_num))
  funext k
  rcases out_corr X X' ready layout x j hgood2 k with ⟨z, hm, h1, h2, hE⟩ | ⟨i, h1, h2⟩
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target
        ((x, j), k) = (X.shrinkStateIndex ready layout).incoming (.inl z) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inl z); rw [h1] at e; exact e
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).incoming (.inl (tId z hm)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inl (tId z hm)); rw [h2] at e; exact e
    have hsrc : endpoint (X.packingData.roleBase layout) (sourceRole layout) z = (x, j) :=
      ((X.shrinkStateIndex ready layout).src_eq (.inl z)).symm.trans (congrArg Prod.fst h1)
    have hx : (X.packingData.survivingRole layout (sourceRole layout z.1) z.2.1.1).1 = x :=
      congrArg Prod.fst hsrc
    have hw : (baseGraph X).edist x (endpoint (X.packingData.roleBase layout) (targetRole layout) z).1 ≤ 4 := by
      have := roles_near X layout (sourceRole layout z.1) (targetRole layout z.1) z.2.1.1
      rw [hx] at this
      exact this
    have r3 := rank_eq X X' (SD a b) layout (targetRole layout)
      (endpoint (X.packingData.roleBase layout) (targetRole layout) z).1
      (endpoint (X.packingData.roleBase layout) (targetRole layout) z).2 (good_near hgood hw) z
      ((mem_fib X (SD a b) layout (targetRole layout) _ z).mpr rfl) hm
    simp only [outFar]
    rw [t1, t1', in_rank X ready layout z, in_rank X' ready layout (tId z hm),
      endpoint_tId layout (targetRole layout) z hm hE]
    exact r3
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target
        ((x, j), k) = (X.shrinkStateIndex ready layout).incoming (.inr ((x, j), i)) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inr ((x, j), i)); rw [h1] at e; exact e
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).incoming (.inr ((pb X X' x, j), i)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inr ((pb X X' x, j), i)); rw [h2] at e; exact e
    simp only [outFar]
    rw [t1, t1', in_dummy_val X ready layout (x, j) i, in_dummy_val X' ready layout (pb X X' x, j) i]

/-- Far slot numbers of the in-slots at `(x, j)` (radius 6). -/
theorem inFar_shrink (x : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 6 → SGood X X' y) :
    inFar (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)) (x, j) =
      inFar (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)) (pb X X' x, j) := by
  have hgood2 : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y h => hgood y (h.trans (by norm_num))
  funext k
  rcases in_corr X X' ready layout x j hgood2 k with ⟨z, hm, h1, h2, hE⟩ | ⟨i, h1, h2⟩
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target.symm
        ((x, j), k) = (X.shrinkStateIndex ready layout).outgoing (.inl z) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inl z); rw [h1] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target.symm
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).outgoing (.inl (tId z hm)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inl (tId z hm)); rw [h2] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    have hdst : endpoint (X.packingData.roleBase layout) (targetRole layout) z = (x, j) :=
      ((X.shrinkStateIndex ready layout).dst_eq (.inl z)).symm.trans (congrArg Prod.fst h1)
    have hx : (X.packingData.survivingRole layout (targetRole layout z.1) z.2.1.1).1 = x :=
      congrArg Prod.fst hdst
    have hw : (baseGraph X).edist x (endpoint (X.packingData.roleBase layout) (sourceRole layout) z).1 ≤ 4 := by
      have := roles_near X layout (targetRole layout z.1) (sourceRole layout z.1) z.2.1.1
      rw [hx] at this
      exact this
    have r3 := rank_eq X X' (SD a b) layout (sourceRole layout)
      (endpoint (X.packingData.roleBase layout) (sourceRole layout) z).1
      (endpoint (X.packingData.roleBase layout) (sourceRole layout) z).2 (good_near hgood hw) z
      ((mem_fib X (SD a b) layout (sourceRole layout) _ z).mpr rfl) hm
    simp only [inFar]
    rw [t1, t1', out_rank X ready layout z, out_rank X' ready layout (tId z hm),
      endpoint_tId layout (sourceRole layout) z hm hE]
    exact r3
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target.symm
        ((x, j), k) = (X.shrinkStateIndex ready layout).outgoing
          (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i)) := by
      have e := (X.shrinkStateIndex ready layout).match_eq
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i)); rw [h1] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target.symm
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).outgoing
          (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i)); rw [h2] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    simp only [inFar]
    rw [t1, t1', out_dummy_val X ready layout _ i, out_dummy_val X' ready layout _ i]

end Far

/-! ## The theorem -/

section Main

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- The statement of `P1P7.shrink_panel_local` (Statement.lean:185), PROVED. -/
theorem shrink_panel_local' (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 6 →
      shrinkData B X s y = shrinkData B X' s' y')
    (hlayout : layoutBit B X s = layoutBit B X' s')
    (j : BitWord (packingTagBits (2 ^ a))) :
    panel (X.shrinkNext B ready s) (x, j) = panel (X'.shrinkNext B ready s') (x', j) := by
  have hg := good_of_agree B X X' s s' x x' hx 5 (fun y y' h hd => hagree y y' h (by simpa using hd))
  have hgood6 : ∀ y, (baseGraph X).edist x y ≤ 6 → SGood X X' y :=
    fun y hy => (hg y (by simpa using hy)).1
  have hgood : ∀ y, (baseGraph X).edist x y ≤ 3 → SGood X X' y :=
    fun y hy => hgood6 y (hy.trans (by norm_num))
  have hch : ∀ y, (baseGraph X).edist x y ≤ 3 → choiceAt B X s y = choiceAt B X' s' (pb X X' y) :=
    fun y hy => (hg y (by simpa using hy.trans (by norm_num : (3 : ℕ∞) ≤ 6))).2
  have hgood2 : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y :=
    fun y h => hgood y (h.trans (by norm_num))
  have hxx : pb X X' x = x' := pb_eq X X' hx
  subst hxx
  have key : ∀ L L' : Bool, L = L' →
      panel (X.shrinkOutputState L (SD a b)
        (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m L t)
        (X.shrinkStateIndex ready L)) (x, j) =
      panel (X'.shrinkOutputState L' (SD a b)
        (fun m t ↦ X'.packingData.termWidths B X'.shrinkNumber X'.packingWidth s' m L' t)
        (X'.shrinkStateIndex ready L')) (pb X X' x, j) := by
    rintro L _ rfl
    unfold panel
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · exact outNbr_shrink X X' ready L _ _ x j hgood2
    · exact outFar_shrink X X' ready L _ _ x j hgood6
    · exact inNbr_shrink X X' ready L _ _ x j hgood2
    · exact inFar_shrink X X' ready L _ _ x j hgood6
    · exact outWidths_shrink B ready X X' s s' L x j hgood hch
  exact key _ _ hlayout

end Main

end P1P7
