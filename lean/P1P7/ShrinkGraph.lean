import P1P7.ShrinkFiber

/-!
# P7, shrink half, layer 4: the new slot graph near `(x, j)`

For the new state `X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)` (the next state of
OpenAI's shrinking pass for `layout` = the layout bit and `w` = the term widths, ShrinkStatePass.lean:62):
* `outNbr_shrink`, `inNbr_shrink`: the neighbour addresses and displacements at `(x, j)` agree with those at
  `(pb x, j)` when every base within distance 2 of `x` is good (any widths `w`, `w'`);
* `outFar_shrink`, `inFar_shrink`: the far slot numbers agree when every base within distance 6 of `x` is good.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBaseGraph {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

theorem cycleTags_apply {V Tag : Type*} {J : ℕ} (index : Tag ≃ Fin J) (v : V) (t : Tag) :
    cycleTags index (v, t) = (v, index.symm (finRotate J (index t))) := rfl

theorem cycleTags_symm_apply {V Tag : Type*} {J : ℕ} (index : Tag ≃ Fin J) (v : V) (t : Tag) :
    (cycleTags index).symm (v, t) = (v, index.symm ((finRotate J).symm (index t))) := rfl

section Graph

variable {a b g : ℕ} {δ : ℝ}

/-- Addresses of the new state (paper rem:G1). -/
theorem addr_shrinkOut (X : State a (packingLaneBits a g)) (layout : Bool)
    (w : X.packingData.Motif → Fin 4 → ℕ) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (p : X.Base × TagW a) :
    addr (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)) p =
      (bitWordFinEquiv (packingTagBits (2 ^ a)) p.2 : ℕ) + 2 ^ packingTagBits (2 ^ a) * addr X p.1 := rfl

theorem out_dummy_val (X : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (q : X.Base × TagW a) (i : Fin (2 ^ b - PackingData.survivingDegree (2 ^ a) (2 * 2 ^ a + 1) (SD a b))) :
    (((X.shrinkStateIndex ready layout).outgoing (.inr (q, i))).2 : ℕ) =
      PackingData.survivingDegree (2 ^ a) (2 * 2 ^ a + 1) (SD a b) + i := rfl

theorem in_dummy_val (X : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (q : X.Base × TagW a) (i : Fin (2 ^ b - PackingData.survivingDegree (2 ^ a) (2 * 2 ^ a + 1) (SD a b))) :
    (((X.shrinkStateIndex ready layout).incoming (.inr (q, i))).2 : ℕ) =
      PackingData.survivingDegree (2 ^ a) (2 * 2 ^ a + 1) (SD a b) + i := rfl

/-- Wire ends of an ID in a fibre at `v` are good when the ball of radius 2 around `v` is good. -/
theorem fib_ends (X X' : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) (layout : Bool)
    (pick : Fin 4 → PackedRole) (v : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist v y ≤ 2 → SGood X X' y)
    (z : SurvivingSlots.Id X.packingData.BaseMotif sd)
    (hz : endpoint (X.packingData.roleBase layout) pick z = (v, j)) : EndsGood X X' z.2.1.1.val := by
  have hv : (X.packingData.survivingRole layout (pick z.1) z.2.1.1).1 = v := congrArg Prod.fst hz
  obtain ⟨h1, h2⟩ := role_ends X layout (pick z.1) z.2.1.1
  rw [hv] at h1 h2
  exact ⟨hgood _ h1, hgood _ h2⟩

variable (X X' : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
  (layout : Bool)

/-- The out-slot `k` at `(x, j)` and at `(pb x, j)` belong to partner IDs, or to the same dummy. -/
theorem out_corr (x : X.Base) (j : TagW a) (hgood : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y)
    (k : Fin (2 ^ b)) :
    (∃ (z : SurvivingSlots.Id X.packingData.BaseMotif (SD a b)) (hm : MotifT X X' z.2.1.1.val),
      (X.shrinkStateIndex ready layout).outgoing (.inl z) = ((x, j), k) ∧
      (X'.shrinkStateIndex ready layout).outgoing (.inl (tId z hm)) = ((pb X X' x, j), k) ∧
      EndsGood X X' z.2.1.1.val) ∨
    (∃ i, (X.shrinkStateIndex ready layout).outgoing (.inr ((x, j), i)) = ((x, j), k) ∧
      (X'.shrinkStateIndex ready layout).outgoing (.inr ((pb X X' x, j), i)) = ((pb X X' x, j), k)) := by
  have he := (X.shrinkStateIndex ready layout).outgoing.apply_symm_apply ((x, j), k)
  rcases hcase : (X.shrinkStateIndex ready layout).outgoing.symm ((x, j), k) with z | ⟨b0, i⟩
  · rw [hcase] at he
    have hsrc : endpoint (X.packingData.roleBase layout) (sourceRole layout) z = (x, j) :=
      ((X.shrinkStateIndex ready layout).src_eq (.inl z)).symm.trans (congrArg Prod.fst he)
    have hz : z ∈ fib X (SD a b) layout (sourceRole layout) (x, j) :=
      (mem_fib X (SD a b) layout (sourceRole layout) _ z).mpr hsrc
    have hE : EndsGood X X' z.2.1.1.val := fib_ends X X' (SD a b) layout (sourceRole layout) x j hgood z hsrc
    have hm : MotifT X X' z.2.1.1.val := motif_tA X X' _ hE z.2.1.1.property
    refine Or.inl ⟨z, hm, he, ?_, hE⟩
    apply Prod.ext
    · rw [(X'.shrinkStateIndex ready layout).src_eq (.inl (tId z hm))]
      exact (endpoint_tId layout (sourceRole layout) z hm hE).trans (congrArg (tB X X') hsrc)
    · apply Fin.ext
      have r1 := out_rank X ready layout z
      have r2 := out_rank X' ready layout (tId z hm)
      have r3 := rank_eq X X' (SD a b) layout (sourceRole layout) x j hgood z hz hm
      rw [hsrc] at r1
      rw [endpoint_tId layout (sourceRole layout) z hm hE, hsrc] at r2
      have hk : (((X.shrinkStateIndex ready layout).outgoing (.inl z)).2 : ℕ) = k :=
        congrArg (fun p => (p.2 : ℕ)) he
      rw [r2]
      exact r3.symm.trans (r1.symm.trans hk)
  · rw [hcase] at he
    have hb0 : b0 = (x, j) :=
      ((X.shrinkStateIndex ready layout).src_eq (.inr (b0, i))).symm.trans (congrArg Prod.fst he)
    subst hb0
    refine Or.inr ⟨i, he, ?_⟩
    apply Prod.ext
    · exact (X'.shrinkStateIndex ready layout).src_eq (.inr ((pb X X' x, j), i))
    · apply Fin.ext
      have d1 := out_dummy_val X ready layout (x, j) i
      have d2 := out_dummy_val X' ready layout (pb X X' x, j) i
      have hk : (((X.shrinkStateIndex ready layout).outgoing (.inr ((x, j), i))).2 : ℕ) = k :=
        congrArg (fun p => (p.2 : ℕ)) he
      exact d2.trans (d1.symm.trans hk)

/-- The in-slot `k` at `(x, j)` and at `(pb x, j)` belong to partner IDs, or to the same dummy. -/
theorem in_corr (x : X.Base) (j : TagW a) (hgood : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y)
    (k : Fin (2 ^ b)) :
    (∃ (z : SurvivingSlots.Id X.packingData.BaseMotif (SD a b)) (hm : MotifT X X' z.2.1.1.val),
      (X.shrinkStateIndex ready layout).incoming (.inl z) = ((x, j), k) ∧
      (X'.shrinkStateIndex ready layout).incoming (.inl (tId z hm)) = ((pb X X' x, j), k) ∧
      EndsGood X X' z.2.1.1.val) ∨
    (∃ i, (X.shrinkStateIndex ready layout).incoming
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i)) = ((x, j), k) ∧
      (X'.shrinkStateIndex ready layout).incoming
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i)) =
          ((pb X X' x, j), k)) := by
  have he := (X.shrinkStateIndex ready layout).incoming.apply_symm_apply ((x, j), k)
  rcases hcase : (X.shrinkStateIndex ready layout).incoming.symm ((x, j), k) with z | ⟨b0, i⟩
  · rw [hcase] at he
    have hdst : endpoint (X.packingData.roleBase layout) (targetRole layout) z = (x, j) :=
      ((X.shrinkStateIndex ready layout).dst_eq (.inl z)).symm.trans (congrArg Prod.fst he)
    have hz : z ∈ fib X (SD a b) layout (targetRole layout) (x, j) :=
      (mem_fib X (SD a b) layout (targetRole layout) _ z).mpr hdst
    have hE : EndsGood X X' z.2.1.1.val := fib_ends X X' (SD a b) layout (targetRole layout) x j hgood z hdst
    have hm : MotifT X X' z.2.1.1.val := motif_tA X X' _ hE z.2.1.1.property
    refine Or.inl ⟨z, hm, he, ?_, hE⟩
    apply Prod.ext
    · rw [(X'.shrinkStateIndex ready layout).dst_eq (.inl (tId z hm))]
      exact (endpoint_tId layout (targetRole layout) z hm hE).trans (congrArg (tB X X') hdst)
    · apply Fin.ext
      have r1 := in_rank X ready layout z
      have r2 := in_rank X' ready layout (tId z hm)
      have r3 := rank_eq X X' (SD a b) layout (targetRole layout) x j hgood z hz hm
      rw [hdst] at r1
      rw [endpoint_tId layout (targetRole layout) z hm hE, hdst] at r2
      have hk : (((X.shrinkStateIndex ready layout).incoming (.inl z)).2 : ℕ) = k :=
        congrArg (fun p => (p.2 : ℕ)) he
      rw [r2]
      exact r3.symm.trans (r1.symm.trans hk)
  · rw [hcase] at he
    have hb0 : cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a))) b0 = (x, j) :=
      ((X.shrinkStateIndex ready layout).dst_eq (.inr (b0, i))).symm.trans (congrArg Prod.fst he)
    have hb0' : b0 = (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j) := by
      rw [← hb0, Equiv.symm_apply_apply]
    subst hb0'
    refine Or.inr ⟨i, he, ?_⟩
    apply Prod.ext
    · rw [(X'.shrinkStateIndex ready layout).dst_eq]
      exact Equiv.apply_symm_apply _ _
    · apply Fin.ext
      have d1 := in_dummy_val X ready layout ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j)) i
      have d2 := in_dummy_val X' ready layout
        ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j)) i
      have hk : (((X.shrinkStateIndex ready layout).incoming
          (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i))).2 : ℕ) = k :=
        congrArg (fun p => (p.2 : ℕ)) he
      exact d2.trans (d1.symm.trans hk)

variable (w : X.packingData.Motif → Fin 4 → ℕ) (w' : X'.packingData.Motif → Fin 4 → ℕ)

/-- Out-neighbour addresses and displacements at `(x, j)` (radius 2). -/
theorem outNbr_shrink (x : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y) :
    outNbr (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)) (x, j) =
      outNbr (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)) (pb X X' x, j) := by
  funext k
  have hxg : SGood X X' x := hgood x (by simp)
  rcases out_corr X X' ready layout x j hgood k with ⟨z, hm, h1, h2, hE⟩ | ⟨i, h1, h2⟩
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target
        ((x, j), k) = (X.shrinkStateIndex ready layout).incoming (.inl z) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inl z); rw [h1] at e; exact e
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).incoming (.inl (tId z hm)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inl (tId z hm)); rw [h2] at e; exact e
    have t2 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.displacement
        ((x, j), k) = X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) z := by
      have e := (X.shrinkStateIndex ready layout).displacement_eq (.inl z); rw [h1] at e; exact e
    have t2' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.displacement
        ((pb X X' x, j), k) =
          X'.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) (tId z hm) := by
      have e := (X'.shrinkStateIndex ready layout).displacement_eq (.inl (tId z hm)); rw [h2] at e; exact e
    have t3 : ((X.shrinkStateIndex ready layout).incoming (.inl z)).1 =
        endpoint (X.packingData.roleBase layout) (targetRole layout) z :=
      (X.shrinkStateIndex ready layout).dst_eq (.inl z)
    have t3' : ((X'.shrinkStateIndex ready layout).incoming (.inl (tId z hm))).1 =
        endpoint (X'.packingData.roleBase layout) (targetRole layout) (tId z hm) :=
      (X'.shrinkStateIndex ready layout).dst_eq (.inl (tId z hm))
    have hd : addr X' (pb X X' (endpoint (X.packingData.roleBase layout) (targetRole layout) z).1) =
        addr X (endpoint (X.packingData.roleBase layout) (targetRole layout) z).1 :=
      role_addr layout (targetRole layout z.1) z.2.1.1 hE
    simp only [outNbr]
    rw [t1, t1', t2, t2', t3, t3', endpoint_tId layout (targetRole layout) z hm hE,
      roleDisplacement_tId layout z hm hE, addr_shrinkOut, addr_shrinkOut]
    simp only [tB, hd]
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target
        ((x, j), k) = (X.shrinkStateIndex ready layout).incoming (.inr ((x, j), i)) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inr ((x, j), i)); rw [h1] at e; exact e
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).incoming (.inr ((pb X X' x, j), i)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inr ((pb X X' x, j), i)); rw [h2] at e; exact e
    have t2 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.displacement
        ((x, j), k) = 0 := by
      have e := (X.shrinkStateIndex ready layout).displacement_eq (.inr ((x, j), i)); rw [h1] at e; exact e
    have t2' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.displacement
        ((pb X X' x, j), k) = 0 := by
      have e := (X'.shrinkStateIndex ready layout).displacement_eq (.inr ((pb X X' x, j), i)); rw [h2] at e; exact e
    have t3 : ((X.shrinkStateIndex ready layout).incoming (.inr ((x, j), i))).1 =
        cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a))) (x, j) :=
      (X.shrinkStateIndex ready layout).dst_eq _
    have t3' : ((X'.shrinkStateIndex ready layout).incoming (.inr ((pb X X' x, j), i))).1 =
        cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a))) (pb X X' x, j) :=
      (X'.shrinkStateIndex ready layout).dst_eq _
    simp only [outNbr]
    rw [t1, t1', t2, t2', t3, t3', addr_shrinkOut, addr_shrinkOut]
    simp only [cycleTags_apply, hxg.addr_eq]

/-- In-neighbour addresses and displacements at `(x, j)` (radius 2). -/
theorem inNbr_shrink (x : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist x y ≤ 2 → SGood X X' y) :
    inNbr (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)) (x, j) =
      inNbr (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)) (pb X X' x, j) := by
  funext k
  have hxg : SGood X X' x := hgood x (by simp)
  rcases in_corr X X' ready layout x j hgood k with ⟨z, hm, h1, h2, hE⟩ | ⟨i, h1, h2⟩
  · have t1 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.base.target.symm
        ((x, j), k) = (X.shrinkStateIndex ready layout).outgoing (.inl z) := by
      have e := (X.shrinkStateIndex ready layout).match_eq (.inl z); rw [h1] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    have t1' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.base.target.symm
        ((pb X X' x, j), k) = (X'.shrinkStateIndex ready layout).outgoing (.inl (tId z hm)) := by
      have e := (X'.shrinkStateIndex ready layout).match_eq (.inl (tId z hm)); rw [h2] at e
      exact (Equiv.symm_apply_eq _).mpr e.symm
    have t2 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.displacement
        ((X.shrinkStateIndex ready layout).outgoing (.inl z)) =
          X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) z :=
      (X.shrinkStateIndex ready layout).displacement_eq (.inl z)
    have t2' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.displacement
        ((X'.shrinkStateIndex ready layout).outgoing (.inl (tId z hm))) =
          X'.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout) (tId z hm) :=
      (X'.shrinkStateIndex ready layout).displacement_eq (.inl (tId z hm))
    have t3 : ((X.shrinkStateIndex ready layout).outgoing (.inl z)).1 =
        endpoint (X.packingData.roleBase layout) (sourceRole layout) z :=
      (X.shrinkStateIndex ready layout).src_eq (.inl z)
    have t3' : ((X'.shrinkStateIndex ready layout).outgoing (.inl (tId z hm))).1 =
        endpoint (X'.packingData.roleBase layout) (sourceRole layout) (tId z hm) :=
      (X'.shrinkStateIndex ready layout).src_eq (.inl (tId z hm))
    have hd : addr X' (pb X X' (endpoint (X.packingData.roleBase layout) (sourceRole layout) z).1) =
        addr X (endpoint (X.packingData.roleBase layout) (sourceRole layout) z).1 :=
      role_addr layout (sourceRole layout z.1) z.2.1.1 hE
    simp only [inNbr]
    rw [t1, t1', t2, t2', t3, t3', endpoint_tId layout (sourceRole layout) z hm hE,
      roleDisplacement_tId layout z hm hE, addr_shrinkOut, addr_shrinkOut]
    simp only [tB, hd]
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
    have t2 : (X.shrinkOutputState layout (SD a b) w (X.shrinkStateIndex ready layout)).slots.displacement
        ((X.shrinkStateIndex ready layout).outgoing
          (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i))) = 0 :=
      (X.shrinkStateIndex ready layout).displacement_eq _
    have t2' : (X'.shrinkOutputState layout (SD a b) w' (X'.shrinkStateIndex ready layout)).slots.displacement
        ((X'.shrinkStateIndex ready layout).outgoing
          (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i))) = 0 :=
      (X'.shrinkStateIndex ready layout).displacement_eq _
    have t3 : ((X.shrinkStateIndex ready layout).outgoing
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j), i))).1 =
          (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (x, j) :=
      (X.shrinkStateIndex ready layout).src_eq _
    have t3' : ((X'.shrinkStateIndex ready layout).outgoing
        (.inr ((cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j), i))).1 =
          (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))).symm (pb X X' x, j) :=
      (X'.shrinkStateIndex ready layout).src_eq _
    simp only [inNbr]
    rw [t1, t1', t2, t2', t3, t3', addr_shrinkOut, addr_shrinkOut]
    simp only [cycleTags_symm_apply, hxg.addr_eq]

end Graph

end P1P7
