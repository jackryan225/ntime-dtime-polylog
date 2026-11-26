import P1P7.ShrinkIds

/-!
# P7, shrink half, layer 3: fibres of the new slot graph and equality of slot numbers

* `role_ends`: the two ends of the old wire of a motif lie within distance 2 of each of its three role bases.
* `role_addr`: the partner of a role base has the same address (when both wire ends are good).
* `fib`: the lane-zero IDs with a given role at a packed base; `card_fib` (OpenAI's uniform count).
* `out_rank`, `in_rank`: OpenAI's slot numbers (`paddedSlot_numbers`) as ranks of `okey` in a fibre.
* `rank_eq`: if every base within distance 2 of `v` is good, the rank of an ID in the fibre at `(v, j)` equals the
  rank of its partner in the fibre at `(pb v, j)`.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBaseFib {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

/-! ## Distances inside one motif -/

section Dist

variable {a G : ℕ}

theorem edist_target_le (X : State a G) (y : X.Base) (k : Fin (2 ^ a)) :
    (baseGraph X).edist y (X.slots.base.target (y, k)).1 ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  left
  rw [baseGraph, SimpleGraph.fromRel_adj]
  exact ⟨fun h => X.slots.base.ends_ne (y, k) h.symm, Or.inl ⟨k, rfl⟩⟩

theorem edist_le_two {X : State a G} {u v w : X.Base} (h1 : (baseGraph X).edist u v ≤ 1)
    (h2 : (baseGraph X).edist v w ≤ 1) : (baseGraph X).edist u w ≤ 2 :=
  (SimpleGraph.edist_triangle (v := v)).trans ((add_le_add h1 h2).trans_eq one_add_one_eq_two)

variable {g : ℕ} (X : State a (packingLaneBits a g))

theorem C_base (m : X.packingData.Motif) :
    (X.packingData.C m).1.1 = m.val.1.1.1 ∨
      (X.packingData.C m).1.1 = (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 := by
  unfold PackingData.C
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem D_base (m : X.packingData.Motif) :
    (X.packingData.D m).1.1 = m.val.1.1.1 ∨
      (X.packingData.D m).1.1 = (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 := by
  unfold PackingData.D
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ends_of_base (m : X.packingData.Motif) {w : X.Base}
    (hw : w = m.val.1.1.1 ∨ w = (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1) :
    (baseGraph X).edist w m.val.1.1.1 ≤ 1 ∧
      (baseGraph X).edist w (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 ≤ 1 := by
  have hy := edist_target_le X m.val.1.1.1 m.val.1.2
  rcases hw with rfl | rfl
  · exact ⟨by simp, hy⟩
  · exact ⟨by rw [SimpleGraph.edist_comm]; exact hy, by simp⟩

/-- Both ends of the old wire are within distance 2 of every role base of the motif. -/
theorem role_ends (layout : Bool) (r : PackedRole) (m : X.packingData.Motif) :
    (baseGraph X).edist (X.packingData.survivingRole layout r m).1 m.val.1.1.1 ≤ 2 ∧
      (baseGraph X).edist (X.packingData.survivingRole layout r m).1
        (X.slots.base.target (m.val.1.1.1, m.val.1.2)).1 ≤ 2 := by
  obtain ⟨hC1, hC2⟩ := ends_of_base X m (C_base X m)
  obtain ⟨hD1, hD2⟩ := ends_of_base X m (D_base X m)
  have le12 : ∀ {u v : X.Base}, (baseGraph X).edist u v ≤ 1 → (baseGraph X).edist u v ≤ 2 :=
    fun h => h.trans one_le_two
  cases r
  · exact ⟨le12 hC1, le12 hC2⟩
  · have hB : (baseGraph X).edist (X.slots.base.target ((X.packingData.C m).1.1,
        X.packingData.slotLabel (X.packingData.C m).2.2)).1 (X.packingData.C m).1.1 ≤ 1 := by
      rw [SimpleGraph.edist_comm]; exact edist_target_le X _ _
    exact ⟨edist_le_two hB hC1, edist_le_two hB hC2⟩
  · have hD : (baseGraph X).edist (X.packingData.placement layout (X.packingData.D m)).1
        (X.packingData.D m).1.1 ≤ 1 := by
      unfold PackingData.placement
      split_ifs
      · simp
      · rw [SimpleGraph.edist_comm]
        exact edist_target_le X (X.packingData.D m).1.1 (X.packingData.slotLabel (X.packingData.D m).2.2)
      · show (baseGraph X).edist (X.packingData.D m).1.1 (X.packingData.D m).1.1 ≤ 1
        simp
    exact ⟨edist_le_two hD hD1, edist_le_two hD hD2⟩

/-- The partner of a role base has the same address. -/
theorem role_addr {X X' : State a (packingLaneBits a g)} (layout : Bool) (r : PackedRole)
    (m : X.packingData.Motif) (h : EndsGood X X' m.val) :
    addr X' (pb X X' (X.packingData.survivingRole layout r m).1) =
      addr X (X.packingData.survivingRole layout r m).1 := by
  cases r
  · exact (C_good m h).addr_eq
  · exact (C_good m h).tgt_addr (X.packingData.slotLabel (X.packingData.C m).2.2)
  · show addr X' (pb X X' (X.packingData.placement layout (X.packingData.D m)).1) =
      addr X (X.packingData.placement layout (X.packingData.D m)).1
    unfold PackingData.placement
    split_ifs
    · exact (D_good m h).addr_eq
    · exact (D_good m h).tgt_addr (X.packingData.slotLabel (X.packingData.D m).2.2)
    · exact (D_good m h).addr_eq

end Dist

/-! ## Fibres and ranks -/

section Fiber

variable {a b g : ℕ} {δ : ℝ}

/-- OpenAI's subdivision counts of a shrinking substep. -/
noncomputable abbrev SD (a b : ℕ) : Fin 4 → ℕ := subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)

/-- The lane-zero IDs whose `pick` role sits at the packed base `v`. -/
noncomputable def fib (X : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) (layout : Bool)
    (pick : Fin 4 → PackedRole) (v : X.Base × TagW a) :
    Finset (SurvivingSlots.Id X.packingData.BaseMotif sd) :=
  Finset.univ.filter (fun z => endpoint (X.packingData.roleBase layout) pick z = v)

theorem mem_fib (X : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) (layout : Bool)
    (pick : Fin 4 → PackedRole) (v : X.Base × TagW a) (z : SurvivingSlots.Id X.packingData.BaseMotif sd) :
    z ∈ fib X sd layout pick v ↔ endpoint (X.packingData.roleBase layout) pick z = v := by
  simp [fib]

theorem card_fib (X : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) (layout : Bool)
    (pick : Fin 4 → PackedRole) (v : X.Base × TagW a) :
    (fib X sd layout pick v).card =
      2 ^ a * (3 * (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) / 4) * ∑ t, sd t := by
  unfold fib
  rw [← Fintype.card_subtype]
  exact card_endpoint _ _ _ (X.packingData.card_roleBase (State.two_le_packingColors a) layout) v

/-- OpenAI's outgoing slot number of a genuine ID is its `okey`-rank among the IDs with the same source. -/
theorem out_rank (X : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (z : SurvivingSlots.Id X.packingData.BaseMotif (SD a b)) :
    (((X.shrinkStateIndex ready layout).outgoing (.inl z)).2 : ℕ) =
      ((fib X (SD a b) layout (sourceRole layout)
        (endpoint (X.packingData.roleBase layout) (sourceRole layout) z)).filter
          (fun z2 => okey (SD a b) X z2 < okey (SD a b) X z)).card := by
  letI := X.packingData.slotIdentifierOrder X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) (SD a b)
  have hJ : 1 < 2 ^ packingTagBits (2 ^ a) := Nat.one_lt_two_pow (Nat.succ_pos _).ne'
  have hn := paddedSlot_numbers (endpoint (X.packingData.roleBase layout) (sourceRole layout))
    (endpoint (X.packingData.roleBase layout) (targetRole layout))
    (X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout))
    (fun i ↦ (X.packingData.survivingSlot_bases_ne (orderedDyadicPacking_validTags X.slots X.baseIndex)
      layout (subdiv := SD a b) ⟨i.1, i.2.1.1, i.2.2⟩).symm)
    (card_endpoint _ _ (SD a b) (X.packingData.card_roleBase (State.two_le_packingColors a) layout))
    (card_endpoint _ _ (SD a b) (X.packingData.card_roleBase (State.two_le_packingColors a) layout))
    ready.degree_budget (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))) (cycleTags_ne _ hJ) z
    (fib X (SD a b) layout (sourceRole layout) (endpoint (X.packingData.roleBase layout) (sourceRole layout) z))
    (fib X (SD a b) layout (targetRole layout) (endpoint (X.packingData.roleBase layout) (targetRole layout) z))
    (fun z2 => mem_fib X (SD a b) layout (sourceRole layout) _ z2)
    (fun z2 => mem_fib X (SD a b) layout (targetRole layout) _ z2)
  refine hn.1.trans ?_
  congr 1
  apply Finset.filter_congr
  intro z2 _
  exact id_lt_iff (SD a b) X z2 z

/-- OpenAI's incoming slot number of a genuine ID is its `okey`-rank among the IDs with the same target. -/
theorem in_rank (X : State a (packingLaneBits a g)) (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (z : SurvivingSlots.Id X.packingData.BaseMotif (SD a b)) :
    (((X.shrinkStateIndex ready layout).incoming (.inl z)).2 : ℕ) =
      ((fib X (SD a b) layout (targetRole layout)
        (endpoint (X.packingData.roleBase layout) (targetRole layout) z)).filter
          (fun z2 => okey (SD a b) X z2 < okey (SD a b) X z)).card := by
  letI := X.packingData.slotIdentifierOrder X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) (SD a b)
  have hJ : 1 < 2 ^ packingTagBits (2 ^ a) := Nat.one_lt_two_pow (Nat.succ_pos _).ne'
  have hn := paddedSlot_numbers (endpoint (X.packingData.roleBase layout) (sourceRole layout))
    (endpoint (X.packingData.roleBase layout) (targetRole layout))
    (X.packingData.roleDisplacement layout (sourceRole layout) (targetRole layout))
    (fun i ↦ (X.packingData.survivingSlot_bases_ne (orderedDyadicPacking_validTags X.slots X.baseIndex)
      layout (subdiv := SD a b) ⟨i.1, i.2.1.1, i.2.2⟩).symm)
    (card_endpoint _ _ (SD a b) (X.packingData.card_roleBase (State.two_le_packingColors a) layout))
    (card_endpoint _ _ (SD a b) (X.packingData.card_roleBase (State.two_le_packingColors a) layout))
    ready.degree_budget (cycleTags (bitWordFinEquiv (packingTagBits (2 ^ a)))) (cycleTags_ne _ hJ) z
    (fib X (SD a b) layout (sourceRole layout) (endpoint (X.packingData.roleBase layout) (sourceRole layout) z))
    (fib X (SD a b) layout (targetRole layout) (endpoint (X.packingData.roleBase layout) (targetRole layout) z))
    (fun z2 => mem_fib X (SD a b) layout (sourceRole layout) _ z2)
    (fun z2 => mem_fib X (SD a b) layout (targetRole layout) _ z2)
  refine hn.2.trans ?_
  congr 1
  apply Finset.filter_congr
  intro z2 _
  exact id_lt_iff (SD a b) X z2 z

/-- Ranks in a fibre are transported to the partner fibre when every base within distance 2 of the centre is good. -/
theorem rank_eq (X X' : State a (packingLaneBits a g)) (sd : Fin 4 → ℕ) (layout : Bool)
    (pick : Fin 4 → PackedRole) (v : X.Base) (j : TagW a)
    (hgood : ∀ y, (baseGraph X).edist v y ≤ 2 → SGood X X' y)
    (z : SurvivingSlots.Id X.packingData.BaseMotif sd) (hz : z ∈ fib X sd layout pick (v, j))
    (hm : MotifT X X' z.2.1.1.val) :
    ((fib X sd layout pick (v, j)).filter (fun z2 => okey sd X z2 < okey sd X z)).card =
      ((fib X' sd layout pick (pb X X' v, j)).filter
        (fun z2 => okey sd X' z2 < okey sd X' (tId z hm))).card := by
  have ends : ∀ z2 ∈ fib X sd layout pick (v, j), EndsGood X X' z2.2.1.1.val := by
    intro z2 hz2
    have hv : (X.packingData.survivingRole layout (pick z2.1) z2.2.1.1).1 = v :=
      congrArg Prod.fst ((mem_fib X sd layout pick _ z2).mp hz2)
    obtain ⟨h1, h2⟩ := role_ends X layout (pick z2.1) z2.2.1.1
    rw [hv] at h1 h2
    exact ⟨hgood _ h1, hgood _ h2⟩
  rw [okey_tId sd z hm (ends z hz).1.addr_eq]
  refine rank_transport _ _ _ _ (okey_injective sd X).injOn (okey_injective sd X').injOn ?_ ?_ _
  · exact le_of_eq ((card_fib X' sd layout pick _).trans (card_fib X sd layout pick _).symm)
  · intro z2 hz2
    have he := ends z2 hz2
    refine ⟨tId z2 (motif_tA X X' z2.2.1.1.val he z2.2.1.1.property), ?_, okey_tId sd z2 _ he.1.addr_eq⟩
    rw [mem_fib, endpoint_tId layout pick z2 _ he, (mem_fib X sd layout pick _ z2).mp hz2] <;> rfl

end Fiber

end P1P7
