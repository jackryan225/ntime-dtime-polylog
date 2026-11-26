import P1SolGreedy.MotifLeaf

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal P1ChkGreedy

namespace P1SolGreedy.SolDemand

/-- Every request width comes from a section of the public format row. -/
def RowWidths (row : BaseRow) (rs : List P1Batch.Req) : Prop :=
  ∀ r ∈ rs, ∃ c : Mem, r.2 = (rowSection c row).2

theorem rowWidths_nil (row : BaseRow) : RowWidths row [] := fun _ h => (List.not_mem_nil h).elim

theorem rowWidths_append {row : BaseRow} {a b : List P1Batch.Req}
    (ha : RowWidths row a) (hb : RowWidths row b) : RowWidths row (a ++ b) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact ha r h
  · exact hb r h

theorem rowWidths_cons {row : BaseRow} {r : P1Batch.Req} {rs : List P1Batch.Req} {c : Mem}
    (h : r.2 = (rowSection c row).2) (hs : RowWidths row rs) : RowWidths row (r :: rs) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hm
  · exact ⟨c, h⟩
  · exact hs q hm

theorem rowWidths_map {T : Type} (row : BaseRow) (xs : List T) (f : T → P1Batch.Req) (c : Mem)
    (h : ∀ x ∈ xs, (f x).2 = (rowSection c row).2) : RowWidths row (xs.map f) := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact ⟨c, h x hx⟩

theorem rowWidths_flatMap {T : Type} (row : BaseRow) (xs : List T) (f : T → List P1Batch.Req)
    (h : ∀ x ∈ xs, RowWidths row (f x)) : RowWidths row (xs.flatMap f) := by
  intro r hr
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.mp hr
  exact h x hx r hm

theorem rowWidths_slots (row : BaseRow) (y : NumberWord) (ks : List NumberWord) (c : Mem) :
    RowWidths row (slotsAt c (row, y, ks)) := by
  rw [slotsAt_eq]
  exact rowWidths_map row ks _ c (fun _ _ => rfl)

theorem rowWidths_addrRaw (p : MotifContext × NumberWord) :
    RowWidths (motifLevel p.1) (addrRaw p) := by
  unfold addrRaw
  exact rowWidths_append (rowWidths_slots _ _ _ .outAddr) (rowWidths_slots _ _ _ .inAddr)

theorem rowWidths_first (q : MotifContext) : RowWidths (motifLevel q) (motFirstRaw q) := by
  unfold motFirstRaw
  cases q.1.2.1
  · exact rowWidths_nil _
  · exact rowWidths_addrRaw (q, motifRoot q)

theorem rowWidths_panelRaw (p : MotifContext × NumberWord) :
    RowWidths (motifLevel p.1) (neighborPanelRaw p) := by
  unfold neighborPanelRaw
  apply rowWidths_cons (c := .offset) (r := offsetAt (motifLevel p.1, p.2)) rfl
  exact rowWidths_append (rowWidths_append (rowWidths_append
    (rowWidths_append (rowWidths_addrRaw p) (rowWidths_slots _ _ _ .outFar))
    (rowWidths_slots _ _ _ .inFar)) (rowWidths_slots _ _ _ .outDisp)) (rowWidths_slots _ _ _ .inDisp)

theorem rowWidths_second (p : MotifBases) : RowWidths (motifLevel p.1) (motSecondRaw p) :=
  rowWidths_flatMap _ p.2 (fun Z => neighborPanelRaw (p.1, Z)) (fun Z _ => rowWidths_panelRaw (p.1, Z))

theorem rowWidths_leafColours (s : MotifNear) :
    RowWidths (motifLevel (nearContext s)) (leafColours s) := by
  apply rowWidths_flatMap _ s.1.2 (fun Z => leafColourAt (s, Z))
  intro Z _
  apply rowWidths_map (c := .colour)
  intro z _
  rfl

theorem rowWidths_bundleCosts (s : MotifNear) (w : WireWords) :
    RowWidths (motifLevel (nearContext s)) (bundleCostsAt (s, w)) := by
  unfold bundleCostsAt Code.polyPush
  dsimp only
  apply rowWidths_map (c := .width)
  intro z _
  rfl

theorem rowWidths_wire (p : MotifNear × WireWords) :
    RowWidths (motifLevel (nearContext p.1)) (leafWireFields p) := by
  refine rowWidths_append ?_ ?_
  · unfold leafWidthsAt
    exact rowWidths_cons (c := .width) rfl
      (rowWidths_append (rowWidths_bundleCosts p.1 p.2) (rowWidths_bundleCosts p.1 (nearHop true p)))
  · unfold leafTermsAt Code.polyPush
    exact rowWidths_map _ _ _ .terms (fun _ _ => rfl)

theorem rowWidths_leafWires (all : Bool) (s : MotifNear) :
    RowWidths (motifLevel (nearContext s)) (leafWires all s) :=
  rowWidths_flatMap _ (arcRoots all (nearContext s)) (fun w => leafWireFields (s, w))
    (fun w _ => rowWidths_wire (s, w))

theorem rowWidths_leafEnergies (q : MotifContext) : RowWidths (motifLevel q) (leafEnergies q) := by
  unfold leafEnergies
  exact rowWidths_cons (c := .energy) rfl (rowWidths_cons (c := .energy) rfl
    (rowWidths_cons (c := .energy) rfl (rowWidths_cons (c := .energy) rfl (rowWidths_nil _))))

theorem rowWidths_third (all : Bool) (s : MotifNear) :
    RowWidths (motifLevel (nearContext s)) (motThirdRaw all s) := by
  unfold motThirdRaw
  dsimp only
  cases (nearContext s).1.2.1
  · exact rowWidths_nil _
  · apply rowWidths_append (rowWidths_append (rowWidths_leafColours s) (rowWidths_leafWires all s))
    cases all
    · exact rowWidths_nil _
    · exact rowWidths_leafEnergies _

theorem rowWidths_clip (row : BaseRow) (len : NumberWord) (rs : List P1Batch.Req)
    (h : RowWidths row rs) : RowWidths row (clipRequests (len, rs)) := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact h r hr

theorem rowWidths_le (D : Dims) (ℓ : ℕ) (rs : List P1Batch.Req) (h : RowWidths (levelRow D ℓ) rs) :
    ∀ r ∈ rs, P1Batch.bval r.2 ≤ size (levelRow D ℓ) := by
  intro r hr
  obtain ⟨c, hc⟩ := h r hr
  rw [hc, rowSection_levelRow, bval_bin]
  exact width_le_size_levelRow D ℓ c

theorem rowWidths_default (rs : List P1Batch.Req) (h : RowWidths defaultRow rs) :
    ∀ r ∈ rs, P1Batch.bval r.2 ≤ size defaultRow := by
  intro r hr
  obtain ⟨c, hc⟩ := h r hr
  rw [hc]
  cases c <;> exact Nat.zero_le _

theorem total_of_boundedRequests {S : Type} [Codec S] {X : Type} (σ : X → ℕ) (state : X → S)
    (row : X → BaseRow) (rq : S → List P1Batch.Req) (hp : Poly rq) (hs : Dom σ (fun p => size (state p)))
    (hr : Dom σ (fun p => size (row p)))
    (hW : ∀ p, ∀ r ∈ rq (state p), P1Batch.bval r.2 ≤ size (row p)) :
    Dom σ (fun p => P1Batch.total (rq (state p))) :=
  ((hp.length.map state |>.sub hs).mul hr).mono fun p =>
    (total_le_of_width_le _ _ (hW p)).trans (Nat.mul_le_mul_right _ (length_le_size _))

set_option maxHeartbeats 600000 in
theorem setupMotif_level (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    motifLevel (setupMotif all (motifFormat all D M ag, i)) =
      let ℓ := P1Batch.bval i % 2 ^ levBits D
      if ℓ ≤ D.top then levelRow D ℓ else defaultRow := by
  change selectRow defaultRow ((Carry.nat_div (i, bin (2 ^ levBits D))).2, (fmtGreedy D M).2.2) = _
  rw [selectRow_level, (bval_divide _ _).2, bval_bin]

theorem setupMotif_widths_le (all : Bool) (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord)
    (rs : List P1Batch.Req)
    (h : RowWidths (motifLevel (setupMotif all (motifFormat all D M ag, i))) rs) :
    ∀ r ∈ rs, P1Batch.bval r.2 ≤ size (motifLevel (setupMotif all (motifFormat all D M ag, i))) := by
  rw [setupMotif_level] at h ⊢
  dsimp only at *
  split_ifs at h ⊢
  · exact rowWidths_le D _ rs h
  · exact rowWidths_default rs h

end P1SolGreedy.SolDemand
