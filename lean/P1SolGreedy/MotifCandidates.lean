import P1SolGreedy.MotifNeighborhood

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

def arcWordKey (p : WireRadices × WireWords) : NumberWord :=
  joinWords (p.2.2.2, p.1.1, p.2.2.1)

@[fun_prop] theorem arcWordKey_poly : Poly arcWordKey := by unfold arcWordKey; fun_prop

theorem arcWordKey_code {a g : ℕ} (v : WireWords) (Y : ℕ) (k : Fin (2 ^ a))
    (w : BitWord (packingLaneBits a g)) (h : MatchesWire v (packingArcEquiv ℕ a g ((Y, k), w))) :
    P1Batch.bval (arcWordKey (wireRadices a g, v)) = keyOf a g k w := by
  have H := (matchesWire_parts _ _).mp h
  change P1Batch.bval v.1 = Y ∧ P1Batch.bval v.2.1 = k.val ∧
    P1Batch.bval v.2.2 = bwNum ((packingArcEquiv ℕ a g).symm (packingArcEquiv ℕ a g ((Y, k), w))).2 at H
  rw [Equiv.symm_apply_apply] at H
  simp only [arcWordKey, wireRadices, bval_joinWords, bval_bin, H.2.1, H.2.2, keyOf]
  rfl

def indexedWire (q : MotifContext) : WireWords :=
  let x := Carry.nat_div (q.2.2, q.2.1.1.1)
  (motifRoot q, x.2, boundWord (q.2.1.1.2.2.2.2, x.1))

@[fun_prop] theorem indexedWire_poly : Poly indexedWire := by unfold indexedWire; dsimp only; fun_prop

theorem indexedWire_code (all : Bool) (D : Dims) (ℓ a g : ℕ) (len Y key : NumberWord) :
    MatchesWire (indexedWire (activeMotif all D ℓ a g len Y key))
      (wireOf a g (P1Batch.bval Y) (P1Batch.bval key)) := by
  rw [matchesWire_parts]
  unfold wireOf
  rw [Equiv.symm_apply_apply]
  refine ⟨rfl, ?_, ?_⟩
  · change P1Batch.bval (Carry.nat_div (key, bin (2 ^ a))).2 = _
    rw [(bval_divide _ _).2, bval_bin]
    rfl
  · have H := bval_boundWord (2 ^ packingLaneBits a g) ((Carry.nat_div (key, bin (2 ^ a))).1)
    rw [(bval_divide _ _).1, bval_bin] at H
    rw [show bwNum (laneWord a g (P1Batch.bval key / 2 ^ a)) =
      (finOr0 (2 ^ packingLaneBits a g) (P1Batch.bval key / 2 ^ a)).val from
      congrArg Fin.val (Equiv.apply_symm_apply _ _)]
    exact H

def arcRoots (all : Bool) (q : MotifContext) : List WireWords :=
  if all then
    ((motifSlots q).product (wordRange q.2.1.2.2.2.2.1)).map fun p => (motifRoot q, p)
  else [indexedWire q]

@[fun_prop] theorem arcRoots_poly (all : Bool) : Poly (arcRoots all) := by
  have h := product_poly ([] : NumberWord) ([] : NumberWord)
  let addBase (p : NumberWord × (NumberWord × NumberWord)) : WireWords := p
  have hm := Poly.push ([] : NumberWord) (([], []) : NumberWord × NumberWord) (Poly.identity (X := WireWords))
  cases all
  · exact show Poly (fun q : MotifContext => [indexedWire q]) from by fun_prop
  · change Poly (fun q : MotifContext => Code.polyPush addBase
      (motifRoot q, (motifSlots q).product (wordRange q.2.1.2.2.2.2.1)))
    exact (by fun_prop : Poly (fun q : MotifContext =>
      (motifRoot q, (motifSlots q).product (wordRange q.2.1.2.2.2.2.1)))).compose hm

/-- Every slot and mask with the anchor's label, tag and residual-lane coordinates. -/
def rankWireWords (p : WireRadices × WireWords × NumberWord × NumberWord) : WireWords :=
  let f := splitLane (p.1, p.2.1.2.2)
  (p.2.1.1, p.2.2.1, joinLane (p.1, p.2.2.2, f.2))

@[fun_prop] theorem rankWireWords_poly : Poly rankWireWords := by
  unfold rankWireWords
  dsimp only
  fun_prop

theorem wireLane_code {a g : ℕ} (v : WireWords) (e : Wire ℕ a g) (hv : MatchesWire v e) :
    laneNumbers (splitLane (wireRadices a g, v.2.2)) =
      (bwNum e.2.1, bwNum e.2.2, bwNum e.1.1.2.1, bwNum e.1.1.2.2) := by
  have h := splitLane_code v.2.2 _ ((matchesWire_parts v e).mp hv).2.2
  rw [show packingFields a g ((packingArcEquiv ℕ a g).symm e).2 =
    (e.2.1, e.2.2, e.1.1.2) from (packingFields a g).apply_symm_apply _] at h
  exact h

theorem rankWireWords_code {a g : ℕ} (v : WireWords) (e : Wire ℕ a g) (hv : MatchesWire v e)
    (k m : NumberWord) (i : Fin (2 ^ a)) (w : ColorWord a)
    (hk : P1Batch.bval k = i.val) (hm : P1Batch.bval m = bwNum w) :
    MatchesWire (rankWireWords (wireRadices a g, v, k, m)) (atThin e i w) := by
  rw [matchesWire_parts]
  obtain ⟨hb, _, _⟩ := (matchesWire_parts v e).mp hv
  refine ⟨hb, hk, ?_⟩
  let f := splitLane (wireRadices a g, v.2.2)
  change P1Batch.bval (joinLane (wireRadices a g, m, f.2)) = _
  have hc := wireLane_code v e hv
  change laneNumbers f = _ at hc
  apply joinLane_code
  have hf : packingFields a g ((packingArcEquiv ℕ a g).symm (atThin e i w)).2 =
      (w, e.2.2, e.1.1.2) := (packingFields a g).apply_symm_apply _
  rw [hf]
  change (P1Batch.bval m, (laneNumbers f).2) = (bwNum w, bwNum e.2.2, bwNum e.1.1.2.1, bwNum e.1.1.2.2)
  have ht : (laneNumbers f).2 = (bwNum e.2.2, bwNum e.1.1.2.1, bwNum e.1.1.2.2) :=
    congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2) hc
  exact Prod.ext hm ht

/-- A candidate AB arc in the bundle obtained by shifting the anchor tag by the stored offset. -/
def totalWireWords (p : WireRadices × WireWords × NumberWord × NumberWord × NumberWord) : WireWords :=
  let f := splitLane (p.1, p.2.1.2.2)
  let off := boundWord (p.1.2.2.1, p.2.2.1)
  let tag := xorWords (f.2.2.1, off)
  (p.2.1.1, f.2.1, joinLane (p.1, p.2.2.2.1, p.2.2.2.2, tag, f.2.2.2))

@[fun_prop] theorem totalWireWords_poly : Poly totalWireWords := by
  unfold totalWireWords
  dsimp only
  fun_prop

def totalWire {a g : ℕ} (e : Wire ℕ a g) (off : TagWord a) (mask : ColorWord a) (label : BitWord a) :
    Wire ℕ a g :=
  (((e.1.1.1, (e.1.1.2.1 + off, e.1.1.2.2)), bitWordFinEquiv a e.2.2), mask, label)

theorem totalWireWords_code {a g : ℕ} (v : WireWords) (e : Wire ℕ a g) (hv : MatchesWire v e)
    (off mask label : NumberWord) (w : ColorWord a) (l : BitWord a)
    (hm : P1Batch.bval mask = bwNum w) (hl : P1Batch.bval label = bwNum l) :
    MatchesWire (totalWireWords (wireRadices a g, v, off, mask, label))
      (totalWire e (bwOf (packingTagBits (2 ^ a)) (P1Batch.bval off)) w l) := by
  rw [matchesWire_parts]
  obtain ⟨hb, _, _⟩ := (matchesWire_parts v e).mp hv
  let f := splitLane (wireRadices a g, v.2.2)
  have hc := wireLane_code v e hv
  change laneNumbers f = _ at hc
  have hfₛ : P1Batch.bval f.2.1 = bwNum e.2.2 := congrArg (fun m : ℕ × ℕ × ℕ × ℕ => m.2.1) hc
  refine ⟨hb, hfₛ, ?_⟩
  let δ := bwOf (packingTagBits (2 ^ a)) (P1Batch.bval off)
  let off' := boundWord (bin (2 ^ packingTagBits (2 ^ a)), off)
  let t := xorWords (f.2.2.1, off')
  change P1Batch.bval (joinLane (wireRadices a g, mask, label, t, f.2.2.2)) = _
  apply joinLane_code
  have hδ : P1Batch.bval off' = bwNum δ :=
    (bval_boundWord _ _).trans (congrArg Fin.val (Equiv.apply_symm_apply _ _)).symm
  have ht : P1Batch.bval t = bwNum (e.1.1.2.1 + δ) := by
    unfold t
    have hfT : P1Batch.bval f.2.2.1 = bwNum e.1.1.2.1 :=
      congrArg (fun m : ℕ × ℕ × ℕ × ℕ => m.2.2.1) hc
    rw [bval_xorWords, hfT, hδ]
    exact (bitWord_code_add _ _).symm
  have hf : packingFields a g ((packingArcEquiv ℕ a g).symm (totalWire e δ w l)).2 =
      (w, l, e.1.1.2.1 + δ, e.1.1.2.2) := (packingFields a g).apply_symm_apply _
  rw [hf]
  have hfL : P1Batch.bval f.2.2.2 = bwNum e.1.1.2.2 :=
    congrArg (fun m : ℕ × ℕ × ℕ × ℕ => m.2.2.2) hc
  exact Prod.ext hm (Prod.ext hl (Prod.ext ht hfL))

end P1SolGreedy.SolDemand
