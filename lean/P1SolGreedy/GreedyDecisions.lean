import P1ChkGreedy.LocalC78
import P1ChkFinal.ProgC11

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1Wit P1ChkGreedy

namespace P1SolGreedy.SolDemand

/-- A bounded least-missing test. The witness number never determines the loop length. -/
def leastMissing (cap v : ℕ) (vals : List ℕ) : Bool :=
  decide (v < cap) && !(vals.contains v) &&
    (List.range cap).all (fun k => decide (v ≤ k) || vals.contains k)

theorem leastMissing_spec (cap v : ℕ) (vals : List ℕ) :
    leastMissing cap v vals = true ↔
      v < cap ∧ v ∉ vals ∧ ∀ k < v, k ∈ vals := by
  simp only [leastMissing, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨hcap, hnot⟩, hprev⟩
    refine ⟨hcap, hnot, fun k hk => ?_⟩
    exact (hprev k (hk.trans hcap)).resolve_left (Nat.not_le_of_lt hk)
  · rintro ⟨hcap, hnot, hprev⟩
    refine ⟨⟨hcap, hnot⟩, fun k _ => ?_⟩
    rcases le_or_gt v k with h | h
    · exact Or.inl h
    · exact Or.inr (hprev k h)

theorem C5chk_decision (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    leastMissing (2 * (D.lv ℓ).slots + 1) (rdColour D u ℓ Y) (c5vals D u ℓ Y) = true ↔
      C5chk D u ℓ Y :=
  leastMissing_spec _ _ _

def tagTests (a : ℕ) : List (SlotGraph.TagTests (2 ^ a)) :=
  let slots := List.finRange (2 ^ a)
  let opts := none :: slots.map some
  let tests := opts.map Sum.inl ++ opts.flatMap (fun o₁ => opts.map fun o₂ => Sum.inr (o₁, o₂))
  [false, true].flatMap fun b => slots.flatMap fun i => tests.map fun t => ((b, i), t)

theorem mem_tagTests (a : ℕ) (t : SlotGraph.TagTests (2 ^ a)) : t ∈ tagTests a := by
  have ho (o : Option (Fin (2 ^ a))) : o ∈ none :: (List.finRange (2 ^ a)).map some := by
    cases o <;> simp
  obtain ⟨⟨b, i⟩, q⟩ := t
  unfold tagTests
  dsimp only
  refine List.mem_flatMap.mpr ⟨b, by cases b <;> simp, ?_⟩
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange _, ?_⟩
  refine List.mem_map.mpr ⟨q, ?_, rfl⟩
  apply List.mem_append.mpr
  rcases q with o | ⟨o₁, o₂⟩
  · exact Or.inl (List.mem_map.mpr ⟨o, ho o, rfl⟩)
  · exact Or.inr (List.mem_flatMap.mpr ⟨o₁, ho o₁, List.mem_map.mpr ⟨o₂, ho o₂, rfl⟩⟩)

def tagVals (a g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) : List ℕ :=
  (tagTests a).map fun t => (bitWordFinEquiv _ (forbS a g D u ℓ Y t) : ℕ)

theorem mem_tagVals (a g : ℕ) (D : Dims) (u : List Bool) (ℓ Y v : ℕ) :
    v ∈ tagVals a g D u ℓ Y ↔ ∃ t, (bitWordFinEquiv _ (forbS a g D u ℓ Y t) : ℕ) = v := by
  simp only [tagVals, List.mem_map, mem_tagTests, true_and]

theorem C6chk_decision (a g : ℕ) (D : Dims) (u : List Bool) (ℓ Y : ℕ) :
    leastMissing (2 ^ packingTagBits (2 ^ a)) (rdOffset D u ℓ Y) (tagVals a g D u ℓ Y) = true ↔
      C6chk a g D u ℓ Y := by
  simp only [leastMissing_spec, C6chk, mem_tagVals, not_exists]
  exact and_congr_right (fun _ => and_congr_left (fun _ => forall_congr' fun t => ne_comm))

section Term

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

def decideTerm (motif : Bool) (copies scale radiusNum radiusDen : ℕ)
    (term : ℕ × (Bool × Fin 4 → ℕ)) : Bool :=
  if motif then
    decide (term.1 = 1) &&
      decide (MotifAdmission.energy supplyMass term.2 * radiusDen ^ 2 ≤
        (copies * scale * radiusNum) ^ 2 * MotifAdmission.denominator supplyMass)
  else decide (term.1 = 0 ∧ ∀ j : Bool × Fin 4, term.2 j = 0)

theorem decideTerm_spec (a g : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (DW : List Bool → ℕ → ℕ → ℕ → Bool → ℕ) (Y : ℕ) (k : Fin (2 ^ a))
    (w : BitWord (packingLaneBits a g)) :
    decideTerm (decide (IsMotifAt a g D u ℓ Y k w))
      (MotifConversion.repetitions B (DW u ℓ Y (keyOf a g k w)))
      B.scale B.radius.num.natAbs B.radius.den (rawS D u ℓ Y (keyOf a g k w)) = true ↔
      C7at a g D u ℓ B DW Y k w := by
  unfold C7at decideTerm
  by_cases h : IsMotifAt a g D u ℓ Y k w
  · simp only [h, decide_true, ite_true, Bool.and_eq_true, decide_eq_true_eq,
      MotifConversion.mem_outerIndices_iff B supplyMass_pos]
    exact and_congr_right (fun _ => Iff.of_eq decide_eq_true_eq.symm)
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, decide_eq_true_eq]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Prod.ext h₁ (funext h₂)
    · intro he
      rw [he]
      exact ⟨rfl, fun _ => rfl⟩

end Term

/-- Out-of-range starts are clipped to the end of the witness before the batch. -/
def clippedReq (len start width : ℕ) : P1Batch.Req :=
  (P1ChkFinal.bin (min len start), P1ChkFinal.bin width)

theorem clippedReq_valid (len start width : ℕ) :
    P1Batch.bval (clippedReq len start width).1 ≤ len := by
  simp only [clippedReq, P1ChkFinal.bval_bin, min_le_left]

theorem fetch_clippedReq (u : List Bool) (start width : ℕ) :
    P1Batch.fetch u (clippedReq u.length start width) = (u.drop start).take width := by
  simp only [clippedReq, P1Batch.fetch, P1ChkFinal.bval_bin]
  by_cases h : start ≤ u.length
  · rw [min_eq_right h]
  · have hg : u.length ≤ start := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [min_eq_left hg, List.drop_of_length_le (Nat.le_refl _), List.drop_of_length_le hg]

end P1SolGreedy.SolDemand
