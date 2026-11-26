import P1SolGreedy.MotifTermWords
import P1SolGreedy.MotifWidthsEval

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

section At

variable (all : Bool) (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y key : NumberWord)

local notation "ctx" => (activeMotif all D ℓ a g len Y key)
local notation "bases" => (savedMotifBases ctx u)
local notation "near" => (savedMotifNear bases u)
local notation "leaf" => (savedMotifFields all near u)

theorem termValueWord_reads (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) (c : NumberWord)
    (hc : P1Batch.bval c < 9) :
    P1Batch.bval (termValueWord ((leaf, w), c)) = rdTerms D u ℓ Y' (keyOf a g k v) (P1Batch.bval c) := by
  let r := leafTermAt ((near, w), c)
  let j := Carry.born (P1Batch.bval c)
  let r' := leafTermAt ((near, w), j)
  have hr' : r' ∈ motThirdRaw all near :=
    leafWireRequest_mem all D u ℓ a g len Y key w hr
      (List.mem_append_right _ (leafTermsAt_mem near w (born_mem_wordRange hc)))
  have H (x : NumberWord) : requestNumbers (leafTermAt ((near, w), x)) =
      requestNumbers (fieldReq D (secLev ℓ .terms)
        ((Y' * (D.lv ℓ).termKeys + keyOf a g k v) * ((D.lv ℓ).termArity + 1) + P1Batch.bval x)) := by
    have hy : P1Batch.bval w.1 = Y' := ((matchesWire_parts w _).mp hw).1
    have hkey := arcWordKey_code w Y' k v hw
    have h := termRequest_value D ℓ w.1 (arcWordKey (wireRadices a g, w)) x
    rw [hy, hkey] at h
    exact h
  have he : requestNumbers r = requestNumbers r' := by
    unfold r r'
    rw [H c, H j, bval_born]
  exact cacheRead_field' D u _ _ _ r ⟨r', hr', he⟩ (H c)

theorem termField_reads (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) (l : Bool)
    (j : Fin 4) :
    P1Batch.bval (termValueWord ((leaf, w), termIndexWord (l, Carry.born j.val))) =
      (rawS D u ℓ Y' (keyOf a g k v)).2 (l, j) := by
  have h : P1Batch.bval (termIndexWord (l, Carry.born j.val)) = 1 + termIdx (l, j) := by
    rw [termIndexWord_value, bval_born, termIdx, Nat.add_assoc]
  have hc : P1Batch.bval (termIndexWord (l, Carry.born j.val)) < 9 := by
    rw [h, termIdx]
    have hj := j.isLt
    cases l <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [termValueWord_reads all D u ℓ a g len Y key w Y' k v hw hr _ hc, h]
  rfl

theorem termFlag_reads (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) :
    P1Batch.bval (termValueWord ((leaf, w), [])) = (rawS D u ℓ Y' (keyOf a g k v)).1 :=
  termValueWord_reads all D u ℓ a g len Y key w Y' k v hw hr [] (by decide)

theorem termGroup_reads (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) (l : Bool) :
    P1Batch.bval (termGroup l (leaf, w)) =
      ∑ j : Fin 4, MotifAdmission.weight supplyMass (l, j) * (rawS D u ℓ Y' (keyOf a g k v)).2 (l, j) ^ 2 := by
  unfold termGroup
  rw [bval_sumPush, sumWordRange]
  refine Finset.sum_congr rfl fun j _ => ?_
  change P1Batch.bval (weightedSquare (selectRow [] (Carry.born j.val, termWeightTable l),
    termValueWord ((leaf, w), termIndexWord (l, Carry.born j.val)))) = _
  rw [weightedSquare_value, termField_reads all D u ℓ a g len Y key w Y' k v hw hr l j]
  unfold termWeightTable
  rw [selectRow_table, bval_born, ite_eq_left j.isLt, finOr0_fin, bval_bin]

theorem zeroTerm_iff (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) :
    zeroTerm (leaf, w) = true ↔
      (rawS D u ℓ Y' (keyOf a g k v)).1 = 0 ∧ ∀ j, (rawS D u ℓ Y' (keyOf a g k v)).2 j = 0 := by
  unfold zeroTerm
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hasTrue_spec]
  simp only [Code.polyPush, List.mem_map, not_exists, not_and, nonzeroTerm,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, numberEq_spec, not_not]
  have H (c : NumberWord) (hc : c ∈ wordRange (tally 9)) :
    P1Batch.bval (termValueWord ((leaf, w), c)) = rdTerms D u ℓ Y' (keyOf a g k v) (P1Batch.bval c) := by
    rw [wordRange_tally, List.mem_map] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact termValueWord_reads all D u ℓ a g len Y key w Y' k v hw hr _ (by rw [bval_born]; exact List.mem_range.mp hi)
  change (∀ c ∈ wordRange (tally 9), P1Batch.bval (termValueWord ((leaf, w), c)) = 0) ↔ _
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hm := born_mem_wordRange (by decide : 0 < 9)
      have hs := H (Carry.born 0) hm
      rw [bval_born] at hs
      exact hs.symm.trans (h (Carry.born 0) hm)
    · rintro ⟨l, j⟩
      let i := 1 + termIdx (l, j)
      have hi : i < 9 := by
        have hj := j.isLt
        cases l
        · change 1 + (0 + j.val) < 9
          omega
        · change 1 + (4 + j.val) < 9
          omega
      have hh := (H _ (born_mem_wordRange hi)).symm.trans (h _ (born_mem_wordRange hi))
      change rdTerms D u ℓ Y' (keyOf a g k v) (P1Batch.bval (Carry.born i)) = 0 at hh
      rw [bval_born] at hh
      exact hh
  · rintro ⟨hf, hv⟩ c hc
    rw [H c hc]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (wordRange_tally 9 ▸ hc)
    rw [bval_born]
    have hi' := List.mem_range.mp hi
    by_cases h0 : i = 0
    · rw [h0]
      exact hf
    · by_cases h4 : i ≤ 4
      · let j : Fin 4 := ⟨i - 1, by omega⟩
        have he : i = 1 + termIdx (false, j) := by change i = 1 + (0 + (i - 1)); omega
        rw [he]
        exact hv (false, j)
      · let j : Fin 4 := ⟨i - 5, by omega⟩
        have he : i = 1 + termIdx (true, j) := by change i = 1 + (4 + (i - 5)); omega
        rw [he]
        exact hv (true, j)

section Block

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

local notation "storedDW" => (DWLocal (a := a) (g := g) (D := D))

theorem copiesWords_reads (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) :
    P1Batch.bval (copiesWords B.scale (wordDemand (leaf, w))) =
      MotifConversion.repetitions B (storedDW u ℓ Y' (keyOf a g k v)) := by
  apply copiesWords_value
  unfold DWLocal
  rw [wireOf_keyOf]
  exact wordDemand_reads all D u ℓ a g len Y key w _ hw hr

set_option maxHeartbeats 750000 in
theorem validTermWords_iff (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) :
    validTermWords B.scale B.radius.num.natAbs B.radius.den (leaf, w) = true ↔
      (rawS D u ℓ Y' (keyOf a g k v)).1 = 1 ∧
      MotifAdmission.energy supplyMass (rawS D u ℓ Y' (keyOf a g k v)).2 * B.radius.den ^ 2 ≤
        (MotifConversion.repetitions B (storedDW u ℓ Y' (keyOf a g k v)) * B.scale * B.radius.num.natAbs) ^ 2 *
          MotifAdmission.denominator supplyMass := by
  unfold validTermWords bitAnd
  dsimp only
  rw [Bool.and_eq_true, numberEq_spec]
  simp only [Bool.not_eq_true', less_spec, decide_eq_false_iff_not, Nat.not_lt]
  change (P1Batch.bval (termValueWord ((leaf, w), [])) = 1 ∧ _) ↔ _
  rw [termFlag_reads all D u ℓ a g len Y key w Y' k v hw hr, bval_mul, weightedSquare_value, bval_mul,
    bval_add, bval_bin, bval_bin, bval_bin, termGroup_reads all D u ℓ a g len Y key w Y' k v hw hr false,
    termGroup_reads all D u ℓ a g len Y key w Y' k v hw hr true,
    copiesWords_reads all D u ℓ a g len Y key B w Y' k v hw hr,
    MotifAdmission.energy, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Nat.mul_comm (MotifAdmission.denominator supplyMass), ← Nat.mul_assoc]
  rw [Nat.add_comm (∑ j : Fin 4, MotifAdmission.weight supplyMass (false, j) * (rawS D u ℓ Y' (keyOf a g k v)).2 (false, j) ^ 2)]

open Classical in
set_option maxHeartbeats 900000 in
theorem decideTermWords_correct (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y key : NumberWord) :
    decideTermWords B.scale B.radius.num.natAbs B.radius.den
      (savedMotifFields false (savedMotifNear (savedMotifBases (activeMotif false D ℓ a g len Y key) u) u) u) =
      true ↔ C7key B a g D u ℓ (P1Batch.bval Y) (P1Batch.bval key) := by
  let q := activeMotif false D ℓ a g len Y key
  let s := savedMotifNear (savedMotifBases q u) u
  let f := savedMotifFields false s u
  let w := indexedWire q
  let k : Fin (2 ^ a) := ⟨P1Batch.bval key % (2 ^ a), Nat.mod_lt _ (Nat.two_pow_pos a)⟩
  let v := laneWord a g (P1Batch.bval key / (2 ^ a))
  have hw : MatchesWire w (packingArcEquiv ℕ a g ((P1Batch.bval Y, k), v)) :=
    indexedWire_code false D ℓ a g len Y key
  have hr : w ∈ arcRoots false q := List.mem_cons_self
  have hM := wordMotif_iff false D u ℓ a g len Y key w _ k v hw hr
  have hV := validTermWords_iff false D u ℓ a g len Y key B w _ k v hw hr
  have hZ := zeroTerm_iff false D u ℓ a g len Y key w _ k v hw hr
  change (bif wordMotif (f, w) then validTermWords B.scale B.radius.num.natAbs B.radius.den (f, w)
    else zeroTerm (f, w)) = true ↔ C7at a g D u ℓ B (DWLocal (a := a) (g := g) (D := D)) (P1Batch.bval Y) k v
  rw [← decideTerm_spec B]
  unfold decideTerm
  by_cases h : IsMotifAt a g D u ℓ (P1Batch.bval Y) k v
  · rw [hM.mpr h, Bool.cond_true]
    simp only [h, decide_true, ite_true, Bool.and_eq_true, decide_eq_true_eq]
    exact hV
  · have hb : wordMotif (f, w) = false := Bool.eq_false_iff.mpr (fun hh => h (hM.mp hh))
    rw [hb, Bool.cond_false]
    simp only [h, decide_false, Bool.false_eq_true, ite_false, decide_eq_true_eq]
    exact hZ

end Block
end At

end P1SolGreedy.SolDemand
