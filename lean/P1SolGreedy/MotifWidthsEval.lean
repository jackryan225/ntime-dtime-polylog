import P1SolGreedy.MotifReadCorrect

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
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

theorem thinSelect_code (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (hb : w.1 ∈ bases.2) :
    MatchesWire (wordThin (leaf, w)) (thinWire D u ℓ e) := by
  unfold wordThin thinWire
  change MatchesWire (bif wordThick (leaf, w) then nearHop true (near, w) else w) _
  rw [wordThick_here all D u ℓ a g len Y key w e hw hb]
  by_cases H : sThick D u ℓ e
  · rw [decide_eq_true H, Bool.cond_true, ite_eq_left H]
    exact nearHop_code all D u ℓ a g len Y key w e hw hb true
  · rw [decide_eq_false H, Bool.cond_false, ite_eq_right H]
    exact hw

theorem thin_base_mem (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (hr : w ∈ arcRoots all ctx) :
    (wordThin (leaf, w)).1 ∈ bases.2 := by
  have hy := rootWire_base all D ℓ a g len Y key w hr
  have hb : w.1 ∈ bases.2 := hy.symm ▸ root_base_mem all D u ℓ a g len Y key
  unfold wordThin
  change (bif wordThick (leaf, w) then nearHop true (near, w) else w).1 ∈ bases.2
  cases wordThick (leaf, w)
  · exact hb
  · have hk : P1Batch.bval w.2.1 < 2 ^ a := ((matchesWire_parts w e).mp hw).2.1.symm ▸ e.1.2.isLt
    exact root_hop_base_mem all D u ℓ a g len Y key w hy hk true

theorem bundleWidthRequest_mem (w : WireWords) (hr : w ∈ arcRoots all ctx) (m j : NumberWord)
    (hm : m ∈ motifMasks ctx) (hj : j ∈ motifSlots ctx) :
    nearWidthRequest (near, bundleAB (near, wordThin (leaf, w), m, j)) ∈ motThirdRaw all near := by
  apply leafWireRequest_mem all D u ℓ a g len Y key w hr
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  change nearWidthRequest (near, bundleAB (near, (bif wordThick (leaf, w) then nearHop true (near, w) else w),
    m, j)) ∈ bundleCostsAt (near, w) ++ bundleCostsAt (near, nearHop true (near, w))
  cases wordThick (leaf, w)
  · exact List.mem_append_left _ (bundleCostsAt_mem _ _ hm hj)
  · exact List.mem_append_right _ (bundleCostsAt_mem _ _ hm hj)

theorem isMotifAt_thick (D : Dims) (u : List Bool) (ℓ a g Y : ℕ)
    (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g)) :
    IsMotifAt a g D u ℓ Y k v ↔
      ¬ (sThick D u ℓ (packingArcEquiv ℕ a g ((Y, k), v)) ∧
        sThick D u ℓ (sOut a g D u ℓ (packingArcEquiv ℕ a g ((Y, k), v)))) := by
  unfold IsMotifAt sThick sOut laneWord
  dsimp only
  rw [Equiv.symm_apply_apply]
  let x := bwOf (packingLaneBits a g) (rdOutDisp D u ℓ Y k)
  let c := colS a D u ℓ (rdOutAddr D u ℓ Y k)
  change (¬ ((packingFields a g v).1 (colS a D u ℓ Y) = 1 ∧
      ((packingFields a g v).1 + (packingFields a g x).1) c = 1)) ↔
    (¬ ((packingFields a g v).1 (colS a D u ℓ Y) = 1 ∧ (packingFields a g (v + x)).1 c = 1))
  have h : (packingFields a g (v + x)).1 = (packingFields a g v).1 + (packingFields a g x).1 := by
    rw [map_add]
    rfl
  rw [h]

set_option maxHeartbeats 600000 in
theorem wordMotif_iff (w : WireWords) (Y' : ℕ) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((Y', k), v))) (hr : w ∈ arcRoots all ctx) :
    wordMotif (leaf, w) = true ↔ IsMotifAt a g D u ℓ Y' k v := by
  let e := packingArcEquiv ℕ a g ((Y', k), v)
  have hy := rootWire_base all D ℓ a g len Y key w hr
  have hb : w.1 ∈ bases.2 := hy.symm ▸ root_base_mem all D u ℓ a g len Y key
  have ha := wordThick_here all D u ℓ a g len Y key w e hw hb
  have hz := wordThick_hop all D u ℓ a g len Y key w e hw hb true
  change wordThick (leaf, nearHop true (near, w)) = decide (sThick D u ℓ (sOut a g D u ℓ e)) at hz
  change bitNand (wordThick (leaf, w), wordThick (leaf, nearHop true (near, w))) = true ↔ _
  rw [ha, hz, isMotifAt_thick]
  unfold bitNand
  dsimp only
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  rfl

theorem flagsCount_value (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] :
    P1Batch.bval (flagsCount (!decide p, decide q, decide r, decide s)) =
      (if ¬ p ∧ q then 1 else 0) + (if r ∧ ¬ p ∧ s then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [flagsCount, bval_add, P1Batch.bval, hp, hq, hr, hs]

theorem bval_sumPush {A T : Type} (f : A × T → NumberWord) (a : A) (xs : List T) :
    P1Batch.bval (sumWords (Code.polyPush f (a, xs))) =
      (xs.map (fun t => P1Batch.bval (f (a, t)))).sum := by
  rw [bval_sumWords, Code.polyPush, List.map_map]
  rfl

theorem bval_chooseBoth (p q : Prop) [Decidable p] [Decidable q] (w : NumberWord) :
    P1Batch.bval (bif bitAnd (decide p, decide q) then w else []) = (if p ∧ q then P1Batch.bval w else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bitAnd, hp, hq, P1Batch.bval]

set_option maxHeartbeats 900000 in
theorem wordRankAt_reads (t w : WireWords) (f e : Wire ℕ a g) (ht : MatchesWire t f) (hw : MatchesWire w e)
    (hb : t.1 ∈ bases.2) (k : Fin (2 ^ a)) (mask : ColorWord a) :
    let z := atThin f k mask
    let v := sIn a g D u ℓ z
    P1Batch.bval (wordRankAt ((leaf, t, wireRankKey (wireRadices a g, w)),
        Carry.born k.val, Carry.born (bwNum mask))) =
      (if ¬ sThick D u ℓ z ∧ sKey z < sKey e then 1 else 0) +
      (if sThick D u ℓ v ∧ ¬ sThick D u ℓ z ∧ sKey v < sKey e then 1 else 0) := by
  let z := atThin f k mask
  let v := sIn a g D u ℓ z
  let wz := rankWireWords (wireRadices a g, t, Carry.born k.val, Carry.born (bwNum mask))
  let wv := nearHop false (near, wz)
  let K := wireRankKey (wireRadices a g, w)
  have hZ : MatchesWire wz z := rankWireWords_code t f ht _ _ k mask (bval_born _) (bval_born _)
  have hzb : wz.1 ∈ bases.2 := hb
  have hV : MatchesWire wv v := nearHop_code all D u ℓ a g len Y key wz z hZ hzb false
  change P1Batch.bval (flagsCount (!wordThick (leaf, wz), Carry.lt_ (wireRankKey (wireRadices a g, wz), K),
    wordThick (leaf, wv), Carry.lt_ (wireRankKey (wireRadices a g, wv), K))) = _
  have ha := wordThick_here all D u ℓ a g len Y key wz z hZ hzb
  have hb' := wordThick_hop all D u ℓ a g len Y key wz z hZ hzb false
  change wordThick (leaf, wv) = decide (sThick D u ℓ v) at hb'
  have hz := wireRankKey_code wz z hZ
  have hv := wireRankKey_code wv v hV
  have he : P1Batch.bval K = sKey e := wireRankKey_code w e hw
  rw [ha, hb', less_spec, less_spec, hz, hv, he]
  exact flagsCount_value _ _ _ _

set_option maxHeartbeats 900000 in
theorem wordRank_reads (t w : WireWords) (f e : Wire ℕ a g) (ht : MatchesWire t f) (hw : MatchesWire w e)
    (hb : t.1 ∈ bases.2) :
    P1Batch.bval (wordRank (leaf, t, w)) = sRank D u ℓ f e := by
  let k := wireRankKey (wireRadices a g, w)
  let p := fun x : NumberWord × NumberWord => P1Batch.bval (wordRankAt ((leaf, t, k), x))
  change P1Batch.bval (sumWords (Code.polyPush wordRankAt
    ((leaf, t, k), (wordRange (tally (2 ^ a))).product (wordRange (tally (2 ^ (2 * 2 ^ a + 1))))))) = _
  rw [bval_sumPush, sumWordProduct]
  let c := bitWordFinEquiv (2 * 2 ^ a + 1)
  change (∑ j : Fin (2 ^ a), ∑ i : Fin (2 ^ (2 * 2 ^ a + 1)), p (Carry.born j.val, Carry.born i.val)) = _
  calc
    _ = ∑ j : Fin (2 ^ a), ∑ mask : ColorWord a, p (Carry.born j.val, Carry.born (bwNum mask)) :=
      Finset.sum_congr rfl fun j _ =>
        (c.sum_comp (fun i : Fin (2 ^ (2 * 2 ^ a + 1)) => p (Carry.born j.val, Carry.born i.val))).symm
    _ = sRank D u ℓ f e := by
      simp only [p, k, wordRankAt_reads all D u ℓ a g len Y key t w f e ht hw hb, Finset.sum_add_distrib, sRank]

set_option maxHeartbeats 900000 in
theorem bundleAB_code_at (v : WireWords) (t : Wire ℕ a g) (ht : MatchesWire v t) (hb : v.1 ∈ bases.2)
    (m : ColorWord a) (j : BitWord a) :
    MatchesWire (bundleAB (near, v, Carry.born (bwNum m), Carry.born (bwNum j)))
      (totalWire t (bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ t.1.1.1)) m j) := by
  let offset := nearOffset (near, v.1)
  let mc := Carry.born (bwNum m)
  let jc := Carry.born (bwNum j)
  have ho : P1Batch.bval offset = rdOffset D u ℓ t.1.1.1 := by
    have hv := nearOffset_reads all D u ℓ a g len Y key v.1 hb
    exact hv.trans (congrArg (rdOffset D u ℓ) ((matchesWire_parts v t).mp ht).1)
  have H := totalWireWords_code v t ht offset mc jc m j (bval_born _) (bval_born _)
  rw [ho] at H
  exact H

set_option maxHeartbeats 900000 in
theorem totalCandidate_reads (wz : WireWords) (z : Wire ℕ a g) (hz : MatchesWire wz z)
    (hzb : wz.1 ∈ bases.2) (hq : nearWidthRequest (near, wz) ∈ motThirdRaw all near) :
    P1Batch.bval
      (bif bitAnd (wordThick (leaf, wz), wordThick (leaf, nearHop true (near, wz))) then wordWidth (leaf, wz) else []) =
      if sThick D u ℓ z ∧ sThick D u ℓ (sOut a g D u ℓ z) then sWidth D u ℓ z else 0 := by
  have hZ := wordThick_here all D u ℓ a g len Y key wz z hz hzb
  have hV := wordThick_hop all D u ℓ a g len Y key wz z hz hzb true
  have hW := wordWidth_reads all D u ℓ a g len Y key wz z hz hq
  simp only [ite_true] at hV
  rw [hZ, hV, bval_chooseBoth, hW]

set_option maxHeartbeats 900000 in
theorem wordTotalAt_reads (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (hr : w ∈ arcRoots all ctx)
    (m : ColorWord a) (j : BitWord a) :
    let t := thinWire D u ℓ e
    let z := totalWire t (bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ t.1.1.1)) m j
    P1Batch.bval (wordTotalAt ((leaf, wordThin (leaf, w)), Carry.born (bwNum m), Carry.born (bwNum j))) =
      if sThick D u ℓ z ∧ sThick D u ℓ (sOut a g D u ℓ z) then sWidth D u ℓ z else 0 := by
  let t := thinWire D u ℓ e
  let v := wordThin (leaf, w)
  let z := totalWire t (bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ t.1.1.1)) m j
  let mc := Carry.born (bwNum m)
  let jc := Carry.born (bwNum j)
  let wz := bundleAB (near, v, mc, jc)
  change P1Batch.bval (wordTotalAt ((leaf, v), mc, jc)) = if sThick D u ℓ z ∧
    sThick D u ℓ (sOut a g D u ℓ z) then sWidth D u ℓ z else 0
  have hy := rootWire_base all D ℓ a g len Y key w hr
  have hwB : w.1 ∈ bases.2 := hy.symm ▸ root_base_mem all D u ℓ a g len Y key
  have ht : MatchesWire v t := thinSelect_code all D u ℓ a g len Y key w e hw hwB
  have hb : v.1 ∈ bases.2 := thin_base_mem all D u ℓ a g len Y key w e hw hr
  have hz : MatchesWire wz z := bundleAB_code_at all D u ℓ a g len Y key v t ht hb m j
  have he : wz.1 = v.1 := bundleAB_base (near, v, mc, jc)
  have hzb : wz.1 ∈ bases.2 := by rw [he]; exact hb
  have hm : mc ∈ motifMasks ctx := born_mem_wordRange (bitWordFinEquiv _ m).isLt
  have hj : jc ∈ motifSlots ctx := born_mem_wordRange (bitWordFinEquiv _ j).isLt
  have hWmem : nearWidthRequest (near, wz) ∈ motThirdRaw all near :=
    bundleWidthRequest_mem all D u ℓ a g len Y key w hr mc jc hm hj
  have H := totalCandidate_reads all D u ℓ a g len Y key wz z hz hzb hWmem
  change P1Batch.bval (wordTotalAt ((leaf, v), mc, jc)) = if sThick D u ℓ z ∧
    sThick D u ℓ (sOut a g D u ℓ z) then sWidth D u ℓ z else 0 at H
  exact H

set_option maxHeartbeats 900000 in
theorem wordTotal_reads (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (hr : w ∈ arcRoots all ctx) :
    let t := thinWire D u ℓ e
    P1Batch.bval (wordTotal (leaf, wordThin (leaf, w))) =
      sTotal D u ℓ t (bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ t.1.1.1)) := by
  let p := fun x : NumberWord × NumberWord => P1Batch.bval (wordTotalAt ((leaf, wordThin (leaf, w)), x))
  change P1Batch.bval (sumWords (Code.polyPush wordTotalAt
    ((leaf, wordThin (leaf, w)), (wordRange (tally (2 ^ (2 * 2 ^ a + 1)))).product (wordRange (tally (2 ^ a)))))) = _
  rw [bval_sumPush, sumWordProduct, sTotal, Fintype.sum_prod_type]
  let c := bitWordFinEquiv (2 * 2 ^ a + 1)
  let d := bitWordFinEquiv a
  rw [← c.sum_comp (fun i => ∑ j : Fin (2 ^ a), p (Carry.born i.val, Carry.born j.val))]
  apply Finset.sum_congr rfl
  intro m _
  rw [← d.sum_comp (fun j => p (Carry.born (c m).val, Carry.born j.val))]
  apply Finset.sum_congr rfl
  intro j _
  exact wordTotalAt_reads all D u ℓ a g len Y key w e hw hr m j

set_option maxHeartbeats 900000 in
theorem wordDemand_reads (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) (hr : w ∈ arcRoots all ctx) :
    (P1Batch.bval (wordDemand (leaf, w)).1, P1Batch.bval (wordDemand (leaf, w)).2) =
      let v := widthsAt D u ℓ (fun Z => bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ Z)) e
      (v false, v true) := by
  let w₀ := wordThin (leaf, w)
  let t := thinWire D u ℓ e
  let T := sTotal D u ℓ t (bwOf (packingTagBits (2 ^ a)) (rdOffset D u ℓ t.1.1.1))
  let q := PackingData.pieceCount (2 ^ a) (2 * 2 ^ a + 1)
  let result := Carry.nat_div (wordTotal (leaf, w₀), bin q)
  let r := wordRank (leaf, w₀, w)
  have ht : MatchesWire w₀ t :=
    thinSelect_code all D u ℓ a g len Y key w e hw
      ((rootWire_base all D ℓ a g len Y key w hr).symm ▸ root_base_mem all D u ℓ a g len Y key)
  have hr₀ := wordRank_reads all D u ℓ a g len Y key w₀ w t e ht hw (thin_base_mem all D u ℓ a g len Y key w e hw hr)
  change P1Batch.bval r = sRank D u ℓ t e at hr₀
  have hT : P1Batch.bval (wordTotal (leaf, w₀)) = T := wordTotal_reads all D u ℓ a g len Y key w e hw hr
  have hq₁ : P1Batch.bval result.1 = T / q := by unfold result; rw [(bval_divide _ _).1, hT, bval_bin]
  have hq₂ : P1Batch.bval result.2 = T % q := by unfold result; rw [(bval_divide _ _).2, hT, bval_bin]
  apply Prod.ext
  · change P1Batch.bval (bif Carry.lt_ (r, result.2) then Bits.add (result.1, [true]) else result.1) =
      if sRank D u ℓ t e < T % q then T / q + 1 else T / q
    rw [less_spec, hr₀, hq₂]
    by_cases h : sRank D u ℓ t e < T % q
    · rw [decide_eq_true h, Bool.cond_true, ite_eq_left h, bval_add, hq₁]
      rfl
    · rw [decide_eq_false h, Bool.cond_false, ite_eq_right h, hq₁]
  · exact wordWidth_root all D u ℓ a g len Y key w e hw hr

end At

end P1SolGreedy.SolDemand
