import P1SolGreedy.C6Words

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

theorem mem_wordRange (n : ℕ) (w : NumberWord) :
    w ∈ wordRange (tally n) ↔ ∃ k : Fin n, Carry.born k.val = w := by
  rw [wordRange_tally, List.mem_map]
  exact ⟨fun ⟨k, hk, he⟩ => ⟨⟨k, List.mem_range.mp hk⟩, he⟩,
    fun ⟨k, he⟩ => ⟨k.val, List.mem_range.mpr k.isLt, he⟩⟩

theorem optSlotWords_codes (a g : ℕ) (w : OptSlotWord) :
    w ∈ optSlotWords (tagRow a g) ↔ ∃ o : Option (Fin (2 ^ a)), codeOptSlot o = w := by
  change w ∈ (false, []) :: (wordRange (tally (2 ^ a))).map (fun i => (true, i)) ↔ _
  simp only [List.mem_cons, List.mem_map, mem_wordRange]
  constructor
  · rintro (rfl | ⟨_, ⟨k, rfl⟩, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some k, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inl rfl
    | some k => exact Or.inr ⟨_, ⟨k, rfl⟩, rfl⟩

theorem tagPorts_codes (a g : ℕ) (w : PortWord) :
    w ∈ tagPorts (tagRow a g) ↔ ∃ p : Bool × Fin (2 ^ a), codePort p = w := by
  obtain ⟨b, w⟩ := w
  change (b, w) ∈ [false, true].product (wordRange (tally (2 ^ a))) ↔ _
  rw [show ((b, w) ∈ [false, true].product (wordRange (tally (2 ^ a)))) ↔ _ from List.mem_product,
    mem_wordRange]
  constructor
  · rintro ⟨_, k, rfl⟩
    exact ⟨(b, k), rfl⟩
  · rintro ⟨⟨b', k⟩, he⟩
    have hb : b' = b := congrArg Prod.fst he
    have hk : Carry.born k.val = w := congrArg Prod.snd he
    exact ⟨by cases b <;> simp, ⟨k, hk⟩⟩

theorem choiceWords_codes (a g : ℕ) (w : TestChoiceWord) :
    w ∈ choiceWords (tagRow a g) ↔
      ∃ t : Option (Fin (2 ^ a)) ⊕ (Option (Fin (2 ^ a)) × Option (Fin (2 ^ a))),
        codeTestChoice t = w := by
  simp only [choiceWords, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨o, ho, rfl⟩ | ⟨⟨o₁, o₂⟩, hp, rfl⟩)
    · obtain ⟨opt, rfl⟩ := (optSlotWords_codes a g o).mp ho
      exact ⟨.inl opt, rfl⟩
    · obtain ⟨h₁, h₂⟩ := List.mem_product.mp hp
      obtain ⟨p, rfl⟩ := (optSlotWords_codes a g o₁).mp h₁
      obtain ⟨q, rfl⟩ := (optSlotWords_codes a g o₂).mp h₂
      exact ⟨.inr (p, q), rfl⟩
  · rintro ⟨o, rfl⟩
    rcases o with one | ⟨p, q⟩
    · exact Or.inl ⟨codeOptSlot one, (optSlotWords_codes a g _).mpr ⟨one, rfl⟩, rfl⟩
    · exact Or.inr ⟨(codeOptSlot p, codeOptSlot q),
        List.mem_product.mpr ⟨(optSlotWords_codes a g _).mpr ⟨p, rfl⟩,
          (optSlotWords_codes a g _).mpr ⟨q, rfl⟩⟩, rfl⟩

theorem tagTestWords_codes (a g : ℕ) (w : TagTestWord) :
    w ∈ tagTestWords (tagRow a g) ↔ ∃ t : SlotGraph.TagTests (2 ^ a), codeTagTest t = w := by
  obtain ⟨p, c⟩ := w
  unfold tagTestWords
  rw [show ((p, c) ∈ (tagPorts (tagRow a g)).product (choiceWords (tagRow a g))) ↔ _ from List.mem_product,
    tagPorts_codes, choiceWords_codes]
  constructor
  · rintro ⟨⟨slot, rfl⟩, ⟨test, rfl⟩⟩
    exact ⟨(slot, test), rfl⟩
  · rintro ⟨⟨port, test⟩, he⟩
    exact ⟨⟨port, congrArg Prod.fst he⟩, ⟨test, congrArg Prod.snd he⟩⟩

def savedTagState (q : TagContext) (u : List Bool) : TagState :=
  (q, (tagRootRaw q).map (fun r => (r, P1Batch.fetch u r)))

def savedTagFields (q : TagContext) (u : List Bool) : TagFields :=
  let s := savedTagState q u
  (q, s.2, (tagSecondRaw s).map (fun r => (r, P1Batch.fetch u r)))

theorem tagNext_reads (q : TagContext) (u : List Bool) (hl : P1Batch.bval q.1.1 = u.length) :
    tagNext (q, (tagRoot q).map (P1Batch.fetch u)) = savedTagState q u := by
  unfold tagNext tagRoot savedTagState
  dsimp only
  rw [cacheFields_fetch _ _ hl]

theorem tagFinish_reads (q : TagContext) (u : List Bool) (hl : P1Batch.bval q.1.1 = u.length) :
    let s := savedTagState q u
    tagFinish (s, (tagSecond s).map (P1Batch.fetch u)) = savedTagFields q u := by
  unfold tagFinish tagSecond savedTagFields
  dsimp only
  have hs : P1Batch.bval (savedTagState q u).1.1.1 = u.length := hl
  rw [cacheFields_fetch _ _ hs]
  rfl

section At

variable (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y : NumberWord)

local notation "q" => (activeTag D ℓ a g len Y)
local notation "rootState" => (savedTagState q u)
local notation "panelData" => (savedTagFields q u)

theorem root_slot_reads (c : Mem) (hc : c ∈ tagRootSections) (k : Fin (2 ^ a)) :
    P1Batch.bval (cacheRead (rootState.2, slotAt c (levelRow D ℓ, Y, Carry.born k.val))) =
      readField D u (secLev ℓ c) (P1Batch.bval Y * (D.lv ℓ).slots + k.val) := by
  have hk : P1Batch.bval (Carry.born k.val) < 2 ^ a := by rw [bval_born]; exact k.isLt
  have h := cacheRead_slot D u ℓ c (tagRootRaw q) Y (Carry.born k.val) hk
    (fun _ hr => tagRootSlot_mem D ℓ a g len Y hc hr)
  rw [bval_born] at h
  exact h

theorem neighborAt_reads (b : Bool) (k : Fin (2 ^ a)) :
    P1Batch.bval (neighborAt (rootState, codePort (b, k))) =
      if b then rdOutAddr D u ℓ (P1Batch.bval Y) k else rdInAddr D u ℓ (P1Batch.bval Y) k := by
  cases b
  · exact root_slot_reads D u ℓ a g len Y .inAddr (by simp [tagRootSections]) k
  · exact root_slot_reads D u ℓ a g len Y .outAddr (by simp [tagRootSections]) k

theorem rootShift_reads (b : Bool) (k : Fin (2 ^ a)) :
    P1Batch.bval (rootShift (panelData, codePort (b, k))) =
      (bitWordFinEquiv _ (if b then tauOut a g D u ℓ (P1Batch.bval Y) k
        else tauIn a g D u ℓ (P1Batch.bval Y) k) : ℕ) := by
  cases b
  · change P1Batch.bval (extractedTag (tagRow a g,
        cacheRead (rootState.2, slotAt .inDisp (levelRow D ℓ, Y, Carry.born k.val)))) = _
    rw [extractedTag_spec, root_slot_reads D u ℓ a g len Y .inDisp (by simp [tagRootSections]) k]
    rfl
  · change P1Batch.bval (extractedTag (tagRow a g,
        cacheRead (rootState.2, slotAt .outDisp (levelRow D ℓ, Y, Carry.born k.val)))) = _
    rw [extractedTag_spec, root_slot_reads D u ℓ a g len Y .outDisp (by simp [tagRootSections]) k]
    rfl

theorem rootOffset_reads :
    P1Batch.bval (cacheRead (rootState.2, offsetAt (levelRow D ℓ, Y))) = rdOffset D u ℓ (P1Batch.bval Y) :=
  cacheRead_field D u ℓ .offset (tagRootRaw q) Y (tagRootOffset_mem D ℓ a g len Y)

theorem increment_reads (Z : NumberWord) (rs : List P1Batch.Req)
    (hs : ∀ r ∈ slotsAt .outDisp (levelRow D ℓ, Z, wordRange (tally (2 ^ a))), r ∈ rs)
    (o : Option (Fin (2 ^ a))) :
    P1Batch.bval (tagIncrementWord
      ((q, rs.map (fun r => (r, P1Batch.fetch u r))), Z, codeOptSlot o)) =
      (bitWordFinEquiv _ (incS a g D u ℓ (P1Batch.bval Z) o) : ℕ) := by
  cases o with
  | none =>
    change 0 = (bitWordFinEquiv (packingTagBits (2 ^ a)) 0).val
    exact (bitWord_code_zero _).symm
  | some k =>
    have hk : P1Batch.bval (Carry.born k.val) < 2 ^ a := by rw [bval_born]; exact k.isLt
    change P1Batch.bval (extractedTag (tagRow a g, cacheRead (rs.map (fun r => (r, P1Batch.fetch u r)),
      slotAt .outDisp (levelRow D ℓ, Z, Carry.born k.val)))) = _
    rw [extractedTag_spec, cacheRead_slot D u ℓ .outDisp rs Z _ hk hs, bval_born]
    rfl

theorem increment_root (o : Option (Fin (2 ^ a))) :
    P1Batch.bval (tagIncrementWord (rootState, Y, codeOptSlot o)) =
      (bitWordFinEquiv _ (incS a g D u ℓ (P1Batch.bval Y) o) : ℕ) :=
  increment_reads D u ℓ a g len Y Y (tagRootRaw q)
    (fun r hr => tagRootSlot_mem D ℓ a g len Y (by simp [tagRootSections]) hr) o

theorem increment_neighbor (Z : NumberWord) (hZ : Z ∈ tagNeighbors rootState) (o : Option (Fin (2 ^ a))) :
    P1Batch.bval (tagIncrementWord ((q, panelData.2.2), Z, codeOptSlot o)) =
      (bitWordFinEquiv _ (incS a g D u ℓ (P1Batch.bval Z) o) : ℕ) :=
  increment_reads D u ℓ a g len Y Z (tagSecondRaw rootState)
    (fun _ hr => tagSecond_mem D ℓ a g len Y rootState.2 hZ (List.mem_cons_of_mem _ hr)) o

theorem maskedTag_reads (Z : NumberWord) (hZ : Z ∈ tagNeighbors rootState) :
    P1Batch.bval (maskedTag (panelData, Z)) =
      (bitWordFinEquiv _ (moff a D u ℓ (P1Batch.bval Y) (P1Batch.bval Z)) : ℕ) := by
  have hq : offsetAt (levelRow D ℓ, Z) ∈ tagSecondRaw rootState :=
    tagSecond_mem D ℓ a g len Y rootState.2 hZ List.mem_cons_self
  have hread : P1Batch.bval (cacheRead (panelData.2.2, offsetAt (levelRow D ℓ, Z))) =
      rdOffset D u ℓ (P1Batch.bval Z) :=
    cacheRead_field D u ℓ .offset (tagSecondRaw rootState) Z hq
  unfold maskedTag moff
  change P1Batch.bval (bif Carry.lt_ (Z, Y) then
    boundWord (bin (2 ^ packingTagBits (2 ^ a)), cacheRead (panelData.2.2, offsetAt (levelRow D ℓ, Z)))
    else []) = _
  rw [less_spec]
  by_cases h : P1Batch.bval Z < P1Batch.bval Y
  · rw [decide_eq_true h, Bool.cond_true, ite_eq_left h, bval_boundWord, hread, Equiv.apply_symm_apply]
  · rw [decide_eq_false h, Bool.cond_false, ite_eq_right h, bitWord_code_zero]
    rfl

set_option maxHeartbeats 900000 in
theorem testTagWord_reads (t : SlotGraph.TagTests (2 ^ a)) :
    P1Batch.bval (testTagWord (panelData, codeTagTest t)) =
      (bitWordFinEquiv _ (forbS a g D u ℓ (P1Batch.bval Y) t) : ℕ) := by
  obtain ⟨⟨b, k⟩, t⟩ := t
  let p := codePort (b, k)
  let w := rootShift (panelData, p)
  let Z := neighborAt (rootState, p)
  let home (o : Option (Fin (2 ^ a))) := tagIncrementWord (rootState, Y, codeOptSlot o)
  let near (o : Option (Fin (2 ^ a))) := tagIncrementWord ((q, panelData.2.2), Z, codeOptSlot o)
  let f := maskedTag (panelData, Z)
  have hZmem : Z ∈ tagNeighbors rootState :=
    neighborAt_mem rootState b _ (born_mem_wordRange k.isLt)
  have hZ := neighborAt_reads D u ℓ a g len Y b k
  change P1Batch.bval Z =
    (if b then rdOutAddr D u ℓ (P1Batch.bval Y) k else rdInAddr D u ℓ (P1Batch.bval Y) k) at hZ
  have hw := rootShift_reads D u ℓ a g len Y b k
  change P1Batch.bval w = (bitWordFinEquiv _ (if b then _ else _) : ℕ) at hw
  have hhome (o) := increment_root D u ℓ a g len Y o
  have hnear (o) := increment_neighbor D u ℓ a g len Y Z hZmem o
  have hf := maskedTag_reads D u ℓ a g len Y Z hZmem
  change P1Batch.bval f = (bitWordFinEquiv _ (moff a D u ℓ (P1Batch.bval Y) (P1Batch.bval Z)) : ℕ) at hf
  cases b <;> rcases t with o | ⟨o₁, o₂⟩
  · change P1Batch.bval (xorWords (w, home o)) = _
    rw [bval_xorWords, hw, show P1Batch.bval (home o) = _ from hhome o]
    exact (bitWord_code_add _ _).symm
  · change P1Batch.bval (xorWords (xorWords (xorWords (w, near o₁), home o₂), f)) = _
    rw [bval_xorWords, bval_xorWords, bval_xorWords, hw, hf,
      show P1Batch.bval (near o₁) = _ from hnear o₁, show P1Batch.bval (home o₂) = _ from hhome o₂, hZ]
    rw [forbS, bitWord_code_sub, bitWord_code_add, bitWord_code_add]
    rfl
  · change P1Batch.bval (xorWords (w, home o)) = _
    rw [bval_xorWords, hw, show P1Batch.bval (home o) = _ from hhome o]
    exact (bitWord_code_add _ _).symm
  · change P1Batch.bval (xorWords (xorWords (xorWords (w, home o₁), near o₂), f)) = _
    rw [bval_xorWords, bval_xorWords, bval_xorWords, hw, hf,
      show P1Batch.bval (home o₁) = _ from hhome o₁, show P1Batch.bval (near o₂) = _ from hnear o₂, hZ]
    rw [forbS, bitWord_code_sub, bitWord_code_add, bitWord_code_add]
    rfl

theorem forbiddenTagWords_mem (v : ℕ) :
    v ∈ (forbiddenTagWords panelData).map P1Batch.bval ↔
      ∃ t, (bitWordFinEquiv _ (forbS a g D u ℓ (P1Batch.bval Y) t) : ℕ) = v := by
  change v ∈ ((tagTestWords (tagRow a g)).map (fun w => testTagWord (panelData, w))).map P1Batch.bval ↔ _
  rw [List.map_map, List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨t, rfl⟩ := (tagTestWords_codes a g w).mp hw
    exact ⟨t, (testTagWord_reads D u ℓ a g len Y t).symm.trans he⟩
  · rintro ⟨t, ht⟩
    exact ⟨codeTagTest t, (tagTestWords_codes a g _).mpr ⟨t, rfl⟩,
      (testTagWord_reads D u ℓ a g len Y t).trans ht⟩

set_option maxHeartbeats 900000 in
theorem decideTag_reads :
    decideTag panelData = true ↔ C6chk a g D u ℓ (P1Batch.bval Y) := by
  let cap := 2 ^ packingTagBits (2 ^ a)
  let v := cacheRead (rootState.2, offsetAt (levelRow D ℓ, Y))
  let forbidden := forbiddenTagWords panelData
  change leastMissingWords (v, bin cap, forbidden, wordRange (tally cap)) = true ↔ _
  have hcomplete (k : ℕ) (hk : k < P1Batch.bval (bin cap)) : k ∈ (wordRange (tally cap)).map P1Batch.bval := by
    rw [bval_bin] at hk
    exact List.mem_map.mpr ⟨Carry.born k, born_mem_wordRange hk, bval_born k⟩
  have hv : P1Batch.bval v = rdOffset D u ℓ (P1Batch.bval Y) := rootOffset_reads D u ℓ a g len Y
  rw [leastMissingWords_spec _ _ _ _ hcomplete, hv, bval_bin]
  simp only [forbidden, forbiddenTagWords_mem, C6chk, not_exists, cap]
  exact and_congr_right (fun _ => and_congr_left (fun _ => forall_congr' fun t => ne_comm))

end At

def evaluateTag (q : TagContext) (u : List Bool) : Bool :=
  let s := tagNext (q, (tagRoot q).map (P1Batch.fetch u))
  decideTag (tagFinish (s, (tagSecond s).map (P1Batch.fetch u)))

open Classical in
theorem evaluateTag_correct (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ)
    (x u i : List Bool) (hlen : u.length = M x.length) :
    evaluateTag (setupC6 dims M ag (bin x.length, i)) u =
      decide (C6fam dims ag x u (P1Batch.bval i)) := by
  let D := dims x.length
  let A := ag x.length
  let m := M x.length
  let q := setupTag (tagFormat D m A, i)
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let Y := q.1.2.2.1
  have hq : setupC6 dims M ag (bin x.length, i) = q := by
    simp only [setupC6, bval_bin, D, A, m, q]
  have hsize : P1Batch.bval q.1.1 = u.length := (setupTag_length D m A i).trans hlen.symm
  obtain ⟨hvalid, hy, _⟩ := setupTag_spec D m A i
  rw [hq, Bool.eq_iff_iff, decide_eq_true_eq]
  by_cases h : ShrinkIdx D (P1Batch.bval i)
  · have hactive : q = activeTag D ℓ (A ℓ).1 (A ℓ).2 (bin m) Y := setupTag_inRange D m A i h
    unfold evaluateTag
    rw [tagNext_reads _ _ hsize]
    change decideTag (tagFinish (savedTagState q u,
      (tagSecond (savedTagState q u)).map (P1Batch.fetch u))) = true ↔ _
    rw [tagFinish_reads q u hsize]
    conv_lhs => rw [hactive]
    rw [decideTag_reads, show P1Batch.bval Y = _ from hy]
    change C6chk (A ℓ).1 (A ℓ).2 D u ℓ (P1Batch.bval i / 2 ^ levBits D) ↔
      ShrinkIdx D (P1Batch.bval i) → C6chk (A ℓ).1 (A ℓ).2 D u ℓ (P1Batch.bval i / 2 ^ levBits D)
    exact ⟨fun hc _ => hc, fun hc => hc h⟩
  · have hflag : q.1.2.1 = false := Bool.eq_false_iff.mpr fun ht => h (hvalid.mp ht)
    have hp : evaluateTag q u = true := by
      simp only [evaluateTag, tagNext, tagFinish, decideTag, hflag, Bool.cond_false]
    exact ⟨fun _ ht => (h ht).elim, fun _ => hp⟩

#print axioms evaluateTag_correct

end P1SolGreedy.SolDemand
