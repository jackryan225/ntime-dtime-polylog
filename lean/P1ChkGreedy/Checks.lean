import P1P7.Defs

/-!
# P1ChkGreedy.Checks: checks C5-C9 of the Lemma P verifier, in OpenAI's rules

Problem P1 (C1, wall card W-ntime-dtime-polylog), Case 2, part of task P8 (research/g3/leanplan/PLAN.md).
Lane P1-lean-W2-chkgreedy (brief ORG/briefs/P1-lean-W2-chkgreedy.md, rules ORG/briefs/P1-lean-COMMON.md).
Paper: research/papers/ntime-dtime-polylog.tex, subsec:witness, checks C5-C9 (l.1037-1052) and lem:unique.

The checks follow OpenAI's Lean construction (openai/math 3344da5, folder OAI/Computability/VPVNP), not the older
paper text (P7 spike research/p1/lean/P7/SPIKE.md section 3; PLAN.md section 9, 10:15Z):
* C5, C6: OpenAI's greedy scans `orderedColor`, `orderedTagOffsets` (SlotGreedyScan.lean:182, 235) read the
  neighbours LATER in base order with the initial value 0 (`P1P7.orderedColor_local`, `orderedTagOffsets_local`).
* C7: the stored outer index is admitted (`outerIndices`, MotifConversion.lean:62) for the two demand widths of the
  motif; the AB width is the slice of the bundle payload given by OpenAI's lane-0 key order `X.shrinkNumber`
  (`sortedBundleNumbering`, SlotBundleNumbering.lean:145) and `splitWidth` (larger pieces first).
  Terms are keyed at the source base of the motif's old wire (the convention of `P1P7.choiceAt`).
* C8: energy prefixes with OpenAI's integer coefficients (10, 20, 6, 5) (`P1P7.layoutCoeff`, `groupEnergy_eq`);
  the motifs are grouped by the source base of their wire.
* C9: layout bit = `decide (E true (last) < E false (last))`; ties give `false` = paper layout 1
  (`P1P7.layoutBit_eq_int`).

Form. Each check is a Prop on the TRUE level state `X` (OpenAI's compressor `State`; its base records and widths are
the true ones by the induction of lem:unique, checks C4 and C10) and on the STORED fields of the witness at that level,
given as tables over the bases `X.Base` (the witness stores them in address order `X.baseIndex`; the decoding is
P1Wit.Layout's). For each check: `Ck_true` (the true fields pass at every index) and `Ck_unique` (fields that pass
at every index are the true ones); `Ck_iff` combines both. C5, C6, C8: uniqueness by induction in base order
(`unique_of_earlier`). `level_true` and `level_unique` assemble the step "By C5 and C6 ... By C7 ... By C8 and C9"
of lem:unique for one shrinking level: the passing fields are the true colours and offsets and the term table,
energy prefixes and layout bit of exactly one admitted selection `s : X.ShrinkSelection B`.
-/

namespace P1ChkGreedy

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

/-! ## 1. Uniqueness by induction in base order; scan checks -/

section Scan

variable {V : Type*} {N : ℕ} {A : Type*}

/-- Uniqueness by induction in base order: if the check `P` at `y` determines the value at `y` from the values at
the bases earlier than `y`, then two tables that pass the check at every base are equal. -/
theorem unique_of_earlier (order : V ≃ Fin N) (P : (V → A) → V → Prop)
    (hdet : ∀ f f' y, P f y → P f' y → (∀ z, order z < order y → f z = f' z) → f y = f' y)
    {f f' : V → A} (hf : ∀ y, P f y) (hf' : ∀ y, P f' y) : f = f' := by
  have key : ∀ k : ℕ, ∀ y, (order y : ℕ) = k → f y = f' y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      refine hdet f f' y (hf y) (hf' y) fun z hz => ih (order z) ?_ z rfl
      rw [← hy]
      exact Fin.lt_def.mp hz
  funext y
  exact key _ y rfl

/-- The table that a scan visit at `y` reads: the stored values at the bases earlier than `y`, `init` at all
others (OpenAI's scans start from the constant table `init`). -/
def masked (order : V ≃ Fin N) (init : A) (f : V → A) (y : V) : V → A :=
  fun z => if order z < order y then f z else init

/-- The scan check at `y`: the stored value at `y` is the rule `select` applied to `masked order init f y`. -/
def ScanCheck (order : V ≃ Fin N) (select : V → (V → A) → A) (init : A) (f : V → A) (y : V) : Prop :=
  f y = select y (masked order init f y)

theorem scanCheck_unique (order : V ≃ Fin N) (select : V → (V → A) → A) (init : A) {f f' : V → A}
    (hf : ∀ y, ScanCheck order select init f y) (hf' : ∀ y, ScanCheck order select init f' y) :
    f = f' := by
  refine unique_of_earlier order (ScanCheck order select init) ?_ hf hf'
  intro f f' y h h' hearly
  rw [h, h']
  congr 1
  funext z
  unfold masked
  split_ifs with hz
  · exact hearly z hz
  · rfl

end Scan

/-! ## 2. C5: greedy colours (OpenAI `orderedColor`) -/

section Colour

variable {V : Type*} {d N : ℕ}

/-- **C5** at base `y`: the stored colour of `y` is OpenAI's greedy rule `chooseColor` (SlotGreedyScan.lean:171)
applied to the STORED colours of the bases earlier than `y` in base order and colour `0` at the later ones.
`chooseColor` reads only the `2d` neighbour slots of `y` (`colorForbidden`). -/
def C5 (G : SlotGraph V d) (order : V ≃ Fin N) (col : V → Fin (2 * d + 1)) (y : V) : Prop :=
  ScanCheck order G.chooseColor 0 col y

theorem C5_true (G : SlotGraph V d) (order : V ≃ Fin N) (y : V) :
    C5 G order (G.orderedColor order) y :=
  P1P7.orderedColor_local G order y

theorem C5_unique (G : SlotGraph V d) (order : V ≃ Fin N) {col : V → Fin (2 * d + 1)}
    (h : ∀ y, C5 G order col y) : col = G.orderedColor order :=
  scanCheck_unique order G.chooseColor 0 h (C5_true G order)

theorem C5_iff (G : SlotGraph V d) (order : V ≃ Fin N) (col : V → Fin (2 * d + 1)) :
    (∀ y, C5 G order col y) ↔ col = G.orderedColor order :=
  ⟨C5_unique G order, fun h => h ▸ C5_true G order⟩

/-- `chooseColor` is the least colour outside the `2d` values that it reads. -/
theorem chooseColor_eq_iff (G : SlotGraph V d) (y : V) (f : V → Fin (2 * d + 1)) (c : Fin (2 * d + 1)) :
    G.chooseColor y f = c ↔
      (∀ t, c ≠ G.colorForbidden y f t) ∧ ∀ k < c, ∃ t, G.colorForbidden y f t = k := by
  obtain ⟨h1, h2⟩ := G.chooseColor_spec y f
  constructor
  · rintro rfl
    exact ⟨h1, h2⟩
  · rintro ⟨hc1, hc2⟩
    rcases lt_trichotomy (G.chooseColor y f) c with hlt | heq | hgt
    · obtain ⟨t, ht⟩ := hc2 _ hlt
      exact absurd ht.symm (h1 t)
    · exact heq
    · obtain ⟨t, ht⟩ := h2 _ hgt
      exact absurd ht.symm (hc1 t)

/-- C5 as the test that the checker performs on the values it reads: the stored colour of `y` is none of the `2d`
(masked) neighbour colours, and every smaller colour is one of them. -/
theorem C5_iff_least (G : SlotGraph V d) (order : V ≃ Fin N) (col : V → Fin (2 * d + 1)) (y : V) :
    C5 G order col y ↔
      (∀ t, col y ≠ G.colorForbidden y (masked order 0 col y) t) ∧
        ∀ k < col y, ∃ t, G.colorForbidden y (masked order 0 col y) t = k := by
  unfold C5 ScanCheck
  rw [eq_comm]
  exact chooseColor_eq_iff G y _ (col y)

end Colour

/-! ## 3. C6: greedy tag offsets (OpenAI `orderedTagOffsets`) -/

section TagOffset

variable {V : Type*} {d N J : ℕ} {Tag : Type*} [AddCommGroup Tag]

/-- **C6** at base `y`: the stored offset of `y` is OpenAI's greedy rule `chooseTag` (SlotGreedyScan.lean:218,
first tag in the order `index` outside the `2d((d+1)+(d+1)^2)` values of `tagForbidden`) applied to the STORED
offsets of the earlier bases and offset `0` at the later ones. -/
def C6 (G : SlotGraph V d) (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (off : V → Tag) (y : V) : Prop :=
  ScanCheck order (G.chooseTag index τ hcard) 0 off y

theorem C6_true (G : SlotGraph V d) (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (y : V) :
    C6 G order index τ hcard (G.orderedTagOffsets order index τ hcard) y :=
  P1P7.orderedTagOffsets_local G order index τ hcard y

theorem C6_unique (G : SlotGraph V d) (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) {off : V → Tag}
    (h : ∀ y, C6 G order index τ hcard off y) : off = G.orderedTagOffsets order index τ hcard :=
  scanCheck_unique order (G.chooseTag index τ hcard) 0 h (C6_true G order index τ hcard)

theorem C6_iff (G : SlotGraph V d) (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (off : V → Tag) :
    (∀ y, C6 G order index τ hcard off y) ↔ off = G.orderedTagOffsets order index τ hcard :=
  ⟨C6_unique G order index τ hcard, fun h => h ▸ C6_true G order index τ hcard⟩

/-- `chooseTag` is the first tag (in the order `index`) outside the values that it reads. -/
theorem chooseTag_eq_iff (G : SlotGraph V d) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (y : V) (f : V → Tag) (t : Tag) :
    G.chooseTag index τ hcard y f = t ↔
      (∀ i, index t ≠ index (G.tagForbidden τ y f i)) ∧
        ∀ k < index t, ∃ i, index (G.tagForbidden τ y f i) = k := by
  obtain ⟨h1, h2⟩ := G.chooseTag_spec index τ hcard y f
  constructor
  · rintro rfl
    exact ⟨h1, h2⟩
  · rintro ⟨ht1, ht2⟩
    apply index.injective
    rcases lt_trichotomy (index (G.chooseTag index τ hcard y f)) (index t) with hlt | heq | hgt
    · obtain ⟨i, hi⟩ := ht2 _ hlt
      exact absurd hi.symm (h1 i)
    · exact heq
    · obtain ⟨i, hi⟩ := h2 _ hgt
      exact absurd hi.symm (ht1 i)

/-- C6 as the test that the checker performs on the values it reads. -/
theorem C6_iff_least (G : SlotGraph V d) (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (off : V → Tag) (y : V) :
    C6 G order index τ hcard off y ↔
      (∀ i, index (off y) ≠ index (G.tagForbidden τ y (masked order 0 off y) i)) ∧
        ∀ k < index (off y), ∃ i, index (G.tagForbidden τ y (masked order 0 off y) i) = k := by
  unfold C6 ScanCheck
  rw [eq_comm]
  exact chooseTag_eq_iff G index τ hcard y _ (off y)

end TagOffset

/-! ## 4. C5 and C6 on a compressor state of a shrinking substep -/

section StateGreedy

variable {a g : ℕ}

/-- OpenAI's `τ` of the tag-offset scan of a shrinking substep (PackingLanes.lean:78): the tag part of the lane
displacement of a base slot (in the base record (P1) of the slot's source base). -/
def tagShift (X : State a (packingLaneBits a g)) (p : X.Base × Fin (2 ^ a)) :
    BitWord (packingTagBits (2 ^ a)) :=
  (packingFields a g (X.slots.displacement p)).2.2.1

/-- **C5** on a compressor state: slot graph `X.slots.base`, base order `X.baseIndex` (the addresses). -/
def C5s (X : State a (packingLaneBits a g)) (col : X.Base → Fin (2 * 2 ^ a + 1)) (y : X.Base) : Prop :=
  C5 X.slots.base X.baseIndex col y

theorem C5s_true (X : State a (packingLaneBits a g)) (y : X.Base) : C5s X X.packingData.color y :=
  C5_true X.slots.base X.baseIndex y

theorem C5s_unique (X : State a (packingLaneBits a g)) {col : X.Base → Fin (2 * 2 ^ a + 1)}
    (h : ∀ y, C5s X col y) : col = X.packingData.color :=
  C5_unique X.slots.base X.baseIndex h

theorem C5s_iff (X : State a (packingLaneBits a g)) (col : X.Base → Fin (2 * 2 ^ a + 1)) :
    (∀ y, C5s X col y) ↔ col = X.packingData.color :=
  ⟨C5s_unique X, fun h => h ▸ C5s_true X⟩

/-- **C6** on a compressor state: tags `BitWord (packingTagBits (2^a))` in the order `bitWordFinEquiv`, `τ` the
tag shifts of the base slots (exactly the arguments of `orderedDyadicPacking`, PackingLanes.lean:77). -/
def C6s (X : State a (packingLaneBits a g)) (off : X.Base → BitWord (packingTagBits (2 ^ a)))
    (y : X.Base) : Prop :=
  C6 X.slots.base X.baseIndex (bitWordFinEquiv (packingTagBits (2 ^ a))) (tagShift X)
    (packingTagBits_sufficient (2 ^ a)) off y

theorem C6s_true (X : State a (packingLaneBits a g)) (y : X.Base) : C6s X X.packingData.offset y :=
  C6_true X.slots.base X.baseIndex _ (tagShift X) _ y

theorem C6s_unique (X : State a (packingLaneBits a g))
    {off : X.Base → BitWord (packingTagBits (2 ^ a))} (h : ∀ y, C6s X off y) :
    off = X.packingData.offset :=
  C6_unique X.slots.base X.baseIndex _ (tagShift X) _ h

theorem C6s_iff (X : State a (packingLaneBits a g)) (off : X.Base → BitWord (packingTagBits (2 ^ a))) :
    (∀ y, C6s X off y) ↔ off = X.packingData.offset :=
  ⟨C6s_unique X, fun h => h ▸ C6s_true X⟩

end StateGreedy

/-! ## 5. C7: admitted term indices; C8: energy prefixes; C9: the layout bit -/

section Terms

attribute [local instance] P1P7.instDecEqBase

variable {a g : ℕ} {factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- The old arcs (wires) of a shrinking substep in OpenAI's packed coordinates
`(((base, (tag, lane)), out-slot), (colour bits, slot label))`. -/
abbrev OldArc (X : State a (packingLaneBits a g)) :=
  Arc X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1)

/-- An old arc carries a motif (one CD demand) iff it is not thick at both ends (`PackingData.Motif`). -/
abbrev IsMotif (X : State a (packingLaneBits a g)) (e : OldArc X) : Prop :=
  ¬ (X.packingData.thick (sourcePosition e) ∧
    X.packingData.thick (sourcePosition (X.packingData.actual e)))

/-- The two demand widths of a motif (`shrinkDemandWidths`): the AB width, i.e. the slice of its bundle's payload
in OpenAI's lane-0 key order `X.shrinkNumber` (`splitWidth`, larger pieces first), and the CD width, i.e. the
width of the motif's own old wire. -/
noncomputable abbrev demandW (X : State a (packingLaneBits a g)) (m : X.packingData.Motif) : Bool → ℕ :=
  X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m

/-- **C7** at the term slot of the old arc `e` (keyed at the source base of `e`, as `P1P7.choiceAt`): a thick-thick
arc has an empty slot; a motif holds an outer index (8 integers, `Bool × Fin 4 → ℕ`) admitted for its two demand
widths (`outerIndices`, MotifConversion.lean:62). -/
def C7 (X : State a (packingLaneBits a g)) (tm : OldArc X → Option (Bool × Fin 4 → ℕ)) (e : OldArc X) :
    Prop :=
  if h : IsMotif X e then ∃ v, tm e = some v ∧ v ∈ MotifConversion.outerIndices B (demandW X ⟨e, h⟩)
  else tm e = none

/-- C7 with OpenAI's integer admission test (`MotifAdmission.admit`, fixed rational masses `supplyMass`): what
the checker evaluates. -/
theorem C7_iff_admit (X : State a (packingLaneBits a g)) (tm : OldArc X → Option (Bool × Fin 4 → ℕ))
    (e : OldArc X) :
    C7 B X tm e ↔
      if h : IsMotif X e then ∃ v, tm e = some v ∧
        MotifAdmission.admit supplyMass v (MotifConversion.repetitions B (demandW X ⟨e, h⟩))
          B.scale B.radius = true
      else tm e = none := by
  unfold C7
  split_ifs with h
  · simp only [MotifConversion.mem_outerIndices_iff B supplyMass_pos]
  · exact Iff.rfl

/-- The term table of a selection `s`: the chosen outer index at every motif, empty at the thick-thick arcs
(the data of `P1P7.choiceAt`, as one table over the old arcs). -/
noncomputable def trueTerms (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (e : OldArc X) :
    Option (Bool × Fin 4 → ℕ) :=
  if h : IsMotif X e then some (s ⟨e, h⟩).val else none

theorem trueTerms_motif (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (m : X.packingData.Motif) : trueTerms B X s m.val = some (s m).val := by
  unfold trueTerms
  rw [dif_pos m.property]

theorem choiceAt_eq_trueTerms (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (y : X.Base)
    (i : Fin (2 ^ a)) (t : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) (u : BitWord (2 * 2 ^ a + 1))
    (h : BitWord a) : P1P7.choiceAt B X s y i t l u h = trueTerms B X s (((y, (t, l)), i), (u, h)) := rfl

theorem C7_true (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (e : OldArc X) :
    C7 B X (trueTerms B X s) e := by
  unfold C7 trueTerms
  split_ifs with h
  · exact ⟨_, rfl, (s ⟨e, h⟩).property⟩
  · rfl

/-- C7 at every term slot determines exactly one admitted selection (the paper: "the terms of substep ℓ are
admitted for the true demand widths"; `X.ShrinkSelection B` is OpenAI's type of admitted term lists). -/
theorem C7_unique (X : State a (packingLaneBits a g)) {tm : OldArc X → Option (Bool × Fin 4 → ℕ)}
    (h : ∀ e, C7 B X tm e) : ∃! s : X.ShrinkSelection B, tm = trueTerms B X s := by
  have hm : ∀ m : X.packingData.Motif, ∃ v, tm m.val = some v ∧
      v ∈ MotifConversion.outerIndices B (demandW X m) := by
    intro m
    have hme := h m.val
    rw [C7, dif_pos m.property] at hme
    exact hme
  choose v hv using hm
  refine ⟨fun m => ⟨v m, (hv m).2⟩, ?_, ?_⟩
  · funext e
    by_cases he : IsMotif X e
    · rw [trueTerms, dif_pos he]
      exact (hv ⟨e, he⟩).1
    · have hne := h e
      rw [C7, dif_neg he] at hne
      rw [trueTerms, dif_neg he, hne]
  · intro s' hs'
    funext m
    apply Subtype.ext
    have h2 := (hv m).1
    rw [hs', trueTerms_motif] at h2
    exact Option.some.inj h2

theorem C7_iff (X : State a (packingLaneBits a g)) (tm : OldArc X → Option (Bool × Fin 4 → ℕ)) :
    (∀ e, C7 B X tm e) ↔ ∃ s : X.ShrinkSelection B, tm = trueTerms B X s :=
  ⟨fun h => (C7_unique B X h).exists, fun ⟨s, hs⟩ => hs ▸ C7_true B X s⟩

/-- OpenAI's term widths of a selection (`termWidths`, PackedShrinkStep.lean:71): the eight supply widths of
each motif. -/
noncomputable abbrev termW (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    X.packingData.Motif → Bool → Fin 4 → ℕ :=
  X.packingData.termWidths B X.shrinkNumber X.packingWidth s

/-- Term widths read from a stored term table: the supply widths (`MotifConversion.supplyWidths`, payload plus
the selector list) of the stored outer index of each motif; `0` for an empty slot. -/
noncomputable def storedWidths (X : State a (packingLaneBits a g)) (tm : OldArc X → Option (Bool × Fin 4 → ℕ))
    (m : X.packingData.Motif) (l : Bool) (e : Fin 4) : ℕ :=
  (tm m.val).elim 0 fun v => MotifConversion.supplyWidths B (demandW X m) v (l, e)

theorem storedWidths_trueTerms (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    storedWidths B X (trueTerms B X s) = termW B X s := by
  funext m l e
  rw [storedWidths, trueTerms_motif]
  rfl

/-- The source base of a motif's old wire (terms and energies are keyed there). -/
def motifBase (X : State a (packingLaneBits a g)) (m : X.packingData.Motif) : X.Base := m.val.1.1.1

/-- The energy of base `y` in layout group `l` for term widths `W`: over the motifs keyed at `y`, the sum of
`c_e W(m, l, e)^2` with OpenAI's coefficients `c = (10, 20, 6, 5)` (`P1P7.layoutCoeff`; `groupEnergy` cleared of
its denominator, `P1P7.groupEnergy_eq`). -/
noncomputable def energyAt (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ) (y : X.Base)
    (l : Bool) : ℕ :=
  ∑ m ∈ Finset.univ.filter (fun m => motifBase X m = y), ∑ e, P1P7.layoutCoeff e * W m l e ^ 2

/-- The true energy prefix `E_l(y)`: the energies of all bases up to `y` in base order. -/
noncomputable def truePrefix (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ) (y : X.Base)
    (l : Bool) : ℕ :=
  ∑ z ∈ Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex y), energyAt X W z l

/-- The base before `y` in base order (for the first base, `y` itself; C8 then reads `0`). -/
def prevBase (X : State a (packingLaneBits a g)) (y : X.Base) : X.Base :=
  X.baseIndex.symm ⟨(X.baseIndex y : ℕ) - 1, (Nat.sub_le _ _).trans_lt (X.baseIndex y).isLt⟩

theorem prevBase_index (X : State a (packingLaneBits a g)) (y : X.Base) :
    (X.baseIndex (prevBase X y) : ℕ) = (X.baseIndex y : ℕ) - 1 := by
  simp [prevBase]

/-- **C8** at base `y`: `E_l(y) = E_l(y - 1) + energy_l(y)` for both layout groups `l`, with `E_l(-1) = 0`. -/
def C8 (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ)
    (E : X.Base → Bool → ℕ) (y : X.Base) : Prop :=
  ∀ l, E y l = (if 0 < (X.baseIndex y : ℕ) then E (prevBase X y) l else 0) + energyAt X W y l

theorem C8_true (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ)
    (y : X.Base) : C8 X W (truePrefix X W) y := by
  intro l
  have hp := prevBase_index X y
  split_ifs with hy
  · have hset : Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex y) =
        insert y (Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex (prevBase X y))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.le_iff_val_le_val, hp]
      constructor
      · intro hz
        by_cases hzy : z = y
        · exact Or.inl hzy
        · right
          have hne : (X.baseIndex z : ℕ) ≠ X.baseIndex y := fun h =>
            hzy (X.baseIndex.injective (Fin.ext h))
          omega
      · rintro (hzy | hz)
        · rw [hzy]
        · omega
    have hnot : y ∉ Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex (prevBase X y)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, hp, not_le]
      omega
    unfold truePrefix
    rw [hset, Finset.sum_insert hnot]
    exact Nat.add_comm _ _
  · have hy0 : (X.baseIndex y : ℕ) = 0 := by omega
    have hset : Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex y) = {y} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.le_iff_val_le_val, hy0]
      constructor
      · intro hz
        exact X.baseIndex.injective (Fin.ext (by omega))
      · rintro rfl
        omega
    unfold truePrefix
    rw [hset, Finset.sum_singleton, Nat.zero_add]

theorem C8_unique (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ)
    {E : X.Base → Bool → ℕ} (h : ∀ y, C8 X W E y) : E = truePrefix X W := by
  refine unique_of_earlier X.baseIndex (C8 X W) ?_ h (C8_true X W)
  intro f f' y hf hf' hearly
  funext l
  rw [hf l, hf' l]
  split_ifs with hy
  · rw [hearly (prevBase X y) ?_]
    rw [Fin.lt_def, prevBase_index]
    omega
  · rfl

theorem C8_iff (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ)
    (E : X.Base → Bool → ℕ) : (∀ y, C8 X W E y) ↔ E = truePrefix X W :=
  ⟨C8_unique X W, fun h => h ▸ C8_true X W⟩

/-- The last base in base order. -/
def lastBase (X : State a (packingLaneBits a g)) : X.Base :=
  X.baseIndex.symm ⟨Fintype.card X.Base - 1, Nat.sub_lt Fintype.card_pos Nat.one_pos⟩

/-- The true prefix at the last base is the whole sum over all motifs. -/
theorem truePrefix_last (X : State a (packingLaneBits a g)) (W : X.packingData.Motif → Bool → Fin 4 → ℕ)
    (l : Bool) : truePrefix X W (lastBase X) l = ∑ m, ∑ e, P1P7.layoutCoeff e * W m l e ^ 2 := by
  have hall : Finset.univ.filter (fun z => X.baseIndex z ≤ X.baseIndex (lastBase X)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro z _
    rw [Fin.le_iff_val_le_val]
    simp only [lastBase, Equiv.apply_symm_apply]
    have := (X.baseIndex z).isLt
    omega
  rw [truePrefix, hall]
  unfold energyAt
  exact Finset.sum_fiberwise Finset.univ (motifBase X) _

/-- **C9** (one per shrinking level): the stored layout bit is `decide (E true < E false)` at the last base; ties
give `false` (paper layout 1), as OpenAI's `chosenLayout`. -/
def C9 (X : State a (packingLaneBits a g)) (E : X.Base → Bool → ℕ) (lb : Bool) : Prop :=
  lb = decide (E (lastBase X) true < E (lastBase X) false)

theorem C9_true (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    C9 X (truePrefix X (termW B X s)) (P1P7.layoutBit B X s) := by
  unfold C9
  rw [truePrefix_last, truePrefix_last]
  exact P1P7.layoutBit_eq_int B X s

theorem C9_unique (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) {lb : Bool}
    (h : C9 X (truePrefix X (termW B X s)) lb) : lb = P1P7.layoutBit B X s :=
  h.trans (C9_true B X s).symm

theorem C9_iff (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (lb : Bool) :
    C9 X (truePrefix X (termW B X s)) lb ↔ lb = P1P7.layoutBit B X s :=
  ⟨C9_unique B X s, fun h => h ▸ C9_true B X s⟩

/-! ## 6. One shrinking level of lem:unique -/

/-- Existence half: the true fields of an admitted selection `s` pass C5-C9 at every index. -/
theorem level_true (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    (∀ y, C5s X X.packingData.color y) ∧ (∀ y, C6s X X.packingData.offset y) ∧
      (∀ e, C7 B X (trueTerms B X s) e) ∧
      (∀ y, C8 X (storedWidths B X (trueTerms B X s)) (truePrefix X (termW B X s)) y) ∧
      C9 X (truePrefix X (termW B X s)) (P1P7.layoutBit B X s) := by
  refine ⟨C5s_true X, C6s_true X, C7_true B X s, ?_, C9_true B X s⟩
  rw [storedWidths_trueTerms]
  exact C8_true X _

/-- Uniqueness half: stored fields that pass C5-C9 at every index are the true colours and offsets, and the term
table, energy prefixes and layout bit of exactly one admitted selection `s`. -/
theorem level_unique (X : State a (packingLaneBits a g)) {col : X.Base → Fin (2 * 2 ^ a + 1)}
    {off : X.Base → BitWord (packingTagBits (2 ^ a))} {tm : OldArc X → Option (Bool × Fin 4 → ℕ)}
    {E : X.Base → Bool → ℕ} {lb : Bool}
    (h5 : ∀ y, C5s X col y) (h6 : ∀ y, C6s X off y) (h7 : ∀ e, C7 B X tm e)
    (h8 : ∀ y, C8 X (storedWidths B X tm) E y) (h9 : C9 X E lb) :
    col = X.packingData.color ∧ off = X.packingData.offset ∧
      ∃! s : X.ShrinkSelection B, tm = trueTerms B X s ∧ E = truePrefix X (termW B X s) ∧
        lb = P1P7.layoutBit B X s := by
  obtain ⟨s, hs, huniq⟩ := C7_unique B X h7
  have hE : E = truePrefix X (termW B X s) := by
    apply C8_unique
    intro y
    have h8y := h8 y
    rwa [hs, storedWidths_trueTerms] at h8y
  refine ⟨C5s_unique X h5, C6s_unique X h6, s, ⟨hs, hE, ?_⟩, fun s' hs' => huniq s' hs'.1⟩
  rw [hE] at h9
  exact C9_unique B X s h9

end Terms

end P1ChkGreedy
