import P1ChkFinal.C7RTarget

open OAI.Computability.IntegerMultiplication Code
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.VPVNP.SpectralGeometry
open P1Wit P1ChkFinal P1ChkGreedy P1SolGreedy.SolDemand

namespace P1SolC7R.SolC7R

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

noncomputable section

/-- Term key count, term stride, lane count, residual radix, and full lane radix. -/
abbrev ExtraRow := NumberWord × NumberWord × NumberWord × NumberWord × NumberWord
abbrev Format := PublicFmt × List (NumberWord × ExtraRow)
/-- The witness length and guard, selected level rows, and decoded base and term key. -/
abbrev Context := (NumberWord × Bool) × (BaseRow × ExtraRow) × (NumberWord × NumberWord)

def extraRow (a : ℕ) (D : Dims) (ℓ : ℕ) : ExtraRow :=
  let L := D.lv ℓ
  (bin L.termKeys, bin (L.termArity + 1), bin L.lanes, bin (2 ^ (L.laneW - a)),
    bin (2 ^ (a + (L.laneW - a))))

def format (a : ℕ) (D : Dims) (m : ℕ) : Format :=
  (fmtGreedy D m, (List.range (D.top + 1)).map fun ℓ => (bin ℓ, extraRow a D ℓ))

def setup (p : Format × NumberWord) : Context :=
  let j := Carry.nat_div (p.2, p.1.1.1)
  let row := selectRow defaultRow (j.2, p.1.1.2.2)
  let extra := selectRow (default : ExtraRow) (j.2, p.1.2)
  let cell := Carry.nat_div (j.1, extra.1)
  ((p.1.1.2.1, !row.1 && Carry.lt_ (j.1, Carry.times0 (row.2.1, extra.1))),
    (row, extra), cell)

theorem setup_poly : Poly setup := by
  have hr := selectRow_poly defaultRow
  have he := selectRow_poly (default : ExtraRow)
  unfold setup
  dsimp only
  fun_prop

def setupIndex (a : ℕ) (dims : ℕ → Dims) (M : ℕ → ℕ) (z : IndexWord) : Context :=
  setup (format a (dims (P1Batch.bval z.1)) (M (P1Batch.bval z.1)), z.2)

theorem setup_row (a : ℕ) (D : Dims) (m : ℕ) (i : NumberWord) :
    (setup (format a D m, i)).2.1.1 =
      if P1Batch.bval i % 2 ^ P1ChkGreedy.levBits D ≤ D.top then
        levelRow D (P1Batch.bval i % 2 ^ P1ChkGreedy.levBits D) else defaultRow := by
  change selectRow defaultRow ((Carry.nat_div (i, bin (2 ^ P1ChkGreedy.levBits D))).2, (fmtGreedy D m).2.2) = _
  rw [selectRow_level, (bval_divide _ _).2, bval_bin]

theorem setup_spec (a : ℕ) (D : Dims) (m : ℕ) (i : NumberWord) :
    let q := setup (format a D m, i)
    let ℓ := P1Batch.bval i % 2 ^ P1ChkGreedy.levBits D
    let j := P1Batch.bval i / 2 ^ P1ChkGreedy.levBits D
    (q.1.2 = true ↔ ShrinkIdx (P1ChkFinal.C7R.refDims D) (P1Batch.bval i)) ∧
      (ℓ ≤ D.top → q.2.1 = (levelRow D ℓ, extraRow a D ℓ) ∧
        P1Batch.bval q.2.2.1 = j / (D.lv ℓ).termKeys ∧
        P1Batch.bval q.2.2.2 = j % (D.lv ℓ).termKeys) := by
  let ℓ := P1Batch.bval i % 2 ^ P1ChkGreedy.levBits D
  let j := P1Batch.bval i / 2 ^ P1ChkGreedy.levBits D
  let w := Carry.nat_div (i, bin (2 ^ P1ChkGreedy.levBits D))
  let r := selectRow defaultRow (w.2, (fmtGreedy D m).2.2)
  let e := selectRow (default : ExtraRow) (w.2, (format a D m).2)
  have hj : P1Batch.bval w.1 = j := by unfold w; rw [(bval_divide _ _).1, bval_bin]
  have hl : P1Batch.bval w.2 = ℓ := by unfold w; rw [(bval_divide _ _).2, bval_bin]
  have hr : r = if ℓ ≤ D.top then levelRow D ℓ else defaultRow := by
    unfold r; rw [selectRow_level, hl]
  have he : e = if ℓ ≤ D.top then extraRow a D ℓ else default := by
    unfold e format
    rw [selectRow_table, hl]
    simp only [Nat.lt_succ_iff]
  change ((!r.1 && Carry.lt_ (w.1, Carry.times0 (r.2.1, e.1))) = true ↔
      (ℓ ≤ D.top ∧ (!(D.lv ℓ).shrink) = true ∧ j < (D.lv ℓ).bases * (D.lv ℓ).termKeys)) ∧
    (ℓ ≤ D.top → (r, e) = (levelRow D ℓ, extraRow a D ℓ) ∧
      P1Batch.bval (Carry.nat_div (w.1, e.1)).1 = j / (D.lv ℓ).termKeys ∧
      P1Batch.bval (Carry.nat_div (w.1, e.1)).2 = j % (D.lv ℓ).termKeys)
  rw [hr, he]
  by_cases h : ℓ ≤ D.top
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [Bool.and_eq_true, less_spec, decide_eq_true_eq, bval_mul, hj,
      (bval_divide _ _).1, (bval_divide _ _).2, levelRow, extraRow, bval_bin, h, true_and,
      and_self, implies_true]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [h, false_and, false_implies, and_true, Bool.and_eq_true, less_spec,
      decide_eq_true_eq, bval_mul, hj, defaultRow, P1Batch.bval, Nat.zero_mul, Nat.not_lt_zero,
      and_false]

open P1SolFmt.SolFmtAg P1SolFmt.SolFigure P1SolFmt.SolFormat Staff in
private theorem extraRow_poly (a : ℕ) {D : NumberWord → Dims}
    (h : AgFigures (fun p => (D p.1).lv p.2.length)) :
    Poly (fun p : LevelInput => extraRow a (D p.1) p.2.length) := by
  let R := inputRegime LevelInput
  have hw : Realizes R (fun p => ((D p.1).lv p.2.length).laneW) :=
    h.level.laneW.pay ((diameter _ h.packedTally).mono (fun p => by
      let L := (D p.1).lv p.2.length
      change L.laneW ≤ 2 ^ packedBits L
      have hle : L.laneW ≤ packedBits L := by
        unfold packedBits residualBits
        rw [← packingLaneBits_add]
        omega
      exact hle.trans (Nat.le_of_lt Nat.lt_two_pow_self)))
  have hg := hw.minused (Staff.Realizes.fix a)
  have hlow := (Carry.Figure.natural (r := R) 2).repeated hg
  have hfull := (Carry.Figure.natural (r := R) 2).repeated ((Staff.Realizes.fix a).plus hg)
  unfold extraRow
  exact (bin_poly h.level.termKeys).pair
    ((bin_poly (h.level.termArity.added (Carry.Figure.natural 1))).pair
      ((bin_poly h.level.lanes).pair ((bin_poly hlow).pair (bin_poly hfull))))

theorem format_genuine {k : Type*} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine)
    (aM a b d bigBias termBias port : ℕ) :
    Poly (fun w : NumberWord =>
      format port (P1ChkFinal.FamGreedy.gDims A Kc V aM a b d bigBias termBias (P1Batch.bval w))
        (P1Int.lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b (P1Batch.bval w))) := by
  rw [← P1ChkFinal.FamGreedy.m_eq_lpM2_fun Kc a b]
  exact (P1SolFmt.fmtHypGreedy_genuine A Kc V aM a b d bigBias termBias).pair
    (P1SolFmt.SolFmtAg.genuineRows_poly A Kc V aM a b d bigBias termBias
      (extraRow port) (extraRow_poly port))

private theorem fixedMap_poly {X A B : Type} [Codec X] [Codec B]
    (xs : List A) (f : A → X → B) (hf : ∀ i, Poly (f i)) :
    Poly (fun x => xs.map fun i => f i x) := by
  induction xs with
  | nil => exact Code.Poly.const (X := X) ([] : List B)
  | cons i xs ih => exact ((hf i).pair ih).compose Poly.cons

variable {a : ℕ}

abbrev First := Context × FieldCache
abbrev Reads := First × FieldCache

def termAt (p : Context × NumberWord) : P1Batch.Req :=
  let q := p.1
  let e := q.2.1.2
  let slot := joinWords (q.2.2.1, e.1, q.2.2.2)
  fieldWords (rowSection .terms q.2.1.1, joinWords (slot, e.2.1, p.2))

@[fun_prop] theorem termAt_poly : Poly termAt := by unfold termAt; dsimp only; fun_prop

def termCol {a dH : ℕ} (j : Fin (2 ^ a) × Fin dH) : NumberWord :=
  bin (1 + (j.1.val * dH + j.2.val))

abbrev slots (a : ℕ) : List (Fin (2 ^ a)) := List.finRange _
abbrev edges (a dH : ℕ) : List (Fin (2 ^ a) × Fin dH) := Finset.univ.toList
abbrev ties (a : ℕ) : List (Tie (2 ^ a)) := Finset.univ.toList

def inAt (c : Mem) (s : Fin (2 ^ a)) (q : Context) : P1Batch.Req :=
  slotAt c (q.2.1.1, q.2.2.1, bin s.val)

@[fun_prop] theorem inAt_poly (c : Mem) (s : Fin (2 ^ a)) : Poly (inAt c s) := by
  unfold inAt
  fun_prop

/-- Fetch the selected term slot and the incoming endpoints of its base. -/
def firstRaw (a dH : ℕ) (q : Context) : List P1Batch.Req :=
  (termAt (q, []) :: (edges a dH).map (fun j => termAt (q, termCol j))) ++
    (((slots a).map fun s => [inAt .inAddr s q, inAt .inDisp s q, inAt .inFar s q]).flatten)

theorem firstRaw_poly (a dH : ℕ) : Poly (firstRaw a dH) := by
  have ht := fixedMap_poly (edges a dH) (fun j (q : Context) => termAt (q, termCol j)) (by
    intro j; fun_prop)
  have hi := fixedMap_poly (slots a) (fun s (q : Context) => [inAt .inAddr s q, inAt .inDisp s q, inAt .inFar s q])
    (by intro s; fun_prop)
  unfold firstRaw
  exact (((by fun_prop : Poly (fun q : Context => termAt (q, []))).pair ht).compose Poly.cons).pair
    (hi.compose Easy.flatten.poly) |>.compose
      (show Poly (fun p : List P1Batch.Req × List P1Batch.Req => p.1 ++ p.2) from by fun_prop)

def firstReq (a dH : ℕ) (q : Context) : List P1Batch.Req :=
  clipRequests (q.1.1, firstRaw a dH q)

theorem firstReq_poly (a dH : ℕ) : Poly (firstReq a dH) := by
  have h := firstRaw_poly a dH
  unfold firstReq
  fun_prop

def firstNext (a dH : ℕ) (p : Context × List NumberWord) : First :=
  (p.1, cacheFields (firstRaw a dH p.1, p.2))

theorem firstNext_poly (a dH : ℕ) : Poly (firstNext a dH) := by
  have h := firstRaw_poly a dH
  unfold firstNext
  fun_prop

def widthAt (p : Context × NumberWord × NumberWord × NumberWord) : P1Batch.Req :=
  let q := p.1
  let z := joinWords (p.2.1, q.2.1.2.2.2.1, p.2.2.1)
  fieldWords (rowSection .width q.2.1.1, joinWords (z, q.2.1.1.2.2.1, p.2.2.2))

@[fun_prop] theorem widthAt_poly : Poly widthAt := by unfold widthAt; dsimp only; fun_prop

def inWord (c : Mem) (s : Fin (2 ^ a)) (p : First) : NumberWord :=
  cacheRead (p.2, inAt c s p.1)

@[fun_prop] theorem inWord_poly (c : Mem) (s : Fin (2 ^ a)) : Poly (inWord c s) := by
  unfold inWord
  fun_prop

def fullLane (j : Fin (2 ^ a)) (q : Context) : NumberWord :=
  let low := q.2.1.2.2.2.2.1
  joinWords (bin j.val, low, boundWord (low, q.2.2.2))

@[fun_prop] theorem fullLane_poly (j : Fin (2 ^ a)) : Poly (fullLane j) := by
  unfold fullLane
  dsimp only
  fun_prop

def tieRequest (t : Tie (2 ^ a)) (p : First) : P1Batch.Req :=
  let q := p.1
  let s := t.2.val.2
  let lane := fullLane t.2.val.1 q
  if t.1 then widthAt (q, q.2.2.1, lane, bin s.val)
  else
    let far := (Carry.nat_div (inWord .inFar s p, bin (2 ^ a))).2
    let δ := boundWord (q.2.1.2.2.2.2.2, inWord .inDisp s p)
    widthAt (q, inWord .inAddr s p, xorWords (lane, δ), far)

theorem tieRequest_poly (t : Tie (2 ^ a)) : Poly (tieRequest t) := by
  unfold tieRequest
  dsimp only
  cases t.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- Fetch the out-width selected by each tie after undoing its incoming displacement, if any. -/
def secondRaw (a : ℕ) (p : First) : List P1Batch.Req :=
  (ties a).map fun t => tieRequest t p

theorem secondRaw_poly (a : ℕ) : Poly (secondRaw a) :=
  fixedMap_poly _ _ tieRequest_poly

def secondReq (a : ℕ) (p : First) : List P1Batch.Req :=
  clipRequests (p.1.1.1, secondRaw a p)

theorem secondReq_poly (a : ℕ) : Poly (secondReq a) := by
  have h := secondRaw_poly a
  unfold secondReq
  fun_prop

def secondNext (a : ℕ) (p : First × List NumberWord) : Reads :=
  (p.1, cacheFields (secondRaw a p.1, p.2))

theorem secondNext_poly (a : ℕ) : Poly (secondNext a) := by
  have h := secondRaw_poly a
  unfold secondNext
  fun_prop

def termWord (f : NumberWord) (p : Reads) : NumberWord :=
  cacheRead (p.1.2, termAt (p.1.1, f))

@[fun_prop] theorem termWord_poly (f : NumberWord) : Poly (termWord f) := by
  unfold termWord
  fun_prop

def demandWord (t : Tie (2 ^ a)) (p : Reads) : NumberWord :=
  cacheRead (p.2, tieRequest t p.1)

@[fun_prop] theorem demandWord_poly (t : Tie (2 ^ a)) : Poly (demandWord t) := by
  have h := tieRequest_poly t
  unfold demandWord
  fun_prop

private theorem termAt_mem (a dH : ℕ) (q : Context) (f : NumberWord)
    (hf : f = [] ∨ ∃ j : Fin (2 ^ a) × Fin dH, f = termCol j) :
    termAt (q, f) ∈ firstRaw a dH q := by
  apply List.mem_append_left
  rcases hf with rfl | ⟨j, rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ j)))

private theorem inAt_mem (a dH : ℕ) (q : Context) (s : Fin (2 ^ a)) (c : Mem)
    (hc : c = .inAddr ∨ c = .inDisp ∨ c = .inFar) :
    inAt c s q ∈ firstRaw a dH q := by
  apply List.mem_append_right
  apply List.mem_flatten.mpr
  refine ⟨_, List.mem_map_of_mem (List.mem_finRange s), ?_⟩
  rcases hc with rfl | rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem termAt_numbers (a : ℕ) (D : Dims) (ℓ : ℕ) (len Y key f : NumberWord) :
    requestNumbers (termAt (((len, true), (levelRow D ℓ, extraRow a D ℓ), Y, key), f)) =
      requestNumbers (fieldReq D (secLev ℓ .terms)
        ((P1Batch.bval Y * (D.lv ℓ).termKeys + P1Batch.bval key) *
          ((D.lv ℓ).termArity + 1) + P1Batch.bval f)) := by
  simp only [termAt, requestNumbers_rowField, bval_joinWords, extraRow, bval_bin]

private theorem widthAt_numbers (a : ℕ) (D : Dims) (ℓ : ℕ) (len Y key Z lane s : NumberWord) :
    requestNumbers (widthAt (((len, true), (levelRow D ℓ, extraRow a D ℓ), Y, key), Z, lane, s)) =
      requestNumbers (fieldReq D (secLev ℓ .width)
        ((P1Batch.bval Z * (D.lv ℓ).lanes + P1Batch.bval lane) * (D.lv ℓ).slots + P1Batch.bval s)) := by
  unfold widthAt
  rw [requestNumbers_rowField]
  simp only [bval_joinWords, extraRow, levelRow, bval_bin]

private theorem cache_fetch_value (D : Dims) (u : List Bool) (rs : List P1Batch.Req)
    {r : P1Batch.Req} (hr : r ∈ rs) (m i : ℕ)
    (he : requestNumbers r = requestNumbers (fieldReq D m i)) :
    P1Batch.bval (cacheRead (rs.map (fun q => (q, P1Batch.fetch u q)), r)) = readField D u m i := by
  rw [cacheRead_fetch _ _ _ ⟨r, hr, rfl⟩, fetch_of_requestNumbers _ he, bval_bitsVal, ← readField_eq]

def activeContext (a : ℕ) (D : Dims) (ℓ : ℕ) (len Y key : NumberWord) : Context :=
  ((len, true), (levelRow D ℓ, extraRow a D ℓ), Y, key)

def readFirst (a dH : ℕ) (q : Context) (u : List Bool) : First :=
  (q, (firstRaw a dH q).map fun r => (r, P1Batch.fetch u r))

def readAll (a dH : ℕ) (q : Context) (u : List Bool) : Reads :=
  let p := readFirst a dH q u
  (p, (secondRaw a p).map fun r => (r, P1Batch.fetch u r))

theorem termWord_value (a dH : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y key f : NumberWord)
    (hf : f = [] ∨ ∃ j : Fin (2 ^ a) × Fin dH, f = termCol j) :
    P1Batch.bval (termWord f (readAll a dH (activeContext a D ℓ len Y key) u)) =
      rdTerms D u ℓ (P1Batch.bval Y) (P1Batch.bval key) (P1Batch.bval f) :=
  cache_fetch_value D u _ (termAt_mem a dH _ f hf) _ _ (termAt_numbers a D ℓ len Y key f)

private theorem inWord_value (a dH : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y key : NumberWord)
    (s : Fin (2 ^ a)) (c : Mem) (hc : c = .inAddr ∨ c = .inDisp ∨ c = .inFar) :
    P1Batch.bval (inWord c s (readFirst a dH (activeContext a D ℓ len Y key) u)) =
      readField D u (secLev ℓ c) (P1Batch.bval Y * (D.lv ℓ).slots + s.val) := by
  apply cache_fetch_value D u _ (inAt_mem a dH _ s c hc)
  unfold inAt activeContext
  rw [requestNumbers_slotAt, bval_bin]

private theorem bwNum_boundWord (n : ℕ) (v : NumberWord) :
    P1Batch.bval (boundWord (bin (2 ^ n), v)) = bwNum (bwOf n (P1Batch.bval v)) := by
  let : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩
  rw [bval_boundWord]
  unfold bwOf bwNum finOr0
  split
  · rw [Equiv.apply_symm_apply]
  · rw [Equiv.apply_symm_apply]
    rfl

private def oldLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) : BitWord (a + g) :=
  (splitBitWord a g).symm ((bitWordFinEquiv a).symm p, l)

private theorem number_oldLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) :
    bwNum (oldLane p l) = p.val * 2 ^ g + bwNum l := by
  unfold bwNum oldLane
  rw [splitBitWord_number, AddEquiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem number_sub {n : ℕ} (v d : BitWord n) :
    bwNum (v - d) = bwNum v ^^^ bwNum d := by
  exact bitWord_code_sub _ _

private theorem incomingLane {a g : ℕ} (p : Fin (2 ^ a)) (l : BitWord g) (d : BitWord (a + g)) :
    (splitBitWord a g).symm ((bitWordFinEquiv a).symm
      (((bitWordFinEquiv a).symm.trans ((Equiv.addRight (splitBitWord a g d).1).trans
        (bitWordFinEquiv a))).symm p), l - (splitBitWord a g d).2) = oldLane p l - d := by
  apply (splitBitWord a g).injective
  simp only [oldLane, map_sub, AddEquiv.apply_symm_apply]
  apply Prod.ext
  · change (bitWordFinEquiv a).symm ((bitWordFinEquiv a)
        (((bitWordFinEquiv a).symm p) + -(splitBitWord a g d).1)) =
      (bitWordFinEquiv a).symm p - (splitBitWord a g d).1
    rw [Equiv.symm_apply_apply, sub_eq_add_neg]
  · rfl

private theorem fullLane_value (a : ℕ) (D : Dims) (ℓ : ℕ) (len Y key : NumberWord) (j : Fin (2 ^ a)) :
    P1Batch.bval (fullLane j (activeContext a D ℓ len Y key)) =
      bwNum (oldLane j (bwOf ((D.lv ℓ).laneW - a) (P1Batch.bval key))) := by
  simp only [fullLane, activeContext, extraRow, bval_joinWords, bval_bin, bwNum_boundWord, number_oldLane]

theorem demandWord_value (a dH : ℕ) (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y key : NumberWord)
    (t : Tie (2 ^ a)) :
    P1Batch.bval (demandWord t (readAll a dH (activeContext a D ℓ len Y key) u)) =
      C7R.bwS a ((D.lv ℓ).laneW - a) D u ℓ (P1Batch.bval Y)
        (bwOf ((D.lv ℓ).laneW - a) (P1Batch.bval key)) t := by
  let q := activeContext a D ℓ len Y key
  let p := readFirst a dH q u
  let s := t.2.val.2
  let lane := fullLane t.2.val.1 q
  have hmem : tieRequest t p ∈ secondRaw a p :=
    List.mem_map_of_mem (Finset.mem_toList.mpr (Finset.mem_univ t))
  have hl := fullLane_value a D ℓ len Y key t.2.val.1
  change P1Batch.bval (cacheRead ((secondRaw a p).map (fun r => (r, P1Batch.fetch u r)), tieRequest t p)) = _
  cases ht : t.1
  · let z := inWord .inAddr s p
    let δ := boundWord (bin (2 ^ (a + ((D.lv ℓ).laneW - a))), inWord .inDisp s p)
    let far := (Carry.nat_div (inWord .inFar s p, bin (2 ^ a))).2
    have hr : tieRequest t p = widthAt (q, z, xorWords (lane, δ), far) := by
      simp only [tieRequest, ht, Bool.false_eq_true, ite_false]
      rfl
    have hz : P1Batch.bval z = rdInAddr D u ℓ (P1Batch.bval Y) s :=
      inWord_value a dH D u ℓ len Y key s .inAddr (Or.inl rfl)
    have hd : P1Batch.bval δ = bwNum (bwOf (a + ((D.lv ℓ).laneW - a)) (rdInDisp D u ℓ (P1Batch.bval Y) s)) := by
      unfold δ
      rw [bwNum_boundWord, inWord_value a dH D u ℓ len Y key s .inDisp (Or.inr (Or.inl rfl))]
      rfl
    have hf : P1Batch.bval far = (C7R.inFarS a D u ℓ (P1Batch.bval Y) s).val := by
      unfold far C7R.inFarS
      rw [(bval_divide _ _).2, bval_bin, inWord_value a dH D u ℓ len Y key s .inFar (Or.inr (Or.inr rfl))]
      rfl
    have hread := cache_fetch_value D u _ (hr ▸ hmem) _ _
      (widthAt_numbers a D ℓ len Y key z (xorWords (lane, δ)) far)
    rw [hr]
    apply hread.trans
    change rdWidth D u ℓ (P1Batch.bval z) (P1Batch.bval (xorWords (lane, δ))) (P1Batch.bval far) = _
    simp only [C7R.bwS, P1P7.demandOf, ht, Bool.false_eq_true, ite_false, incomingLane,
      number_sub, bval_xorWords, hz, hd, hf, show P1Batch.bval lane = _ from hl, s]
  · have hr : tieRequest t p = widthAt (q, Y, lane, bin s.val) := by
      simp only [tieRequest, ht, ite_true]
      rfl
    have hread := cache_fetch_value D u _ (hr ▸ hmem) _ _
      (widthAt_numbers a D ℓ len Y key Y lane (bin s.val))
    rw [hr]
    apply hread.trans
    change rdWidth D u ℓ (P1Batch.bval Y) (P1Batch.bval lane) (P1Batch.bval (bin s.val)) = _
    simp only [C7R.bwS, P1P7.demandOf, ht, ite_true, bval_bin,
      show P1Batch.bval lane = _ from hl, s, oldLane]


private def energyWords {I : Type} [Fintype I] (mass : I → ℚ) (w : I → Reads → NumberWord)
    (s : Reads) : NumberWord :=
  sumWords (Finset.univ.toList.map fun i => weightedSquare (bin (MotifAdmission.weight mass i), w i s))

private theorem energyWords_poly {I : Type} [Fintype I] (mass : I → ℚ)
    (w : I → Reads → NumberWord) (hw : ∀ i, Poly (w i)) : Poly (energyWords mass w) := by
  apply Poly.compose _ sumWords_poly
  exact fixedMap_poly _ _ (fun i =>
    ((Code.Poly.const (X := Reads) (bin (MotifAdmission.weight mass i))).pair (hw i)).compose
      weightedSquare_poly)

private theorem energyWords_value {I : Type} [Fintype I] (mass : I → ℚ)
    (w : I → Reads → NumberWord) (s : Reads) (v : I → ℕ) (h : ∀ i, P1Batch.bval (w i s) = v i) :
    P1Batch.bval (energyWords mass w s) = MotifAdmission.energy mass v := by
  simp only [energyWords, bval_sumWords, List.map_map, Function.comp_def, weightedSquare_value,
    bval_bin, h, MotifAdmission.energy, Finset.sum_map_toList]

private def copiesAt (a L : ℕ) (s : Reads) : NumberWord :=
  let p : Tie (2 ^ a) → ℚ := Refresh.tieMass
  ceilRootWords (energyWords p demandWord s, bin (L ^ 2 * MotifAdmission.denominator p))

@[fun_prop] private theorem copiesAt_poly (a L : ℕ) : Poly (copiesAt a L) := by
  have h := energyWords_poly (Refresh.tieMass (D := 2 ^ a)) demandWord demandWord_poly
  unfold copiesAt
  dsimp only
  fun_prop

private def admissionWords (a dH a₀ L radNum radDen : ℕ) (s : Reads) : Bool :=
  let q : Fin (2 ^ a) × Fin dH → ℚ := Refresh.expanderMass a₀
  let e := energyWords q (fun j => termWord (termCol j)) s
  let used := Carry.times0 (e, bin (radDen ^ 2))
  let scaled := Carry.times0 (Carry.times0 (copiesAt a L s, bin L), bin radNum)
  let cap := weightedSquare (bin (MotifAdmission.denominator q), scaled)
  bitAnd (numberEq (termWord [] s, [true]), !Carry.lt_ (cap, used))

private theorem admissionWords_poly (a dH a₀ L radNum radDen : ℕ) :
    Poly (admissionWords a dH a₀ L radNum radDen) := by
  have h := energyWords_poly (Refresh.expanderMass (D := 2 ^ a) (dH := dH) a₀)
    (fun j => termWord (termCol j)) (fun j => termWord_poly (termCol j))
  unfold admissionWords
  dsimp only
  fun_prop

private def decideReads (a dH a₀ L radNum radDen : ℕ) (s : Reads) : Bool :=
  bif s.1.1.1.2 then admissionWords a dH a₀ L radNum radDen s else true

private theorem decideReads_poly (a dH a₀ L radNum radDen : ℕ) :
    Poly (decideReads a dH a₀ L radNum radDen) := by
  have h := admissionWords_poly a dH a₀ L radNum radDen
  unfold decideReads
  fun_prop

section Refresh

variable {a a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')

private theorem admissionWords_correct (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y key : NumberWord) :
    admissionWords a dH (2 ^ a₀) F.scale F.radius.num.natAbs F.radius.den
          (readAll a dH (activeContext a D ℓ len Y key) u) = true ↔
      C7R.C7Rat (g := (D.lv ℓ).laneW - a) P hdH hconn F D u ℓ (P1Batch.bval Y) (P1Batch.bval key) := by
  let s := readAll a dH (activeContext a D ℓ len Y key) u
  let w := C7R.bwS a ((D.lv ℓ).laneW - a) D u ℓ (P1Batch.bval Y)
    (bwOf ((D.lv ℓ).laneW - a) (P1Batch.bval key))
  let v := C7R.storedVec a dH D u ℓ (P1Batch.bval Y) (P1Batch.bval key)
  let q : Fin (2 ^ a) × Fin dH → ℚ := Refresh.expanderMass (2 ^ a₀)
  let e := MotifAdmission.energy q v
  let c := MotifConversion.repetitions F w
  have hc : P1Batch.bval (copiesAt a F.scale s) = c := by
    unfold copiesAt c MotifConversion.repetitions MotifAdmission.copies
    rw [bval_ceilRootWords, bval_bin, energyWords_value _ _ _ w (demandWord_value a dH D u ℓ len Y key)]
  have hv (j : Fin (2 ^ a) × Fin dH) : P1Batch.bval (termWord (termCol j) s) = v j := by
    rw [termWord_value a dH D u ℓ len Y key _ (Or.inr ⟨j, rfl⟩)]
    simp only [termCol, bval_bin, v, C7R.storedVec]
  have hf := termWord_value a dH D u ℓ len Y key [] (Or.inl rfl)
  change admissionWords a dH (2 ^ a₀) F.scale F.radius.num.natAbs F.radius.den s = true ↔ _
  unfold admissionWords
  dsimp only
  rw [bitAnd, Bool.and_eq_true, numberEq_spec, less_spec, weightedSquare_value,
    bval_mul, bval_mul, bval_mul, bval_bin, bval_bin, bval_bin, bval_bin, hc,
    energyWords_value q _ s v hv, hf]
  change (_ = 1 ∧ (!decide (MotifAdmission.denominator q * (c * F.scale * F.radius.num.natAbs) ^ 2 <
    e * F.radius.den ^ 2)) = true) ↔
      (_ = 1 ∧ decide (e * F.radius.den ^ 2 ≤
        (c * F.scale * F.radius.num.natAbs) ^ 2 * MotifAdmission.denominator q) = true)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.mul_comm, P1Batch.bval]

open Classical in
theorem evaluate_correct (dims : ℕ → Dims) (M : ℕ → ℕ) (x u i : NumberWord)
    (hlen : u.length = M x.length) :
    let q := setupIndex a dims M (bin x.length, i)
    let p := firstNext a dH (q, (firstReq a dH q).map (P1Batch.fetch u))
    let s := secondNext a (p, (secondReq a p).map (P1Batch.fetch u))
    decideReads a dH (2 ^ a₀) F.scale F.radius.num.natAbs F.radius.den s =
      decide (C7R.C7Rfam P hdH hconn F dims x u (P1Batch.bval i)) := by
  let D := dims x.length
  let m := M x.length
  let ℓ := P1Batch.bval i % 2 ^ P1ChkGreedy.levBits D
  let q := setup (format a D m, i)
  have hq : setupIndex a dims M (bin x.length, i) = q := by
    simp only [setupIndex, bval_bin, q, D, m]
  have hu : P1Batch.bval q.1.1 = u.length := (bval_bin m).trans hlen.symm
  let p := readFirst a dH q u
  have hp : firstNext a dH (q, (firstReq a dH q).map (P1Batch.fetch u)) = p :=
    congrArg (fun c => (q, c)) (cacheFields_fetch u q.1.1 hu (firstRaw a dH q))
  have hs : secondNext a (p, (secondReq a p).map (P1Batch.fetch u)) = readAll a dH q u :=
    congrArg (fun c => (p, c)) (cacheFields_fetch u q.1.1 hu (secondRaw a p))
  dsimp only
  rw [hq, hp, hs, Bool.eq_iff_iff, decide_eq_true_eq]
  have hspec := setup_spec a D m i
  change (q.1.2 = true ↔ ShrinkIdx (C7R.refDims D) (P1Batch.bval i)) ∧
    (ℓ ≤ D.top → _) at hspec
  by_cases h : ShrinkIdx (C7R.refDims D) (P1Batch.bval i)
  · have hℓ : ℓ ≤ D.top := h.1
    have hactive : q.1.2 = true := hspec.1.mpr h
    obtain ⟨hrow, hY, hk⟩ := hspec.2 hℓ
    have hq' : q = activeContext a D ℓ q.1.1 q.2.2.1 q.2.2.2 :=
      Prod.ext (Prod.ext rfl hactive) (Prod.ext hrow rfl)
    change (bif q.1.2 then admissionWords a dH (2 ^ a₀) F.scale F.radius.num.natAbs F.radius.den
      (readAll a dH q u) else true) = true ↔ _
    rw [hactive, Bool.cond_true]
    conv_lhs => rw [hq']
    rw [admissionWords_correct P hdH hconn F, hY, hk]
    exact ⟨fun hc _ => hc, fun hc => hc h⟩
  · have hfalse : q.1.2 = false := Bool.eq_false_iff.mpr fun ht => h (hspec.1.mp ht)
    change (bif q.1.2 then _ else true) = true ↔ _
    rw [hfalse, Bool.cond_false]
    exact ⟨fun _ hh => (h hh).elim, fun _ => rfl⟩

private theorem firstWidths (a dH : ℕ) (q : Context) : RowWidths q.2.1.1 (firstRaw a dH q) := by
  apply rowWidths_append
  · exact rowWidths_cons (c := .terms) rfl (rowWidths_map _ _ _ .terms (fun _ _ => rfl))
  · intro r hr
    obtain ⟨rs, hrs, hm⟩ := List.mem_flatten.mp hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hrs
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨.inAddr, rfl⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨.inDisp, rfl⟩
    have he := List.mem_singleton.mp hm
    subst r
    exact ⟨.inFar, rfl⟩

private theorem secondWidths (a : ℕ) (p : First) : RowWidths p.1.2.1.1 (secondRaw a p) := by
  apply rowWidths_map (c := .width)
  intro t _
  unfold tieRequest
  dsimp only
  split <;> rfl

open Classical in
theorem task (dims : ℕ → Dims) (M KI : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp)
    (hfmt : Poly (fun w : NumberWord => format a (dims (P1Batch.bval w)) (M (P1Batch.bval w)))) :
    ∃ c : ℕ, Task (fun p : QDom M KI => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C7R.C7Rfam P hdH hconn F dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let f := setupIndex a dims M
  let q (p : QDom M KI) := f (SetupIdx p)
  let u (p : QDom M KI) := p.val.2.1
  let row (p : QDom M KI) := (q p).2.1.1
  let s (p : QDom M KI) := firstNext a dH (q p, (firstReq a dH (q p)).map (P1Batch.fetch (u p)))
  let ck (p : QDom M KI) := decide (C7R.C7Rfam P hdH hconn F dims p.val.1 (u p) (P1Batch.bval p.val.2.2))
  have hf : Poly f := (Poly.onleft hfmt).compose setup_poly
  have hq : Dom smallSize (fun p : QDom M KI => size (q p)) := (hf.length.map SetupIdx).sub index_size
  have hrow : Dom smallSize (fun p : QDom M KI => size (row p)) :=
    ((show Poly (fun q : Context => q.2.1.1) from by fun_prop).length.map q).sub hq
  have hpublic (p : QDom M KI) : q p = setup (format a (dims p.val.1.length) (M p.val.1.length), p.val.2.2) := by
    simp only [q, f, setupIndex, SetupIdx, bval_bin]
  have hlen (p : QDom M KI) : P1Batch.bval (q p).1.1 = (u p).length := by
    rw [hpublic]
    exact (bval_bin _).trans p.property.1.symm
  have hw (p : QDom M KI) (rs : List P1Batch.Req) (h : RowWidths (row p) rs) :
      ∀ r ∈ rs, P1Batch.bval r.2 ≤ size (row p) := by
    unfold row at h ⊢
    rw [hpublic, setup_row] at h ⊢
    split at h <;> rename_i hs
    · rw [ite_eq_left hs]
      exact rowWidths_le _ _ _ h
    · rw [ite_eq_right hs]
      exact rowWidths_default _ h
  have ht₁ := total_of_boundedRequests smallSize q row (firstReq a dH) (firstReq_poly a dH) hq hrow
    (fun p => hw p _ (rowWidths_clip _ _ _ (firstWidths a dH (q p))))
  have ha₁ (p : QDom M KI) (r : P1Batch.Req) (hr : r ∈ firstReq a dH (q p)) :
      P1Batch.bval r.1 ≤ (u p).length := (clipRequests_bound _ _ hr).trans_eq (hlen p)
  obtain ⟨t₀, ht₀, T₀⟩ := prepareWitness (M := M) (K := KI) hl f hf
  obtain ⟨t₁, ht₁', hsmall, T₁⟩ := batchPhase hb u q smallSize (firstReq a dH) (firstNext a dH)
    (firstReq_poly a dH) (firstNext_poly a dH) hq ht₁ ha₁
  have ht₂ := total_of_boundedRequests smallSize s row (secondReq a) (secondReq_poly a) hsmall hrow
    (fun p => hw p _ (rowWidths_clip _ _ _ (secondWidths a (s p))))
  have ha₂ (p : QDom M KI) (r : P1Batch.Req) (hr : r ∈ secondReq a (s p)) :
      P1Batch.bval r.1 ≤ (u p).length := (clipRequests_bound _ _ hr).trans_eq (hlen p)
  let check (r : First × List NumberWord) :=
    decideReads a dH (2 ^ a₀) F.scale F.radius.num.natAbs F.radius.den (secondNext a r)
  have hcheck : Poly check := (secondNext_poly a).compose (decideReads_poly _ _ _ _ _ _)
  have hck (p : QDom M KI) : ck p = check (s p, (secondReq a (s p)).map (P1Batch.fetch (u p))) :=
    (evaluate_correct P hdH hconn F dims M p.val.1 (u p) p.val.2.2 p.property.1).symm
  let cost (p : QDom M KI) := p.val.1.length + 3 * (u p).length + t₀ p + ((u p).length + t₁ p)
  have T : Task cost (fun p : QDom M KI => send p.val) (fun p => send (u p, s p)) := T₀.compose T₁
  obtain ⟨t₂, ht₂', T₂⟩ := checkSkeleton hb _ u s (secondReq a) check ck cost smallSize T
    ((secondReq_poly a).pair Poly.identity) hcheck hsmall ht₂ ha₂ hck
  apply pack_budget (E := 5) ((ht₀.add ht₁').add ht₂')
  exact T₂.bound 1 (fun p => by dsimp only [cost, u]; omega)

end Refresh
end
end P1SolC7R.SolC7R

open Classical in
theorem P1SolC7R.c7rProg_genuine {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)
    (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    P1ChkFinal.C7R.C7RProgTarget A Kc V aM a b d bigBias termBias := by
  let dims := P1ChkFinal.FamGreedy.gDims A Kc V aM a b d bigBias termBias
  let M := P1Int.lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b
  let KI := fun n => P1Int.lpK2 a b n - 4
  obtain ⟨c, T⟩ := P1SolC7R.SolC7R.task S.graph (Nat.two_pow_pos S.expanderExponent)
    (S.port_bound.connected_and_pos S.port_order).1 A.refresh dims M KI batchHyp P1SolFmt.SolLength.lenHyp
    (P1SolC7R.SolC7R.format_genuine A Kc V aM a b d bigBias termBias _)
  exact P1ProgDir.famProg_of_task hs hb _ c T

#print axioms P1SolC7R.c7rProg_genuine
