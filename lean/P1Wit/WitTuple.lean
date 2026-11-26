import P1Wit.WitPayload
import P1Count.Concrete

/-!
The P6 encoder on the dependent tuple used by the parity count. The records
are indexed by the numbering of `Dims`. A term record stores the presence
flag followed by the admitted index, and the final widths govern both the
payload slices and the base prefixes.
-/

namespace P1Wit

namespace SolWitfill

/-- Directory values before the fixed-width encoding. -/
structure Directory (D : Dims) where
  start : Fin (D.I * D.r) → ℤ
  prevOwn : Fin (D.I * D.r * 3) → Option (Fin D.I)
  nextOwn : Fin (D.I * D.r * 3) → Option (Fin D.I)
  guess : Fin D.nGB → Option (Fin D.I)
  start_fits : ∀ i, zigzag (start i) < 2 ^ D.bigW

def ownerCode {I : ℕ} (o : Option (Fin I)) : ℕ :=
  optCode (o.map Fin.val)

theorem ownerCode_lt {I b : ℕ} (hI : I < 2 ^ b) (o : Option (Fin I)) :
    ownerCode o < 2 ^ b := by
  cases o with
  | none => exact Nat.two_pow_pos _
  | some a => exact (Nat.succ_le_of_lt a.isLt).trans_lt hI

abbrev TermSlot (D : Dims) (L : LevelDims) :=
  Option (Fin L.termArity → Fin (2 ^ D.wW))

/-- True records at one level. Slot tables use base then slot; the width
table uses base, lane, then outgoing slot. -/
structure LevelRecords (D : Dims) (L : LevelDims) where
  layout : Bool
  outAddr : Fin (L.bases * L.slots) → Fin (2 ^ D.bigW)
  outDisp : Fin (L.bases * L.slots) → Fin (2 ^ L.laneW)
  outFar : Fin (L.bases * L.slots) → Fin (2 ^ L.slotW)
  inAddr : Fin (L.bases * L.slots) → Fin (2 ^ D.bigW)
  inDisp : Fin (L.bases * L.slots) → Fin (2 ^ L.laneW)
  inFar : Fin (L.bases * L.slots) → Fin (2 ^ L.slotW)
  width : Fin (L.bases * L.lanes * L.slots) → Fin (2 ^ D.wW)
  colour : Fin L.bases → Fin (2 ^ L.colW)
  offset : Fin L.bases → Fin (2 ^ L.tagW)
  energy : Fin (L.bases * 2) → Fin (2 ^ D.bigW)
  terms : Fin (L.bases * L.termKeys) → TermSlot D L

def termValue {D : Dims} {L : LevelDims} (t : TermSlot D L) : ℕ → ℕ
  | 0 => if t.isSome then 1 else 0
  | c + 1 => atIndex (fun j => (t.map (fun v => (v j).val)).getD 0) c

theorem termValue_lt {D : Dims} {L : LevelDims} (hw : 0 < D.wW)
    (t : TermSlot D L) (c : ℕ) : termValue t c < 2 ^ D.wW := by
  cases c with
  | zero =>
    cases t with
    | none => exact Nat.two_pow_pos _
    | some _ =>
      change 1 < 2 ^ D.wW
      exact Nat.one_lt_pow (by omega) (by decide)
  | succ c =>
    simp only [termValue]
    apply atIndex_lt
    intro j
    cases t with
    | none => exact Nat.two_pow_pos _
    | some v => exact (v j).isLt

theorem termValue_injective {D : Dims} {L : LevelDims} {t u : TermSlot D L}
    (h : ∀ c : Fin (L.termArity + 1), termValue t c.val = termValue u c.val) : t = u := by
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some v => exact False.elim (Nat.zero_ne_one (h 0))
  | some v =>
    cases u with
    | none => exact False.elim (Nat.one_ne_zero (h 0))
    | some w =>
      congr
      funext i
      apply Fin.ext
      simpa only [Fin.val_succ, termValue, atIndex_fin, Option.map_some, Option.getD_some]
        using h i.succ

def finValue {n b : ℕ} (f : Fin n → Fin b) (i : ℕ) : ℕ :=
  atIndex (fun j => (f j).val) i

theorem finValue_fin {n b : ℕ} (f : Fin n → Fin b) (i : Fin n) :
    finValue f i.val = (f i).val := atIndex_fin _ i

theorem finValue_lt {n k : ℕ} (f : Fin n → Fin (2 ^ k)) (i : ℕ) :
    finValue f i < 2 ^ k :=
  atIndex_lt _ (fun j => (f j).isLt) i

def LevelRecords.code {D : Dims} {L : LevelDims} (R : LevelRecords D L) : Mem → ℕ → ℕ
  | .layout, _ => if R.layout then 1 else 0
  | .outAddr, i => finValue R.outAddr i
  | .outDisp, i => finValue R.outDisp i
  | .outFar, i => finValue R.outFar i
  | .inAddr, i => finValue R.inAddr i
  | .inDisp, i => finValue R.inDisp i
  | .inFar, i => finValue R.inFar i
  | .width, i => finValue R.width i
  | .colour, i => finValue R.colour i
  | .offset, i => finValue R.offset i
  | .energy, i => finValue R.energy i
  | .terms, i => atIndex (fun j => termValue (R.terms j) (i % (L.termArity + 1))) (i / (L.termArity + 1))

theorem LevelRecords.code_lt {D : Dims} {L : LevelDims} (R : LevelRecords D L)
    (hw : 0 < D.wW) (k : Mem) (i : ℕ) : R.code k i < 2 ^ D.levWidth L k := by
  cases k <;> simp only [LevelRecords.code, Dims.levWidth]
  case layout => split <;> decide
  all_goals first | exact finValue_lt _ i | exact atIndex_lt _ (fun j => termValue_lt hw (R.terms j) _) _

abbrev Skeleton (D : Dims) := Fin (D.I * D.N) → Fin D.r → Fin 3

abbrev FinalArcs (D : Dims) := (D.lv D.top).bases * (D.lv D.top).lanes * (D.lv D.top).slots

def finalLevel (D : Dims) : Fin (D.top + 1) := Fin.last D.top

variable {F : Type*}

/-- The record producers for the tuple counted in P11. Each branch's payload
is indexed by its final arc order, with its actual bit width at each arc. -/
structure TupleRecords (D : Dims) (C : P1Count.CountData F) (d : ℕ) where
  skeleton : C.Sk ↪ Skeleton D
  directory : C.Sk → Directory D
  level : (σ : C.Sk) → C.Ch σ → (ℓ : Fin (D.top + 1)) → LevelRecords D (D.lv ℓ.val)
  branch_injective : ∀ σ, Function.Injective (fun ι ℓ => (level σ ι ℓ).terms)
  payload : ∀ σ ι, C.Pay σ ι ≃
    ((i : Fin (FinalArcs D)) → Fin ((level σ ι (finalLevel D)).width i).val → Bool)
  owner_fits : D.I < 2 ^ D.bigW
  terms_fits_flag : 0 < D.wW
  chain_fits_len : ∀ σ ι, C.P σ ι + 1 ≤ D.chainLen
  chain_fits_entry : d ≤ 2 ^ D.chainW
  omega_fits : ∀ σ ι (y : Fin (D.lv D.top).bases),
    widthPrefix (finValue (level σ ι (finalLevel D)).width)
      (y.val * ((D.lv D.top).lanes * (D.lv D.top).slots)) < 2 ^ D.bigW

def levelAt {D : Dims} (R : (ℓ : Fin (D.top + 1)) → LevelRecords D (D.lv ℓ.val))
    (ℓ : ℕ) (k : Mem) (i : ℕ) : ℕ :=
  if h : ℓ < D.top + 1 then (R ⟨ℓ, h⟩).code k i else 0

theorem levelAt_lt {D : Dims} (R : (ℓ : Fin (D.top + 1)) → LevelRecords D (D.lv ℓ.val))
    (h : 0 < D.wW) (ℓ : ℕ) (k : Mem) (i : ℕ) : levelAt R ℓ k i < 2 ^ D.levWidth (D.lv ℓ) k := by
  unfold levelAt
  split
  · exact (R _).code_lt h k i
  · exact Nat.two_pow_pos _

end SolWitfill

open SolWitfill

variable {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}

/-- Fill the fixed witness fields with the skeleton, selected branch,
chain, and their true records. The payload supplies the separate S3 bits. -/
def ofTuple (R : TupleRecords D C d) (t : C.Tup d) : Fields :=
  let dir := R.directory t.1
  let level := levelAt (R.level t.1 t.2.1)
  let widths := finValue (R.level t.1 t.2.1 (finalLevel D)).width
  { trit := fun i k => atIndex (fun j => finValue (R.skeleton t.1 j) k) i
    start := fun i k => atIndex (fun j => zigzag (dir.start j)) (i * D.r + k)
    prevOwn := fun i k δ => atIndex (fun j => ownerCode (dir.prevOwn j)) ((i * D.r + k) * 3 + δ)
    nextOwn := fun i k δ => atIndex (fun j => ownerCode (dir.nextOwn j)) ((i * D.r + k) * 3 + δ)
    guess := atIndex (fun j => ownerCode (dir.guess j))
    layout := fun ℓ => level ℓ .layout 0
    outAddr := fun ℓ y k => level ℓ .outAddr (y * (D.lv ℓ).slots + k)
    outDisp := fun ℓ y k => level ℓ .outDisp (y * (D.lv ℓ).slots + k)
    outFar := fun ℓ y k => level ℓ .outFar (y * (D.lv ℓ).slots + k)
    inAddr := fun ℓ y k => level ℓ .inAddr (y * (D.lv ℓ).slots + k)
    inDisp := fun ℓ y k => level ℓ .inDisp (y * (D.lv ℓ).slots + k)
    inFar := fun ℓ y k => level ℓ .inFar (y * (D.lv ℓ).slots + k)
    width := fun ℓ y l k => level ℓ .width ((y * (D.lv ℓ).lanes + l) * (D.lv ℓ).slots + k)
    colour := fun ℓ y => level ℓ .colour y
    offset := fun ℓ y => level ℓ .offset y
    energy := fun ℓ y c => level ℓ .energy (y * 2 + c)
    terms := fun ℓ y k c =>
      level ℓ .terms ((y * (D.lv ℓ).termKeys + k) * ((D.lv ℓ).termArity + 1) + c)
    Omega := atIndex (fun y : Fin (D.lv D.top).bases =>
      widthPrefix widths (y.val * ((D.lv D.top).lanes * (D.lv D.top).slots)))
    chain := finValue t.2.2.2 }

namespace SolWitfill

theorem ofTuple_levVal (R : TupleRecords D C d) (t : C.Tup d) (ℓ : ℕ)
    (k : Mem) (i : ℕ) (hi : i < (D.lv ℓ).count k) :
    (ofTuple R t).levVal (D.lv ℓ) ℓ k i = levelAt (R.level t.1 t.2.1) ℓ k i := by
  cases k <;> simp only [Fields.levVal, ofTuple, div_mul_add_mod]
  case layout =>
    have hi0 : i = 0 := by
      simp only [LevelDims.count] at hi
      split at hi <;> omega
    rw [hi0]

theorem levels_agree (R : TupleRecords D C d) {t u : C.Tup d} (h : (ofTuple R t).Agree D (ofTuple R u))
    (ℓ : Fin (D.top + 1)) (k : Mem) (i : Fin ((D.lv ℓ.val).count k)) :
    (R.level t.1 t.2.1 ℓ).code k i.val = (R.level u.1 u.2.1 ℓ).code k i.val := by
  have hℓ : ℓ.val ≤ D.top := Nat.le_of_lt_succ ℓ.isLt
  have ha := h (secLev ℓ.val k) (D.secLev_lt_nSec k hℓ) i.val (by rw [D.count_secLev k hℓ]; exact i.isLt)
  simpa only [Fields.val, D.kind_secLev k hℓ, ofTuple_levVal R _ _ _ _ i.isLt, levelAt, dite_eq_left ℓ.isLt] using ha

end SolWitfill

theorem ofTuple_inRange (R : TupleRecords D C d) (t : C.Tup d) :
    (ofTuple R t).InRange D := by
  intro s _ i hi
  rcases hk : D.kind s with _ | _ | _ | _ | _ | ⟨ℓ, k⟩ | _ | _ | _
  all_goals simp only [Fields.val, Dims.width, hk]
  · simp only [ofTuple, finValue]
    apply atIndex_lt
    intro j
    exact atIndex_lt _ (fun k => (R.skeleton t.1 j k).isLt.trans (by decide)) _
  · exact atIndex_lt _ (R.directory t.1).start_fits _
  · exact atIndex_lt _ (fun j => ownerCode_lt R.owner_fits ((R.directory t.1).prevOwn j)) _
  · exact atIndex_lt _ (fun j => ownerCode_lt R.owner_fits ((R.directory t.1).nextOwn j)) _
  · exact atIndex_lt _ (fun j => ownerCode_lt R.owner_fits ((R.directory t.1).guess j)) _
  · rw [ofTuple_levVal R t ℓ k i (by simpa only [Dims.count, hk] using hi)]
    exact levelAt_lt _ R.terms_fits_flag _ _ _
  · exact atIndex_lt _ (R.omega_fits t.1 t.2.1) _
  · exact atIndex_lt _ (fun j => (t.2.2.2 j).isLt.trans_le R.chain_fits_entry) _
  · decide

namespace SolWitfill

def tuplePayload (R : TupleRecords D C d) (t : C.Tup d) : List Bool :=
  flatten (R.payload t.1 t.2.1 t.2.2.1)

theorem tuplePayload_length (R : TupleRecords D C d) (t : C.Tup d) :
    (tuplePayload R t).length =
      widthPrefix (finValue (R.level t.1 t.2.1 (finalLevel D)).width) (FinalArcs D) :=
  flatten_length _

theorem tuplePayload_length_agree (R : TupleRecords D C d) (t u : C.Tup d)
    (h : (ofTuple R t).Agree D (ofTuple R u)) :
    (tuplePayload R t).length = (tuplePayload R u).length := by
  rw [tuplePayload_length, tuplePayload_length, widthPrefix, widthPrefix]
  apply Finset.sum_congr rfl
  intro i hi
  exact levels_agree R h (finalLevel D) .width ⟨i, Finset.mem_range.mp hi⟩

theorem trits_agree (R : TupleRecords D C d) {t u : C.Tup d}
    (h : (ofTuple R t).Agree D (ofTuple R u)) : t.1 = u.1 := by
  apply R.skeleton.injective
  funext i k
  apply Fin.ext
  simpa only [ofTuple, atIndex_fin, finValue_fin] using
    agree_trit (ofTuple_inRange R t) (ofTuple_inRange R u) h i.isLt k.isLt

theorem terms_agree (R : TupleRecords D C d) {t u : C.Tup d}
    (hs : t.1 = u.1) (h : (ofTuple R t).Agree D (ofTuple R u)) : HEq t.2.1 u.2.1 := by
  rcases t with ⟨σ, ι, z, j⟩
  rcases u with ⟨σ', ι', z', j'⟩
  change σ = σ' at hs
  subst σ'
  apply heq_of_eq
  apply R.branch_injective σ
  funext ℓ y
  apply termValue_injective
  intro c
  have hi := idx_lt y.isLt c.isLt
  have h' := levels_agree R h ℓ .terms ⟨y.val * ((D.lv ℓ.val).termArity + 1) + c.val, hi⟩
  simpa only [LevelRecords.code, idx_div c.isLt, idx_mod c.isLt, atIndex_fin] using h'

theorem tuple_eq (R : TupleRecords D C d) (t u : C.Tup d)
    (h : (ofTuple R t).Agree D (ofTuple R u)) (hz : tuplePayload R t = tuplePayload R u) : t = u := by
  have hs := trits_agree R h
  have hι := terms_agree R hs h
  rcases t with ⟨σ, ι, z, j⟩
  rcases u with ⟨σ', ι', z', j'⟩
  change σ = σ' at hs
  subst σ'
  change HEq ι ι' at hι
  have hι' := eq_of_heq hι
  subst ι'
  have hzz : z = z' :=
    (R.payload σ ι).injective (flatten_injective _ hz)
  subst z'
  have hj : j = j' := by
    funext p
    apply Fin.ext
    have hp := p.isLt.trans_le (R.chain_fits_len σ ι)
    have e := agree_chain (ofTuple_inRange R ⟨σ, ι, z, j⟩)
      (ofTuple_inRange R ⟨σ, ι, z, j'⟩) h hp
    simpa only [ofTuple, finValue_fin] using e
  subst j'
  rfl

end SolWitfill

/-- The P6 witness of a typed tuple, in the representation used by P11. -/
def encTuple (R : TupleRecords D C d) (m : ℕ) (t : C.Tup d) : Fin m → Bool :=
  encFn D m (ofTuple R t) (tuplePayload R t)

/-- The witness encoding supplies the injectivity field of `P1Int.P11.CountInput`. -/
theorem encTuple_injective (R : TupleRecords D C d) (m : ℕ)
    (hm : ∀ t, D.fixedLen + (tuplePayload R t).length ≤ m) :
    Function.Injective (encTuple R m) :=
  encFn_comp_injective D m (ofTuple R) (tuplePayload R) (ofTuple_inRange R) hm
    (tuplePayload_length_agree R) (tuple_eq R)

end P1Wit

#print axioms P1Wit.ofTuple
#print axioms P1Wit.ofTuple_inRange
#print axioms P1Wit.encTuple_injective
