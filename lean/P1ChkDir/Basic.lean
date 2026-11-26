import P1Net.Skeleton

/-!
# P1ChkDir.Basic: the witness checks C1, C2, C3 of Lemma P (Prop level)

Problem P1, Case 2, part of task P8 (lane P1-lean-W2-chkdir, brief `ORG/briefs/P1-lean-W2-chkdir.md`).
Paper `research/papers/ntime-dtime-polylog.tex`, `subsec:witness`: sections S0 (skeleton trits) and S1 (directory),
checks C1-C3 (l.1033-1039) and `lem:unique`.

The witness is a bit list `u`; `bit u j` is its bit `j` (`false` beyond its end). Fields have fixed offsets and
widths. Until lane P6 posts `P1Wit.Layout`, the layout is the abstract structure `DirLayout` (offsets of the S0 trit
codes and of the S1 fields, and the codes `cB` of start blocks and `cO` of owners); `P1ChkDir.Codes` gives
concrete codes. Each code checks range and unused parts (`dec` returns `none`).

Conventions of lane net (`P1Net.Skeleton`): tapes `K`; `I` big intervals of `N` small intervals; a skeleton is
`σ : Fin (I * N) → K → Fin 3` (the trit `t` is stored as `t + 1`); the start block of tape `k` at small interval
`i` is `P1Net.betaOf σ k i`; big interval `ι` starts at small interval `ι * N`, its big block is `⌊β / N⌋ = q`, and
it owns the big blocks `q - 1`, `q`, `q + 1` (paper `lem:own`).

Checks (one Prop per index):
* `C1 L u i k`: the trit code of `σ(i, k)` is not `11`.
* `C2 L u ι k`: `β(0, k) = 0` if `ι = 0`; `β(ι, k) = β(ι - 1, k) + Σ_{g < N} σ((ι - 1) N + g, k)` if `ι ≥ 1`.
  (So there are exactly `I * |K|` instances, and `β(I N)` is never stored: the paper's C11-style repair of C2.)
* `C3 L u ι k δ nx`: with `Q = ⌊β(ι, k) / N⌋ - 1 + δ`, the stored next owner (`nx = true`) or previous owner
  (`nx = false`) of `Q` is the least `ι' > ι` (the greatest `ι' < ι`) whose STORED start block owns `Q`, or `none`.
Results: `Ck_true` (true fields pass every instance), `Ck_unique` (passing every instance forces the true fields).
-/

namespace P1ChkDir

open P1Net

/-! ## Bits and fields -/

/-- Bit `j` of the witness, `false` beyond its end. -/
def bit (u : List Bool) (j : ℕ) : Bool := u.getD j false

/-- The `w` bits of `u` at the offsets `off, off + 1, ..., off + w - 1`. -/
def field (u : List Bool) (off w : ℕ) : List Bool := (List.range w).map fun j => bit u (off + j)

@[simp] theorem field_length (u : List Bool) (off w : ℕ) : (field u off w).length = w := by
  simp [field]

/-! ## Fixed-width codes -/

/-- A fixed-width code. `dec` returns `none` on an invalid word (value out of range, nonzero unused part, wrong
length); `ok` is the range of the code. -/
structure Code (α : Type) where
  w : ℕ
  enc : α → List Bool
  dec : List Bool → Option α
  ok : α → Prop
  enc_length : ∀ a, (enc a).length = w
  dec_enc : ∀ a, ok a → dec (enc a) = some a
  dec_ok : ∀ l a, dec l = some a → ok a
  enc_dec : ∀ l a, l.length = w → dec l = some a → enc a = l

namespace Code

variable {α : Type} (c : Code α)

/-- The value stored at offset `off` of `u`, if the field is valid. -/
def read (u : List Bool) (off : ℕ) : Option α := c.dec (field u off c.w)

/-- A field reads as `a` iff `a` is in range and the bits of the field are the code of `a`. -/
theorem read_eq_some {u : List Bool} {off : ℕ} {a : α} :
    c.read u off = some a ↔ c.ok a ∧ field u off c.w = c.enc a := by
  constructor
  · intro h
    exact ⟨c.dec_ok _ _ h, (c.enc_dec _ _ (field_length u off c.w) h).symm⟩
  · rintro ⟨hok, hf⟩
    simp only [read, hf, c.dec_enc a hok]

end Code

/-! ## The trit code of S0 (paper: `00 ↦ 0`, `01 ↦ 1`, `10 ↦ -1`, `11` invalid) -/

/-- Code of a trit stored as `t + 1 : Fin 3`: `-1 ↦ 10`, `0 ↦ 00`, `1 ↦ 01`. -/
def tritEnc (a : Fin 3) : List Bool :=
  if (a : ℕ) = 0 then [true, false] else if (a : ℕ) = 1 then [false, false] else [false, true]

/-- Decoding of a trit code; `11` and words of length other than `2` are invalid. -/
def tritDec : List Bool → Option (Fin 3)
  | [false, false] => some 1
  | [false, true] => some 2
  | [true, false] => some 0
  | _ => none

theorem tritDec_tritEnc (a : Fin 3) : tritDec (tritEnc a) = some a := by
  fin_cases a <;> rfl

theorem tritEnc_length (a : Fin 3) : (tritEnc a).length = 2 := by
  fin_cases a <;> rfl

theorem eq_pair {l : List Bool} (hl : l.length = 2) : ∃ b0 b1, l = [b0, b1] := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, l⟩⟩⟩
  · simp at hl
  · simp at hl
  · exact ⟨b0, b1, rfl⟩
  · simp only [List.length_cons] at hl
    omega

theorem tritEnc_tritDec {l : List Bool} {a : Fin 3} (hl : l.length = 2) (h : tritDec l = some a) :
    tritEnc a = l := by
  obtain ⟨b0, b1, rfl⟩ := eq_pair hl
  cases b0 <;> cases b1 <;> simp only [tritDec, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- The trit code, width `2`. -/
def tritCode : Code (Fin 3) where
  w := 2
  enc := tritEnc
  dec := tritDec
  ok := fun _ => True
  enc_length := tritEnc_length
  dec_enc := fun a _ => tritDec_tritEnc a
  dec_ok := fun _ _ _ => trivial
  enc_dec := fun _ _ hl h => tritEnc_tritDec hl h

/-! ## The layout of S0 and S1 (abstract until `P1Wit.Layout`) -/

/-- The trit code `cT` of S0 (every trit in range), offsets of the S0 trit codes and of the S1 fields, and the
codes of S1. Field `(ι, k)` of S1 is the
start block `β_k(ι N)`; fields `(ι, k, δ)` are the next and the previous owner of the big block `q_k(ι) - 1 + δ`. -/
structure DirLayout (K : Type) (I N : ℕ) where
  cT : Code (Fin 3)
  cT_ok : ∀ a, cT.ok a
  tritOff : Fin (I * N) → K → ℕ
  betaOff : Fin I → K → ℕ
  nextOff : Fin I → K → Fin 3 → ℕ
  prevOff : Fin I → K → Fin 3 → ℕ
  cB : Code ℤ
  cO : Code (Option (Fin I))

variable {K : Type} {I N : ℕ}

namespace DirLayout

variable (L : DirLayout K I N) (u : List Bool)

/-- The skeleton stored in S0 (an invalid code reads as the trit `0`; C1 rejects it). -/
def sigmaS : Fin (I * N) → K → Fin 3 := fun i k => (L.cT.read u (L.tritOff i k)).getD 1

/-- The stored start block `β_k(ι N)`. -/
def betaS (ι : Fin I) (k : K) : Option ℤ := L.cB.read u (L.betaOff ι k)

/-- The stored next owner of field `(ι, k, δ)`. -/
def nextS (ι : Fin I) (k : K) (δ : Fin 3) : Option (Option (Fin I)) := L.cO.read u (L.nextOff ι k δ)

/-- The stored previous owner of field `(ι, k, δ)`. -/
def prevS (ι : Fin I) (k : K) (δ : Fin 3) : Option (Option (Fin I)) := L.cO.read u (L.prevOff ι k δ)

end DirLayout

/-! ## Start blocks -/

/-- Increment of the start block over small interval `i` (`0` beyond the skeleton), as in `P1Net.betaOf`. -/
def sig {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) : ℤ :=
  if h : i < n then ((σ ⟨i, h⟩ k : ℕ) : ℤ) - 1 else 0

theorem betaOf_succ' {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) :
    betaOf σ k (i + 1) = betaOf σ k i + sig σ k i := rfl

theorem betaOf_add {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (a d : ℕ) :
    betaOf σ k (a + d) = betaOf σ k a + ∑ g ∈ Finset.range d, sig σ k (a + g) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, betaOf_succ', ih, Finset.sum_range_succ]
    ring

/-- The true start block of tape `k` at the start of big interval `ι`. -/
def betaT (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (ι : ℕ) (k : K) : ℤ := betaOf σ k (ι * N)

/-- Sum of the trits of tape `k` over big interval `ι`. -/
def trSum (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (ι : ℕ) : ℤ :=
  ∑ g ∈ Finset.range N, sig σ k (ι * N + g)

theorem betaT_zero (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) : betaT N σ 0 k = 0 := by
  simp [betaT, betaOf]

theorem betaT_succ (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (ι : ℕ) (k : K) :
    betaT N σ (ι + 1) k = betaT N σ ι k + trSum N σ k ι := by
  simp only [betaT, trSum]
  rw [Nat.succ_mul, betaOf_add]

/-! ## Big blocks and owners -/

/-- The big block of a start block. -/
def bigOf (N : ℕ) (b : ℤ) : ℤ := b / ((N : ℕ) : ℤ)

/-- A start block `b` owns big block `Q` if `Q` is `⌊b / N⌋ - 1`, `⌊b / N⌋` or `⌊b / N⌋ + 1`. -/
def OwnsB (N : ℕ) (b Q : ℤ) : Prop := bigOf N b - 1 ≤ Q ∧ Q ≤ bigOf N b + 1

instance (N : ℕ) (b Q : ℤ) : Decidable (OwnsB N b Q) := inferInstanceAs (Decidable (_ ∧ _))

theorem ownsB_iff (N : ℕ) (b Q : ℤ) : OwnsB N b Q ↔ ∃ δ : Fin 3, Q = bigOf N b - 1 + (δ : ℤ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(Q - bigOf N b + 1).toNat, by omega⟩, ?_⟩
    simp only
    omega
  · rintro ⟨δ, rfl⟩
    have := δ.isLt
    constructor <;> omega

/-- Big interval `j` owns `Q` according to a table `β` of start blocks (`false` on an invalid entry). -/
def ownsTab (β : Fin I → Option ℤ) (N : ℕ) (j : Fin I) (Q : ℤ) : Bool :=
  match β j with
  | some b => decide (OwnsB N b Q)
  | none => false

/-- The least `j > ι` that owns `Q` according to `β`, or `none`. -/
def nextScan (β : Fin I → Option ℤ) (N : ℕ) (ι : Fin I) (Q : ℤ) : Option (Fin I) :=
  if hS : (Finset.univ.filter fun j : Fin I => ι < j ∧ ownsTab β N j Q = true).Nonempty then
    some ((Finset.univ.filter fun j : Fin I => ι < j ∧ ownsTab β N j Q = true).min' hS)
  else none

/-- The greatest `j < ι` that owns `Q` according to `β`, or `none`. -/
def prevScan (β : Fin I → Option ℤ) (N : ℕ) (ι : Fin I) (Q : ℤ) : Option (Fin I) :=
  if hS : (Finset.univ.filter fun j : Fin I => j < ι ∧ ownsTab β N j Q = true).Nonempty then
    some ((Finset.univ.filter fun j : Fin I => j < ι ∧ ownsTab β N j Q = true).max' hS)
  else none

/-- The table of the true start blocks of tape `k`. -/
def betaTab (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) : Fin I → Option ℤ :=
  fun j => some (betaT N σ j k)

/-- The true big block of the directory field `(ι, k, δ)`: `q_k(ι) - 1 + δ`. -/
def portQT (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (ι : ℕ) (k : K) (δ : Fin 3) : ℤ :=
  bigOf N (betaT N σ ι k) - 1 + (δ : ℤ)

/-- The true next owner of the directory field `(ι, k, δ)`. -/
def nextT (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (ι : Fin I) (k : K) (δ : Fin 3) : Option (Fin I) :=
  nextScan (betaTab N σ k) N ι (portQT N σ ι k δ)

/-- The true previous owner of the directory field `(ι, k, δ)`. -/
def prevT (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (ι : Fin I) (k : K) (δ : Fin 3) : Option (Fin I) :=
  prevScan (betaTab N σ k) N ι (portQT N σ ι k δ)

theorem ownsTab_betaTab (N : ℕ) {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (j : Fin I) (Q : ℤ) :
    ownsTab (betaTab N σ k) N j Q = true ↔ OwnsB N (betaT N σ j k) Q := by
  simp [ownsTab, betaTab]

/-! ## The checks C1, C2, C3 -/

variable (L : DirLayout K I N) (u : List Bool)

/-- **C1** at `(i, k)`: the trit code of `σ(i, k)` is valid (not `11`). -/
def C1 (i : Fin (I * N)) (k : K) : Prop := L.cT.read u (L.tritOff i k) ≠ none

/-- The big interval before `ι` (`0` for `ι = 0`). -/
def predFin (ι : Fin I) : Fin I := ⟨ι - 1, lt_of_le_of_lt (Nat.sub_le _ _) ι.isLt⟩

/-- **C2** at `(ι, k)`: `β(0, k) = 0` for `ι = 0`, and `β(ι, k) = β(ι - 1, k) + Σ_{g < N} σ((ι - 1) N + g, k)`
for `ι ≥ 1` (all values decoded; an invalid field fails). -/
def C2 (ι : Fin I) (k : K) : Prop :=
  if (ι : ℕ) = 0 then L.betaS u ι k = some 0
  else ∃ b, L.betaS u (predFin ι) k = some b ∧
    L.betaS u ι k = some (b + trSum N (L.sigmaS u) k ((ι : ℕ) - 1))

/-- **C3** at `(ι, k, δ, nx)`: with `Q = ⌊β(ι, k) / N⌋ - 1 + δ` (stored `β`), the stored next owner (`nx`) or
previous owner (`¬ nx`) of `Q` is the scan of the STORED start blocks of tape `k`. -/
def C3 (ι : Fin I) (k : K) (δ : Fin 3) (nx : Bool) : Prop :=
  ∃ b, L.betaS u ι k = some b ∧
    if nx then L.nextS u ι k δ = some (nextScan (fun j => L.betaS u j k) N ι (bigOf N b - 1 + (δ : ℤ)))
    else L.prevS u ι k δ = some (prevScan (fun j => L.betaS u j k) N ι (bigOf N b - 1 + (δ : ℤ)))

/-! ## C1: soundness and uniqueness -/

/-- **C1, soundness.** If S0 holds the code of a skeleton `σ`, every C1 instance passes and `σ(u) = σ`. -/
theorem C1_true (σ : Fin (I * N) → K → Fin 3)
    (hf : ∀ i k, field u (L.tritOff i k) L.cT.w = L.cT.enc (σ i k)) :
    (∀ i k, C1 L u i k) ∧ L.sigmaS u = σ := by
  have hr : ∀ i k, L.cT.read u (L.tritOff i k) = some (σ i k) :=
    fun i k => (L.cT.read_eq_some).2 ⟨L.cT_ok _, hf i k⟩
  refine ⟨fun i k => ?_, ?_⟩
  · simp only [C1, hr, ne_eq, reduceCtorEq, not_false_eq_true]
  · funext i k
    simp only [DirLayout.sigmaS, hr, Option.getD_some]

/-- **C1, uniqueness.** If every C1 instance passes, S0 holds the code of the skeleton `σ(u)`. -/
theorem C1_unique (hC1 : ∀ i k, C1 L u i k) :
    ∀ i k, field u (L.tritOff i k) L.cT.w = L.cT.enc (L.sigmaS u i k) := by
  intro i k
  have h := hC1 i k
  unfold C1 at h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h
  simp only [DirLayout.sigmaS, ha, Option.getD_some]
  exact ((L.cT.read_eq_some).1 ha).2

/-! ## C2: soundness and uniqueness -/

/-- **C2, soundness.** If S0 holds `σ` and every start-block field holds the true `β_k(ι N)` of `σ`, every C2
instance passes. -/
theorem C2_true (σ : Fin (I * N) → K → Fin 3) (hσ : L.sigmaS u = σ)
    (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k)) : ∀ ι k, C2 L u ι k := by
  intro ι k
  unfold C2
  split_ifs with h0
  · rw [hβ, h0, betaT_zero]
  · refine ⟨betaT N σ ((ι : ℕ) - 1) k, hβ _ k, ?_⟩
    rw [hβ, hσ]
    obtain ⟨j, hj⟩ : ∃ j, (ι : ℕ) = j + 1 := ⟨(ι : ℕ) - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel, betaT_succ]

/-- **C2, uniqueness.** If every C2 instance passes, every start-block field holds the true `β_k(ι N)` of the
stored skeleton `σ(u)`. -/
theorem C2_unique (hC2 : ∀ ι k, C2 L u ι k) :
    ∀ ι k, L.betaS u ι k = some (betaT N (L.sigmaS u) ι k) := by
  intro ι k
  suffices H : ∀ j (hj : j < I), L.betaS u ⟨j, hj⟩ k = some (betaT N (L.sigmaS u) j k) from H ι ι.isLt
  intro j
  induction j with
  | zero =>
    intro hj
    have h := hC2 ⟨0, hj⟩ k
    simp only [C2, ↓reduceIte] at h
    rw [h, betaT_zero]
  | succ j ih =>
    intro hj
    have h := hC2 ⟨j + 1, hj⟩ k
    simp only [C2, Nat.succ_ne_zero, ↓reduceIte] at h
    obtain ⟨b, hb, hstep⟩ := h
    have hp : predFin (⟨j + 1, hj⟩ : Fin I) = ⟨j, by omega⟩ := Fin.ext (by simp [predFin])
    rw [hp, ih (by omega)] at hb
    simp only [Option.some.injEq] at hb
    rw [hstep, ← hb, Nat.add_sub_cancel, betaT_succ]

/-- C2 uniqueness at the bit level: every start-block field is the code of the true value. -/
theorem C2_unique_bits (hC2 : ∀ ι k, C2 L u ι k) :
    ∀ ι k, field u (L.betaOff ι k) L.cB.w = L.cB.enc (betaT N (L.sigmaS u) ι k) :=
  fun ι k => ((L.cB.read_eq_some).1 (C2_unique L u hC2 ι k)).2

/-! ## C3: soundness and uniqueness -/

/-- Once every start-block field holds the true value, the stored table of tape `k` is the true table. -/
theorem betaS_tab {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k)) (k : K) :
    (fun j => L.betaS u j k) = betaTab N σ k :=
  funext fun j => hβ j k

/-- **C3, soundness.** If the start-block fields and the owner fields hold the true values for `σ`, every C3
instance passes. -/
theorem C3_true {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k))
    (hown : ∀ ι k δ, L.nextS u ι k δ = some (nextT N σ ι k δ) ∧ L.prevS u ι k δ = some (prevT N σ ι k δ)) :
    ∀ ι k δ nx, C3 L u ι k δ nx := by
  intro ι k δ nx
  refine ⟨betaT N σ ι k, hβ ι k, ?_⟩
  rw [betaS_tab L u σ hβ k]
  cases nx
  · simp only [Bool.false_eq_true, ite_false]
    exact (hown ι k δ).2
  · simp only [ite_true]
    exact (hown ι k δ).1

/-- **C3, uniqueness.** If the start-block fields hold the true values for `σ` and every C3 instance passes, the
owner fields hold the true next and previous owners. -/
theorem C3_unique {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k))
    (hC3 : ∀ ι k δ nx, C3 L u ι k δ nx) :
    ∀ ι k δ, L.nextS u ι k δ = some (nextT N σ ι k δ) ∧ L.prevS u ι k δ = some (prevT N σ ι k δ) := by
  intro ι k δ
  obtain ⟨b, hb, hn⟩ := hC3 ι k δ true
  obtain ⟨b', hb', hp⟩ := hC3 ι k δ false
  rw [hβ] at hb hb'
  simp only [Option.some.injEq] at hb hb'
  subst hb hb'
  rw [betaS_tab L u σ hβ k] at hn hp
  simp only [ite_true] at hn
  simp only [Bool.false_eq_true, ite_false] at hp
  exact ⟨hn, hp⟩

/-- C3 uniqueness at the bit level. -/
theorem C3_unique_bits {n : ℕ} (σ : Fin n → K → Fin 3) (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k))
    (hC3 : ∀ ι k δ nx, C3 L u ι k δ nx) :
    ∀ ι k δ, field u (L.nextOff ι k δ) L.cO.w = L.cO.enc (nextT N σ ι k δ) ∧
      field u (L.prevOff ι k δ) L.cO.w = L.cO.enc (prevT N σ ι k δ) := by
  intro ι k δ
  obtain ⟨h1, h2⟩ := C3_unique L u σ hβ hC3 ι k δ
  exact ⟨((L.cO.read_eq_some).1 h1).2, ((L.cO.read_eq_some).1 h2).2⟩

/-! ## The directory chain C1 → C2 → C3 -/

/-- **C1-C3 together.** If every instance of C1, C2 and C3 passes, then S0 is the code of `σ(u)`, every start-block
field is the code of the true `β` of `σ(u)`, and every owner field is the code of the true owner. -/
theorem dir_unique (hC1 : ∀ i k, C1 L u i k) (hC2 : ∀ ι k, C2 L u ι k) (hC3 : ∀ ι k δ nx, C3 L u ι k δ nx) :
    (∀ i k, field u (L.tritOff i k) L.cT.w = L.cT.enc (L.sigmaS u i k)) ∧
    (∀ ι k, L.betaS u ι k = some (betaT N (L.sigmaS u) ι k)) ∧
    (∀ ι k δ, L.nextS u ι k δ = some (nextT N (L.sigmaS u) ι k δ) ∧
      L.prevS u ι k δ = some (prevT N (L.sigmaS u) ι k δ)) :=
  ⟨C1_unique L u hC1, C2_unique L u hC2, C3_unique L u (L.sigmaS u) (C2_unique L u hC2) hC3⟩

/-- **C1-C3 together, soundness.** If S0 is the code of `σ` and the directory fields are the codes of the true
values of `σ` (in range of the codes), every instance of C1, C2 and C3 passes. -/
theorem dir_true (σ : Fin (I * N) → K → Fin 3)
    (hf : ∀ i k, field u (L.tritOff i k) L.cT.w = L.cT.enc (σ i k))
    (hβ : ∀ ι k, L.betaS u ι k = some (betaT N σ ι k))
    (hown : ∀ ι k δ, L.nextS u ι k δ = some (nextT N σ ι k δ) ∧ L.prevS u ι k δ = some (prevT N σ ι k δ)) :
    (∀ i k, C1 L u i k) ∧ (∀ ι k, C2 L u ι k) ∧ (∀ ι k δ nx, C3 L u ι k δ nx) := by
  obtain ⟨h1, hσ⟩ := C1_true L u σ hf
  exact ⟨h1, C2_true L u σ hσ hβ, C3_true L u σ hβ hown⟩

end P1ChkDir
