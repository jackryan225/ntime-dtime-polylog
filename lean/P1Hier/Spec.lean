import C1Challenge.Statement

/-!
# P1Hier.Spec: the universal transcript checker at the functional level (W1, Mathlib only)

A machine `M` (Challenge model) is encoded as `code M : MCode`: tapes, states and symbols become
natural numbers (blank ↦ 0), and the transition function becomes a TABLE with one `Entry` per pair
(state, symbols under the heads). A transcript is a list of table entries, one per configuration of
the run. The checker `Check` tests: at most `T + 1` rows; every row is a table entry; the states chain
from the initial state to a halting row with answer `true`; for every tape separately, the symbols
read agree with a simulation of that tape alone (a column of the transcript). Book-Greibach-Wegbreit:
each tape is checked in its own pass, so a program with a FIXED number of stacks can do it.

Main theorem `check_iff`: `Check (code M) y T τ ↔ τ = transcript M y T ∧ HaltsWithin M y true T`.
So for every run there is exactly one valid transcript.
-/

namespace P1Hier

open C1Challenge

/-! ## Encoded data -/

/-- A head move: `none` = stay, `some false` = left, `some true` = right. -/
abbrev Mv := Option Bool

/-- One cell of a row: symbol read, symbol written, move. -/
abbrev Cell := ℕ × ℕ × Mv

/-- A row: state, one cell per tape (in tape order), then `inl q'` (next state) or `inr b`
(the machine halts here with answer `b`). -/
abbrev Entry := ℕ × List Cell × (ℕ ⊕ Bool)

/-- An encoded machine. -/
structure MCode where
  nK : ℕ
  inp : ℕ
  sym0 : ℕ
  sym1 : ℕ
  init : ℕ
  table : List Entry

/-- A tape with explicit head cell; the blank is `0`. -/
structure Tp where
  L : List ℕ
  h : ℕ
  R : List ℕ

namespace Tp

/-- Write, then move (the order of the Challenge model's step). -/
def act (t : Tp) (w : ℕ) : Mv → Tp
  | none => ⟨t.L, w, t.R⟩
  | some false => ⟨t.L.tail, t.L.headD 0, w :: t.R⟩
  | some true => ⟨w :: t.L, t.R.headD 0, t.R.tail⟩

/-- The tape holding the word `l`, head on its first letter. -/
def ofList (l : List ℕ) : Tp := ⟨[], l.headD 0, l.tail⟩

end Tp

/-- One tape pass: the reads of a column agree with the simulated tape. -/
def colOK : Tp → List Cell → Bool
  | _, [] => true
  | t, x :: rest => (x.1 == t.h) && colOK (t.act x.2.1 x.2.2) rest

/-- The states chain from `q` to a final row that halts with answer `true`. -/
def chainOK : ℕ → List Entry → Bool
  | _, [] => false
  | q, e :: rest => decide (e.1 = q) && (match e.2.2 with
      | Sum.inl q' => chainOK q' rest
      | Sum.inr b => rest.isEmpty && b)

/-- Column `k` of a transcript. -/
def col (k : ℕ) (τ : List Entry) : List Cell := τ.map fun e => e.2.1.getD k (0, 0, none)

def MCode.sym (c : MCode) (b : Bool) : ℕ := if b then c.sym1 else c.sym0

/-- Start tape number `k` on input `y`. -/
def MCode.start (c : MCode) (y : List Bool) (k : ℕ) : Tp :=
  if k = c.inp then Tp.ofList (y.map c.sym) else Tp.ofList []

/-- The transcript check. -/
def Check (c : MCode) (y : List Bool) (T : ℕ) (τ : List Entry) : Prop :=
  τ.length ≤ T + 1 ∧ (∀ e ∈ τ, e ∈ c.table) ∧ chainOK c.init τ = true ∧
    ∀ k < c.nK, colOK (c.start y k) (col k τ) = true

/-! ## Encoding a machine -/

section Encode

variable (M : Machine)

/-- Tape numbering. -/
noncomputable def eK : M.K ≃ Fin (Fintype.card M.K) := Fintype.equivFin M.K

/-- State numbering. -/
noncomputable def encQ (q : M.Q) : ℕ := (Fintype.equivFin M.Q q : ℕ)

open Classical in
/-- Symbol numbering; the blank gets `0`. -/
noncomputable def encG (g : M.Γ) : ℕ := if g = default then 0 else (Fintype.equivFin M.Γ g : ℕ) + 1

/-- Symbol decoding. -/
noncomputable def decG : ℕ → M.Γ := Function.invFun (encG M)

def encMv : HeadMove → Mv
  | .left => some false
  | .stay => none
  | .right => some true

/-- The cell of tape `k` in the row of (state, heads `f`), for the transition `o`. A halting row
writes back the symbol read and stays. -/
noncomputable def cellOf (f : M.K → M.Γ) (o : Option (M.Q × (M.K → M.Γ) × (M.K → HeadMove)))
    (k : M.K) : Cell :=
  match o with
  | none => (encG M (f k), encG M (f k), none)
  | some out => (encG M (f k), encG M (out.2.1 k), encMv (out.2.2 k))

noncomputable def cellsOf (f : M.K → M.Γ) (o : Option (M.Q × (M.K → M.Γ) × (M.K → HeadMove))) :
    List Cell :=
  List.ofFn fun i : Fin (Fintype.card M.K) => cellOf M f o ((eK M).symm i)

/-- The table entry of state `q` with heads `f`. -/
noncomputable def entry (q : M.Q) (f : M.K → M.Γ) : Entry :=
  (encQ M q, cellsOf M f (M.code q f), match M.code q f with
    | none => Sum.inr (M.accept q)
    | some out => Sum.inl (encQ M out.1))

/-- The code of a machine. -/
noncomputable def code : MCode where
  nK := Fintype.card M.K
  inp := eK M M.inputTape
  sym0 := encG M (M.inputSymbol false)
  sym1 := encG M (M.inputSymbol true)
  init := encQ M M.initialState
  table := (Finset.univ : Finset (M.Q × (M.K → M.Γ))).toList.map fun p => entry M p.1 p.2

/-- The row of a configuration. -/
noncomputable def rowOf (c : Cfg M.K M.Γ M.Q) : Entry := entry M c.q (fun k => (c.tapes k).head)

/-- Rows of the run from `c`, until it halts, at most `n + 1` rows. -/
noncomputable def rowsFrom : Cfg M.K M.Γ M.Q → ℕ → List Entry
  | c, 0 => [rowOf M c]
  | c, n + 1 => rowOf M c :: (match M.step c with
      | none => []
      | some c' => rowsFrom c' n)

/-- The transcript of the run of `M` on `y`, cut at `T + 1` rows. -/
noncomputable def transcript (y : List Bool) (T : ℕ) : List Entry := rowsFrom M (M.init y) T

/-- The abstract tape of an encoded tape. -/
noncomputable def absT (t : Tp) : Turing.Tape M.Γ :=
  ⟨decG M t.h, Turing.ListBlank.mk (t.L.map (decG M)), Turing.ListBlank.mk (t.R.map (decG M))⟩

/-- All symbols of the tape are codes of symbols. -/
def Good (t : Tp) : Prop :=
  t.h ∈ Set.range (encG M) ∧ (∀ a ∈ t.L, a ∈ Set.range (encG M)) ∧ ∀ a ∈ t.R, a ∈ Set.range (encG M)

/-- Halting with answer `true` within `n` steps from `c`. -/
def haltsFrom (c : Cfg M.K M.Γ M.Q) (n : ℕ) : Prop :=
  ∃ t ≤ n, ∃ c' : Cfg M.K M.Γ M.Q, (fun oc => Option.bind oc M.step)^[t] (some c) = some c' ∧
    M.step c' = none ∧ M.accept c'.q = true

/-! ### Basic lemmas -/

theorem encQ_injective : Function.Injective (encQ M) := by
  intro a b h
  exact (Fintype.equivFin M.Q).injective (Fin.ext h)

theorem encG_default : encG M default = 0 := by
  simp [encG]

theorem encG_injective : Function.Injective (encG M) := by
  intro a b h
  classical
  unfold encG at h
  by_cases ha : a = default <;> by_cases hb : b = default
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simp only [ha, hb, ite_false, add_left_inj] at h
    exact (Fintype.equivFin M.Γ).injective (Fin.ext h)

theorem decG_encG (g : M.Γ) : decG M (encG M g) = g :=
  Function.leftInverse_invFun (encG_injective M) g

theorem decG_zero : decG M 0 = default := by
  rw [← encG_default M, decG_encG]

theorem zero_mem_range : (0 : ℕ) ∈ Set.range (encG M) := ⟨default, encG_default M⟩

theorem absT_act (t : Tp) (w : M.Γ) (m : HeadMove) :
    absT M (t.act (encG M w) (encMv m)) = m.apply ((absT M t).write w) := by
  rcases t with ⟨L, h, R⟩
  cases m
  · -- left
    simp only [encMv, Tp.act, absT, HeadMove.apply, Turing.Tape.write, Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk, List.map_cons,
      decG_encG, List.map_tail]
    cases L <;> simp [decG_zero]
  · simp [encMv, Tp.act, absT, HeadMove.apply, Turing.Tape.write, decG_encG]
  · simp only [encMv, Tp.act, absT, HeadMove.apply, Turing.Tape.write, Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk, List.map_cons,
      decG_encG, List.map_tail]
    cases R <;> simp [decG_zero]

theorem good_act (t : Tp) (ht : Good M t) (w : M.Γ) (m : HeadMove) :
    Good M (t.act (encG M w) (encMv m)) := by
  rcases t with ⟨L, h, R⟩
  obtain ⟨hh, hL, hR⟩ := ht
  have hw : encG M w ∈ Set.range (encG M) := ⟨w, rfl⟩
  have hd : ∀ l : List ℕ, (∀ a ∈ l, a ∈ Set.range (encG M)) → l.headD 0 ∈ Set.range (encG M) := by
    intro l hl; cases l with
    | nil => exact zero_mem_range M
    | cons a l => exact hl a (by simp)
  have ht' : ∀ l : List ℕ, (∀ a ∈ l, a ∈ Set.range (encG M)) → ∀ a ∈ l.tail, a ∈ Set.range (encG M) := by
    intro l hl a ha; exact hl a (List.mem_of_mem_tail ha)
  cases m
  · refine ⟨hd L hL, ht' L hL, ?_⟩
    intro a ha; simp only [encMv, Tp.act, List.mem_cons] at ha; rcases ha with rfl | ha; exact hw; exact hR a ha
  · exact ⟨hw, hL, hR⟩
  · refine ⟨hd R hR, ?_, ht' R hR⟩
    intro a ha; simp only [encMv, Tp.act, List.mem_cons] at ha; rcases ha with rfl | ha; exact hw; exact hL a ha

/-- The head of a good tape is the code of the abstract head. -/
theorem head_eq (t : Tp) (ht : Good M t) : t.h = encG M (absT M t).head := by
  obtain ⟨g, hg⟩ := ht.1
  simp only [absT, ← hg, decG_encG]

theorem cellsOf_getD (f : M.K → M.Γ) (o) (k : M.K) (d : Cell) :
    (cellsOf M f o).getD (eK M k) d = cellOf M f o k := by
  simp [cellsOf, List.getD_eq_getElem?_getD]

theorem cellOf_fst (f : M.K → M.Γ) (o) (k : M.K) : (cellOf M f o k).1 = encG M (f k) := by
  cases o <;> rfl

theorem mem_table (e : Entry) : e ∈ (code M).table ↔ ∃ q f, e = entry M q f := by
  simp only [code, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨q, f, rfl⟩; exact ⟨q, f, rfl⟩
  · rintro ⟨q, f, rfl⟩; exact ⟨q, f, rfl⟩

theorem iterate_some_step (c c' : Cfg M.K M.Γ M.Q) (h : M.step c = some c') (t : ℕ) :
    (fun oc => Option.bind oc M.step)^[t + 1] (some c) =
      (fun oc => Option.bind oc M.step)^[t] (some c') := by
  rw [Function.iterate_succ_apply]
  simp [h]

theorem iterate_none (t : ℕ) :
    (fun oc => Option.bind oc M.step)^[t] (none : Option (Cfg M.K M.Γ M.Q)) = none := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply]; simpa using ih

theorem haltsFrom_of_none (c : Cfg M.K M.Γ M.Q) (h : M.step c = none) (n : ℕ) :
    haltsFrom M c n ↔ M.accept c.q = true := by
  constructor
  · rintro ⟨t, -, c', hc, -, hacc⟩
    cases t with
    | zero => simp at hc; subst hc; exact hacc
    | succ t =>
      rw [Function.iterate_succ_apply] at hc
      simp [h, iterate_none] at hc
  · intro hacc
    exact ⟨0, Nat.zero_le _, c, rfl, h, hacc⟩

theorem haltsFrom_of_some (c c' : Cfg M.K M.Γ M.Q) (h : M.step c = some c') (n : ℕ) :
    haltsFrom M c (n + 1) ↔ haltsFrom M c' n := by
  constructor
  · rintro ⟨t, ht, c'', hc, hs, hacc⟩
    cases t with
    | zero => simp at hc; subst hc; rw [h] at hs; cases hs
    | succ t =>
      rw [iterate_some_step M c c' h] at hc
      exact ⟨t, by omega, c'', hc, hs, hacc⟩
  · rintro ⟨t, ht, c'', hc, hs, hacc⟩
    exact ⟨t + 1, by omega, c'', by rw [iterate_some_step M c c' h]; exact hc, hs, hacc⟩

theorem haltsFrom_zero (c : Cfg M.K M.Γ M.Q) :
    haltsFrom M c 0 ↔ M.step c = none ∧ M.accept c.q = true := by
  constructor
  · rintro ⟨t, ht, c', hc, hs, hacc⟩
    have : t = 0 := by omega
    subst this
    simp at hc; subst hc; exact ⟨hs, hacc⟩
  · rintro ⟨hs, hacc⟩; exact ⟨0, le_rfl, c, rfl, hs, hacc⟩

/-! ### The main induction -/

/-- The first row of an accepted transcript is the row of the current configuration. -/
theorem head_row (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp)
    (hrep : ∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) (hgood : ∀ k : M.K, Good M (ts (eK M k)))
    (e : Entry) (rest : List Entry) (he : e ∈ (code M).table)
    (hch : chainOK (encQ M c.q) (e :: rest) = true)
    (hcol : ∀ k < Fintype.card M.K, colOK (ts k) (col k (e :: rest)) = true) :
    e = rowOf M c := by
  obtain ⟨q, f, rfl⟩ := (mem_table M e).1 he
  have hq : q = c.q := by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hch
    exact encQ_injective M hch.1
  subst hq
  have hf : f = fun k => (c.tapes k).head := by
    funext k
    have h1 := hcol (eK M k) (eK M k).isLt
    simp only [col, List.map_cons, colOK, Bool.and_eq_true, beq_iff_eq] at h1
    have h2 := h1.1
    simp only [entry, cellsOf_getD, cellOf_fst] at h2
    rw [head_eq M _ (hgood k), hrep k] at h2
    exact encG_injective M h2
  subst hf
  rfl

/-- The left side of the main induction. -/
def Lhs (n : ℕ) (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (τ : List Entry) : Prop :=
  τ.length ≤ n + 1 ∧ (∀ e ∈ τ, e ∈ (code M).table) ∧ chainOK (encQ M c.q) τ = true ∧
    ∀ k < Fintype.card M.K, colOK (ts k) (col k τ) = true

theorem rowOf_mem (c : Cfg M.K M.Γ M.Q) : rowOf M c ∈ (code M).table :=
  (mem_table M _).2 ⟨c.q, _, rfl⟩

/-- The reads of the row of `c` agree with the simulated tapes. -/
theorem reads_ok (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp)
    (hrep : ∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) (hgood : ∀ k : M.K, Good M (ts (eK M k)))
    (o) (k : ℕ) (hk : k < Fintype.card M.K) (d : Cell) :
    ((cellsOf M (fun k => (c.tapes k).head) o).getD k d).1 = (ts k).h := by
  set k' : M.K := (eK M).symm ⟨k, hk⟩
  have hk' : ((eK M k' : Fin _) : ℕ) = k := by simp [k']
  rw [← hk', cellsOf_getD, cellOf_fst, head_eq M _ (hgood k'), hrep k']

theorem rowsFrom_ne_nil (c : Cfg M.K M.Γ M.Q) (n : ℕ) : rowsFrom M c n ≠ [] := by
  cases n <;> simp [rowsFrom]

theorem rowsFrom_head (c : Cfg M.K M.Γ M.Q) (n : ℕ) (e : Entry) (rest : List Entry)
    (h : e :: rest = rowsFrom M c n) : e = rowOf M c := by
  cases n <;> simp only [rowsFrom, List.cons.injEq] at h <;> exact h.1

/-- Halting row. -/
theorem key_none (n : ℕ) (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (rest : List Entry)
    (hrep : ∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) (hgood : ∀ k : M.K, Good M (ts (eK M k)))
    (hcode : M.code c.q (fun k => (c.tapes k).head) = none) :
    Lhs M n c ts (rowOf M c :: rest) ↔ (rowOf M c :: rest = rowsFrom M c n ∧ haltsFrom M c n) := by
  have hstep : M.step c = none := by simp [Machine.step, hcode]
  have hrows : rowsFrom M c n = [rowOf M c] := by
    cases n <;> simp [rowsFrom, hstep]
  rw [hrows, haltsFrom_of_none M c hstep]
  have hrow : rowOf M c = (encQ M c.q, cellsOf M (fun k => (c.tapes k).head) none,
      Sum.inr (M.accept c.q)) := by
    simp only [rowOf, entry, hcode]
  constructor
  · rintro ⟨-, -, hch, -⟩
    rw [hrow] at hch
    simp only [chainOK, decide_true, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff] at hch
    exact ⟨by rw [hch.1], hch.2⟩
  · rintro ⟨hr, hacc⟩
    simp only [List.cons.injEq, true_and] at hr
    subst hr
    refine ⟨by simp, by simp [rowOf_mem], ?_, ?_⟩
    · rw [hrow]; simp [chainOK, hacc]
    · intro k hk
      simp only [col, List.map_cons, List.map_nil, colOK, Bool.and_true, beq_iff_eq]
      rw [hrow]
      exact reads_ok M c ts hrep hgood none k hk _

/-- A transition row with no step left in the budget. -/
theorem key_some_zero (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (rest : List Entry) (out)
    (hcode : M.code c.q (fun k => (c.tapes k).head) = some out) :
    Lhs M 0 c ts (rowOf M c :: rest) ↔ (rowOf M c :: rest = rowsFrom M c 0 ∧ haltsFrom M c 0) := by
  have hstep : M.step c ≠ none := by simp [Machine.step, hcode]
  rw [haltsFrom_zero]
  simp only [hstep, false_and, and_false, iff_false]
  rintro ⟨hlen, -, hch, -⟩
  simp only [List.length_cons] at hlen
  have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  simp [rowOf, entry, hcode, chainOK] at hch

/-- A transition row: one step of the induction. -/
theorem key_some_succ (n : ℕ) (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (rest : List Entry) (out)
    (hrep : ∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) (hgood : ∀ k : M.K, Good M (ts (eK M k)))
    (hcode : M.code c.q (fun k => (c.tapes k).head) = some out)
    (ih : ∀ (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (τ : List Entry),
      (∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) → (∀ k : M.K, Good M (ts (eK M k))) →
      (Lhs M n c ts τ ↔ (τ = rowsFrom M c n ∧ haltsFrom M c n))) :
    Lhs M (n + 1) c ts (rowOf M c :: rest) ↔
      (rowOf M c :: rest = rowsFrom M c (n + 1) ∧ haltsFrom M c (n + 1)) := by
  set c' : Cfg M.K M.Γ M.Q :=
    ⟨out.1, fun k => (out.2.2 k).apply ((c.tapes k).write (out.2.1 k))⟩ with hc'
  have hstep : M.step c = some c' := by simp [Machine.step, hcode, c']
  set cells := cellsOf M (fun k => (c.tapes k).head) (some out) with hcells
  set ts' : ℕ → Tp := fun k => (ts k).act (cells.getD k (0, 0, none)).2.1
    (cells.getD k (0, 0, none)).2.2 with hts'
  have hcell : ∀ k : M.K, cells.getD (eK M k) (0, 0, none) =
      (encG M ((c.tapes k).head), encG M (out.2.1 k), encMv (out.2.2 k)) := by
    intro k; rw [hcells, cellsOf_getD]; rfl
  have hrep' : ∀ k : M.K, absT M (ts' (eK M k)) = c'.tapes k := by
    intro k
    simp only [hts', hcell, c']
    rw [absT_act, hrep]
  have hgood' : ∀ k : M.K, Good M (ts' (eK M k)) := by
    intro k
    simp only [hts', hcell]
    exact good_act M _ (hgood k) _ _
  have hrow : rowOf M c = (encQ M c.q, cells, Sum.inl (encQ M out.1)) := by
    simp only [rowOf, entry, hcode, hcells]
  have hrows : rowsFrom M c (n + 1) = rowOf M c :: rowsFrom M c' n := by
    simp [rowsFrom, hstep]
  rw [hrows, haltsFrom_of_some M c c' hstep, List.cons.injEq]
  simp only [true_and]
  rw [← ih c' ts' rest hrep' hgood']
  unfold Lhs
  have hq : c'.q = out.1 := rfl
  rw [hq]
  constructor
  · rintro ⟨hlen, htab, hch, hcol⟩
    refine ⟨by simpa using hlen, fun e he => htab e (by simp [he]), ?_, ?_⟩
    · rw [hrow] at hch; simpa [chainOK] using hch
    · intro k hk
      have h1 := hcol k hk
      simp only [col, List.map_cons, colOK, Bool.and_eq_true] at h1
      rw [hrow] at h1
      exact h1.2
  · rintro ⟨hlen, htab, hch, hcol⟩
    refine ⟨by simpa using hlen, ?_, ?_, ?_⟩
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact rowOf_mem M c
      · exact htab e he
    · rw [hrow]; simpa [chainOK] using hch
    · intro k hk
      simp only [col, List.map_cons, colOK, Bool.and_eq_true, beq_iff_eq]
      rw [hrow]
      exact ⟨reads_ok M c ts hrep hgood (some out) k hk _, hcol k hk⟩

theorem main (n : ℕ) : ∀ (c : Cfg M.K M.Γ M.Q) (ts : ℕ → Tp) (τ : List Entry),
    (∀ k : M.K, absT M (ts (eK M k)) = c.tapes k) → (∀ k : M.K, Good M (ts (eK M k))) →
    (Lhs M n c ts τ ↔ (τ = rowsFrom M c n ∧ haltsFrom M c n)) := by
  induction n with
  | zero =>
    intro c ts τ hrep hgood
    rcases τ with _ | ⟨e, rest⟩
    · simp [Lhs, chainOK, (rowsFrom_ne_nil M c 0).symm]
    · have key : e = rowOf M c → (Lhs M 0 c ts (e :: rest) ↔
          (e :: rest = rowsFrom M c 0 ∧ haltsFrom M c 0)) := by
        rintro rfl
        rcases hcode : M.code c.q (fun k => (c.tapes k).head) with _ | out
        · exact key_none M 0 c ts rest hrep hgood hcode
        · exact key_some_zero M c ts rest out hcode
      constructor
      · intro h
        exact (key (head_row M c ts hrep hgood e rest (h.2.1 e (by simp)) h.2.2.1 h.2.2.2)).1 h
      · intro h
        exact (key (rowsFrom_head M c 0 e rest h.1)).2 h
  | succ n ih =>
    intro c ts τ hrep hgood
    rcases τ with _ | ⟨e, rest⟩
    · simp [Lhs, chainOK, (rowsFrom_ne_nil M c (n + 1)).symm]
    · have key : e = rowOf M c → (Lhs M (n + 1) c ts (e :: rest) ↔
          (e :: rest = rowsFrom M c (n + 1) ∧ haltsFrom M c (n + 1))) := by
        rintro rfl
        rcases hcode : M.code c.q (fun k => (c.tapes k).head) with _ | out
        · exact key_none M (n + 1) c ts rest hrep hgood hcode
        · exact key_some_succ M n c ts rest out hrep hgood hcode ih
      constructor
      · intro h
        exact (key (head_row M c ts hrep hgood e rest (h.2.1 e (by simp)) h.2.2.1 h.2.2.2)).1 h
      · intro h
        exact (key (rowsFrom_head M c (n + 1) e rest h.1)).2 h

/-! ### The start configuration and the main theorem -/

theorem sym_eq (b : Bool) : (code M).sym b = encG M (M.inputSymbol b) := by
  cases b <;> rfl

theorem absT_ofList (l : List M.Γ) : absT M (Tp.ofList (l.map (encG M))) = Turing.Tape.mk₁ l := by
  cases l with
  | nil => simp [absT, Tp.ofList, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', decG_zero]
  | cons a l =>
    simp [absT, Tp.ofList, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', decG_encG,
      List.map_map, Function.comp_def]

theorem good_ofList (l : List M.Γ) : Good M (Tp.ofList (l.map (encG M))) := by
  refine ⟨?_, by simp [Tp.ofList], ?_⟩
  · cases l with
    | nil => exact zero_mem_range M
    | cons a l => exact ⟨a, rfl⟩
  · intro a ha
    simp only [Tp.ofList] at ha
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_tail ha)
    exact ⟨g, rfl⟩

theorem start_eq (y : List Bool) (k : M.K) :
    (code M).start y (eK M k) = Tp.ofList
      ((if k = M.inputTape then y.map M.inputSymbol else []).map (encG M)) := by
  unfold MCode.start
  by_cases hk : k = M.inputTape
  · subst hk
    have h1 : ((eK M M.inputTape : Fin _) : ℕ) = (code M).inp := rfl
    rw [if_pos h1, if_pos rfl, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _
    exact sym_eq M b
  · have : ((eK M k : Fin _) : ℕ) ≠ (code M).inp := by
      simp only [code]
      intro h
      exact hk ((eK M).injective (Fin.ext h))
    simp [this, hk]

/-- **W1, functional level.** The transcript check accepts exactly the transcript of an accepting
run of at most `T` steps. -/
theorem check_iff (y : List Bool) (T : ℕ) (τ : List Entry) :
    Check (code M) y T τ ↔ τ = transcript M y T ∧ HaltsWithin M y true T := by
  have hrep : ∀ k : M.K, absT M ((code M).start y (eK M k)) = (M.init y).tapes k := by
    intro k
    rw [start_eq, absT_ofList]
    simp only [Machine.init]
    split_ifs <;> rfl
  have hgood : ∀ k : M.K, Good M ((code M).start y (eK M k)) := by
    intro k; rw [start_eq]; exact good_ofList M _
  have := main M T (M.init y) ((code M).start y) τ hrep hgood
  exact this

end Encode

end P1Hier
