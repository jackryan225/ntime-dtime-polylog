import P1Net.Regularize
import P1Net.Routing
import P1Net.Access

/-!
# P3 (lane P1-lean-net, copy A): the routed lane network `N_{x,σ}`, topology

Paper `subsec:network` (a)-(f), with OpenAI's slot conventions (`Compression.State a h`). Per big interval `ι`
the local vertices (`Loc K h`) are:
* `tabC`, `tabP c`: the small-interval table, as a centre and a path with one site per external string `c`
  (state in/out, contents of window `δ` of tape `k` in/out); lane `g` = small interval `ιN + g`;
* `portIn k δ`, `portOut k δ`: the incoming / outgoing big-block ports; lane `g` = small block
  `(q_k(ι) + δ - 1) N + g`;
* `rt k c π`: position (column `c`, type `π`) of the content routing of tape `k` (addresses `(π, lane)`, `h + 3`
  bits, `π` = three type bits: `0..2` In/Out ports, `3..5` table window `δ`, `6, 7` dummies);
* `st c π`: position of the state routing (`h + 1` bits; type `0` = the chain ends, type `1` = table);
* `eIn`, `eOut`: the ends of the state chain of the big interval (lane `0`).
Half-edge slots (`Fin 4`): path sites `0` = previous, `1` = next, `2` = external; ports and chain ends `0` = routing,
`1` = link to another big interval; routing positions `0` / `1` = straight / cross arc to the next column (or the
destination at the last column), `2` / `3` = straight / cross arc from the previous column (or the source at
column `0`). The cross arc of stage `c` flips the stage bit: in the type (base label) for a type bit, in the lane
(displacement) for a lane bit.

Links between big intervals (`interMate`): owner links `portOut (ι, k, δ) — portIn (ι', k, δ')` to the next owner
`ι'` of the same big block (depends on `σ`), and `eOut ι — eIn (ι + 1)`. Unused half-edges are unmated; the padding
of `P1Net.PreGraph.regularize` sends them to the twin.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression

/-! ## Local vertices -/

/-- The external strings of one small-interval table. -/
inductive Ext (K : Type) where
  | stIn
  | stOut
  | cIn (k : K) (δ : Fin 3)
  | cOut (k : K) (δ : Fin 3)
  deriving DecidableEq, Fintype

/-- The local vertices of one big interval. -/
inductive Loc (K : Type) (h : ℕ) where
  | tabC
  | tabP (c : Ext K)
  | portIn (k : K) (δ : Fin 3)
  | portOut (k : K) (δ : Fin 3)
  | rt (k : K) (c : Fin (2 * (h + 3))) (π : BitWord 3)
  | st (c : Fin (2 * (h + 1))) (π : BitWord 1)
  | eIn
  | eOut
  deriving DecidableEq, Fintype

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-! ## Columns, types and the order of the table path -/

/-- The next column. -/
def colSucc {n : ℕ} (c : Fin n) : Option (Fin n) := if hc : c.val + 1 < n then some ⟨c.val + 1, hc⟩ else none

/-- The previous column. -/
def colPred {n : ℕ} (c : Fin n) : Option (Fin n) := if hc : 0 < c.val then some ⟨c.val - 1, by omega⟩ else none

theorem colSucc_eq_some {n : ℕ} {c c' : Fin n} : colSucc c = some c' ↔ colPred c' = some c := by
  have h1 := c.isLt
  have h2 := c'.isLt
  unfold colSucc colPred
  constructor
  · intro hs
    by_cases hc : c.val + 1 < n
    · rw [dif_pos hc, Option.some.injEq] at hs
      subst hs
      simp [Fin.ext_iff]
    · rw [dif_neg hc] at hs
      exact absurd hs (by simp)
  · intro hp
    by_cases hc' : 0 < c'.val
    · rw [dif_pos hc', Option.some.injEq] at hp
      subst hp
      have e : c'.val - 1 + 1 = c'.val := by omega
      simp [Fin.ext_iff, e]
    · rw [dif_neg hc'] at hp
      exact absurd hp (by simp)

theorem colSucc_val {n : ℕ} {c c' : Fin n} (hs : colSucc c = some c') : c'.val = c.val + 1 := by
  unfold colSucc at hs
  by_cases hc : c.val + 1 < n
  · rw [dif_pos hc, Option.some.injEq] at hs
    subst hs
    rfl
  · rw [dif_neg hc] at hs
    exact absurd hs (by simp)

theorem colSucc_ne {n : ℕ} {c c' : Fin n} (hs : colSucc c = some c') : c' ≠ c := by
  intro e
  have := colSucc_val hs
  rw [e] at this
  omega

theorem colPred_ne {n : ℕ} {c c' : Fin n} (hp : colPred c = some c') : c' ≠ c := by
  intro e
  have := colSucc_val (colSucc_eq_some.2 hp)
  rw [e] at this
  omega

/-- First column. -/
def col0 (n : ℕ) : Fin (2 * (n + 1)) := ⟨0, by omega⟩

/-- Last column. -/
def colLast (n : ℕ) : Fin (2 * (n + 1)) := ⟨2 * (n + 1) - 1, by omega⟩

theorem colPred_col0 (n : ℕ) : colPred (col0 n) = none := by simp [colPred, col0]

theorem colSucc_colLast (n : ℕ) : colSucc (colLast n) = none := by
  unfold colSucc
  split_ifs with hc
  · exfalso
    simp only [colLast] at hc
    omega
  · rfl

theorem colPred_eq_none {n : ℕ} (c : Fin (2 * (n + 1))) (h : colPred c = none) : c = col0 n := by
  unfold colPred at h
  by_cases hc : 0 < c.val
  · rw [dif_pos hc] at h
    exact absurd h (by simp)
  · apply Fin.ext
    show c.val = 0
    omega

theorem colSucc_eq_none {n : ℕ} (c : Fin (2 * (n + 1))) (h : colSucc c = none) : c = colLast n := by
  have := c.isLt
  unfold colSucc at h
  by_cases hc : c.val + 1 < 2 * (n + 1)
  · rw [dif_pos hc] at h
    exact absurd h (by simp)
  · apply Fin.ext
    show c.val = 2 * (n + 1) - 1
    omega

/-- The type part of the flip of stage `κ` for addresses with `t` type bits followed by lane bits
(`m = t + l` bits in all). -/
def tyFlip (t l : ℕ) [NeZero (t + l)] (κ : ℕ) : BitWord t :=
  fun j => if (j : ℕ) = (Routing.stageBit (t + l) κ : ℕ) then 1 else 0

/-- The lane part of the flip of stage `κ`. -/
def lnFlip (t l : ℕ) [NeZero (t + l)] (κ : ℕ) : BitWord l :=
  fun j => if (j : ℕ) + t = (Routing.stageBit (t + l) κ : ℕ) then 1 else 0

theorem add_add_self {n : ℕ} (π f : BitWord n) : π + f + f = π := by
  funext j
  simp only [Pi.add_apply]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The type code of a number `< 8` (binary, bit `j` = `(n / 2^j) % 2`). -/
def code3 (n : ℕ) : BitWord 3 := fun j => ((n / 2 ^ (j : ℕ)) % 2 : ℕ)

/-- The number of a type. -/
def num3 (π : BitWord 3) : ℕ := (π 0).val + 2 * (π 1).val + 4 * (π 2).val

theorem num3_code3 (n : ℕ) (hn : n < 8) : num3 (code3 n) = n := by
  interval_cases n <;> decide

theorem code3_num3 (π : BitWord 3) : code3 (num3 π) = π := by
  revert π
  decide

theorem num3_lt (π : BitWord 3) : num3 π < 8 := by
  revert π
  decide

/-- The state type codes: `false` = chain end, `true` = table. -/
def code1 (b : Bool) : BitWord 1 := fun _ => if b then 1 else 0

theorem code1_cases (π : BitWord 1) : π = code1 false ∨ π = code1 true := by
  revert π
  decide

variable (K)

/-- The order of the table path (a fixed finite datum). -/
noncomputable def extIdx : Ext K ≃ Fin (Fintype.card (Ext K)) := Fintype.equivFin _

theorem card_ext_pos : 0 < Fintype.card (Ext K) := Fintype.card_pos_iff.2 ⟨.stIn⟩

/-- First site of the table path. -/
noncomputable def firstExt : Ext K := (extIdx K).symm ⟨0, card_ext_pos K⟩

variable {K}

/-- Previous site of the table path. -/
noncomputable def prevExt (c : Ext K) : Option (Ext K) :=
  if hc : 0 < (extIdx K c).val then some ((extIdx K).symm ⟨(extIdx K c).val - 1, by omega⟩) else none

/-- Next site of the table path. -/
noncomputable def nextExt (c : Ext K) : Option (Ext K) :=
  if hc : (extIdx K c).val + 1 < Fintype.card (Ext K) then
    some ((extIdx K).symm ⟨(extIdx K c).val + 1, hc⟩) else none

theorem nextExt_val {c c' : Ext K} (hs : nextExt c = some c') :
    (extIdx K c').val = (extIdx K c).val + 1 := by
  unfold nextExt at hs
  by_cases hc : (extIdx K c).val + 1 < Fintype.card (Ext K)
  · rw [dif_pos hc, Option.some.injEq] at hs
    subst hs
    simp
  · rw [dif_neg hc] at hs
    exact absurd hs (by simp)

theorem nextExt_eq_some {c c' : Ext K} : nextExt c = some c' ↔ prevExt c' = some c := by
  have h1 := (extIdx K c).isLt
  have h2 := (extIdx K c').isLt
  unfold nextExt prevExt
  constructor
  · intro hs
    by_cases hc : (extIdx K c).val + 1 < Fintype.card (Ext K)
    · rw [dif_pos hc, Option.some.injEq] at hs
      subst hs
      have e : 0 < (extIdx K ((extIdx K).symm ⟨(extIdx K c).val + 1, hc⟩)).val := by simp
      rw [dif_pos e, Option.some.injEq]
      apply (extIdx K).injective
      simp [Fin.ext_iff]
    · rw [dif_neg hc] at hs
      exact absurd hs (by simp)
  · intro hp
    by_cases hc' : 0 < (extIdx K c').val
    · rw [dif_pos hc', Option.some.injEq] at hp
      subst hp
      have e : (extIdx K ((extIdx K).symm ⟨(extIdx K c').val - 1, by omega⟩)).val + 1 <
          Fintype.card (Ext K) := by simp; omega
      rw [dif_pos e, Option.some.injEq]
      apply (extIdx K).injective
      simp only [Equiv.apply_symm_apply, Fin.ext_iff]
      omega
    · rw [dif_neg hc'] at hp
      exact absurd hp (by simp)

theorem prevExt_eq_none {c : Ext K} : prevExt c = none ↔ c = firstExt K := by
  unfold prevExt firstExt
  constructor
  · intro h
    by_cases hc : 0 < (extIdx K c).val
    · rw [dif_pos hc] at h
      exact absurd h (by simp)
    · apply (extIdx K).injective
      simp only [Equiv.apply_symm_apply]
      exact Fin.ext (by simp; omega)
  · intro h
    subst h
    simp

theorem nextExt_ne {c c' : Ext K} (h : nextExt c = some c') : c' ≠ c := by
  intro e
  have := nextExt_val h
  rw [e] at this
  omega

theorem prevExt_ne {c c' : Ext K} (h : prevExt c = some c') : c' ≠ c := by
  intro e
  have := nextExt_val (nextExt_eq_some.2 h)
  rw [e] at this
  omega

/-! ## The local topology -/

/-- Column `0` / last column of the content and state routings. -/
abbrev rcol0 (h : ℕ) : Fin (2 * (h + 3)) := col0 (h + 2)
abbrev rcolLast (h : ℕ) : Fin (2 * (h + 3)) := colLast (h + 2)
abbrev scol0 (h : ℕ) : Fin (2 * (h + 1)) := col0 h
abbrev scolLast (h : ℕ) : Fin (2 * (h + 1)) := colLast h

instance (h : ℕ) : NeZero (3 + h) := ⟨by omega⟩
instance (h : ℕ) : NeZero (1 + h) := ⟨by omega⟩

/-- Where the external string `c` of a table attaches. -/
def extAttach (c : Ext K) : Loc K h × Fin 4 :=
  match c with
  | .stIn => (.st (scolLast h) (code1 true), 0)
  | .stOut => (.st (scol0 h) (code1 true), 2)
  | .cIn k δ => (.rt k (rcolLast h) (code3 (3 + δ)), 0)
  | .cOut k δ => (.rt k (rcol0 h) (code3 (3 + δ)), 2)

/-- The destination attached to the last content-routing column (by type). -/
def rtDst (k : K) (π : BitWord 3) : Option (Loc K h × Fin 4) :=
  if h3 : num3 π < 3 then some (.portOut k ⟨num3 π, h3⟩, 0)
  else if h6 : num3 π < 6 then some (.tabP (.cIn k ⟨num3 π - 3, by omega⟩), 2) else none

/-- The source attached to content-routing column `0` (by type). -/
def rtSrc (k : K) (π : BitWord 3) : Option (Loc K h × Fin 4) :=
  if h3 : num3 π < 3 then some (.portIn k ⟨num3 π, h3⟩, 0)
  else if h6 : num3 π < 6 then some (.tabP (.cOut k ⟨num3 π - 3, by omega⟩), 2) else none

/-- The destination attached to the last state-routing column. -/
def stDst (π : BitWord 1) : Loc K h × Fin 4 :=
  if π = code1 false then (.eOut, 0) else (.tabP .stIn, 2)

/-- The source attached to state-routing column `0`. -/
def stSrc (π : BitWord 1) : Loc K h × Fin 4 :=
  if π = code1 false then (.eIn, 0) else (.tabP .stOut, 2)

/-- Half-edge partners inside one big interval. -/
noncomputable def locMate (l : Loc K h) (s : Fin 4) : Option (Loc K h × Fin 4) :=
  match l with
  | .tabC => if s = 0 then some (.tabP (firstExt K), 0) else none
  | .tabP c =>
    if s = 0 then
      (match prevExt c with
        | some c' => some (.tabP c', 1)
        | none => some (.tabC, 0))
    else if s = 1 then (nextExt c).map fun c' => (.tabP c', 0)
    else if s = 2 then some (extAttach c) else none
  | .portIn k δ => if s = 0 then some (.rt k (rcol0 h) (code3 δ), 2) else none
  | .portOut k δ => if s = 0 then some (.rt k (rcolLast h) (code3 δ), 0) else none
  | .rt k c π =>
    if s = 0 then
      (match colSucc c with
        | some c' => some (.rt k c' π, 2)
        | none => rtDst k π)
    else if s = 1 then (colSucc c).map fun c' => (.rt k c' (π + tyFlip 3 h c), 3)
    else if s = 2 then
      (match colPred c with
        | some c' => some (.rt k c' π, 0)
        | none => rtSrc k π)
    else (colPred c).map fun c' => (.rt k c' (π + tyFlip 3 h c'), 1)
  | .st c π =>
    if s = 0 then
      (match colSucc c with
        | some c' => some (.st c' π, 2)
        | none => some (stDst π))
    else if s = 1 then (colSucc c).map fun c' => (.st c' (π + tyFlip 1 h c), 3)
    else if s = 2 then
      (match colPred c with
        | some c' => some (.st c' π, 0)
        | none => some (stSrc π))
    else (colPred c).map fun c' => (.st c' (π + tyFlip 1 h c'), 1)
  | .eIn => if s = 0 then some (.st (scol0 h) (code1 false), 2) else none
  | .eOut => if s = 0 then some (.st (scolLast h) (code1 false), 0) else none

theorem code1_true_ne : code1 true ≠ code1 false := by decide

theorem fin4_three {s : Fin 4} (h0 : s ≠ 0) (h1 : s ≠ 1) (h2 : s ≠ 2) : s = 3 := by
  revert s; decide

theorem num3_code3_fin (δ : Fin 3) : num3 (code3 δ) = δ := num3_code3 _ (by omega)

theorem num3_code3_add (δ : Fin 3) : num3 (code3 (3 + δ)) = 3 + δ := num3_code3 _ (by omega)

/-- The source attached to column `0` of the content routing is the mate of that column's slot `2`. -/
theorem rtSrc_symm {k : K} {π : BitWord 3} {l' : Loc K h} {s' : Fin 4}
    (hm : rtSrc k π = some (l', s')) : locMate l' s' = some (.rt k (rcol0 h) π, 2) := by
  unfold rtSrc at hm
  by_cases h3 : num3 π < 3
  · rw [dif_pos h3, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [locMate, code3_num3]
  · rw [dif_neg h3] at hm
    by_cases h6 : num3 π < 6
    · rw [dif_pos h6, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have e : 3 + (num3 π - 3) = num3 π := by omega
      simp [locMate, extAttach, e, code3_num3]
    · rw [dif_neg h6] at hm
      exact absurd hm (by simp)

theorem rtDst_symm {k : K} {π : BitWord 3} {l' : Loc K h} {s' : Fin 4}
    (hm : rtDst k π = some (l', s')) : locMate l' s' = some (.rt k (rcolLast h) π, 0) := by
  unfold rtDst at hm
  by_cases h3 : num3 π < 3
  · rw [dif_pos h3, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [locMate, code3_num3]
  · rw [dif_neg h3] at hm
    by_cases h6 : num3 π < 6
    · rw [dif_pos h6, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have e : 3 + (num3 π - 3) = num3 π := by omega
      simp [locMate, extAttach, e, code3_num3]
    · rw [dif_neg h6] at hm
      exact absurd hm (by simp)

theorem stSrc_symm (π : BitWord 1) :
    locMate (stSrc (K := K) (h := h) π).1 (stSrc (K := K) (h := h) π).2 =
      some (.st (scol0 h) π, 2) := by
  rcases code1_cases π with rfl | rfl
  · simp [stSrc, locMate]
  · simp [stSrc, locMate, extAttach, code1_true_ne]

theorem stDst_symm (π : BitWord 1) :
    locMate (stDst (K := K) (h := h) π).1 (stDst (K := K) (h := h) π).2 =
      some (.st (scolLast h) π, 0) := by
  rcases code1_cases π with rfl | rfl
  · simp [stDst, locMate]
  · simp [stDst, locMate, extAttach, code1_true_ne]

/-- **The local mate is symmetric.** -/
theorem locMate_symm {l l' : Loc K h} {s s' : Fin 4} (hm : locMate l s = some (l', s')) :
    locMate l' s' = some (l, s) := by
  cases l with
  | tabC =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [locMate, prevExt_eq_none.2 rfl]
    · simp [locMate, h0] at hm
  | tabP c =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hp : prevExt c with
      | some c' =>
        rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [locMate, nextExt_eq_some.2 hp]
      | none =>
        rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [locMate, prevExt_eq_none.1 hp]
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hn : nextExt c with
        | none => rw [hn] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          simp [locMate, nextExt_eq_some.1 hn]
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte, Option.some.injEq] at hm
          cases c with
          | stIn =>
            simp only [extAttach, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_colLast, stDst, code1_true_ne]
          | stOut =>
            simp only [extAttach, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colPred_col0, stSrc, code1_true_ne]
          | cIn k δ =>
            simp only [extAttach, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_colLast, rtDst, num3_code3_add]
            have := δ.isLt
            omega
          | cOut k δ =>
            simp only [extAttach, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colPred_col0, rtSrc, num3_code3_add]
            have := δ.isLt
            omega
        · simp [locMate, h0, h1, h2] at hm
  | portIn k δ =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [locMate, colPred_col0, rtSrc, num3_code3_fin]
    · simp [locMate, h0] at hm
  | portOut k δ =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [locMate, colSucc_colLast, rtDst, num3_code3_fin]
    · simp [locMate, h0] at hm
  | rt k c π =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hs : colSucc c with
      | some c' =>
        rw [hs, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [locMate, colSucc_eq_some.1 hs]
      | none =>
        rw [hs] at hm
        rw [colSucc_eq_none c hs]
        exact rtDst_symm hm
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hs : colSucc c with
        | none => rw [hs] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          simp [locMate, colSucc_eq_some.1 hs, add_add_self]
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte] at hm
          cases hp : colPred c with
          | some c' =>
            rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_eq_some.2 hp]
          | none =>
            rw [hp] at hm
            rw [colPred_eq_none c hp]
            exact rtSrc_symm hm
        · have h3 := fin4_three h0 h1 h2
          subst h3
          simp only [locMate, if_neg (show (3 : Fin 4) ≠ 0 by decide),
            if_neg (show (3 : Fin 4) ≠ 1 by decide), if_neg (show (3 : Fin 4) ≠ 2 by decide)] at hm
          cases hp : colPred c with
          | none => rw [hp] at hm; exact absurd hm (by simp)
          | some c' =>
            rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_eq_some.2 hp, add_add_self]
  | st c π =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hs : colSucc c with
      | some c' =>
        rw [hs, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [locMate, colSucc_eq_some.1 hs]
      | none =>
        rw [hs, Option.some.injEq] at hm
        rw [colSucc_eq_none c hs]
        have := stDst_symm (K := K) (h := h) π
        rw [hm] at this
        exact this
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hs : colSucc c with
        | none => rw [hs] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          simp [locMate, colSucc_eq_some.1 hs, add_add_self]
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte] at hm
          cases hp : colPred c with
          | some c' =>
            rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_eq_some.2 hp]
          | none =>
            rw [hp, Option.some.injEq] at hm
            rw [colPred_eq_none c hp]
            have := stSrc_symm (K := K) (h := h) π
            rw [hm] at this
            exact this
        · have h3 := fin4_three h0 h1 h2
          subst h3
          simp only [locMate, if_neg (show (3 : Fin 4) ≠ 0 by decide),
            if_neg (show (3 : Fin 4) ≠ 1 by decide), if_neg (show (3 : Fin 4) ≠ 2 by decide)] at hm
          cases hp : colPred c with
          | none => rw [hp] at hm; exact absurd hm (by simp)
          | some c' =>
            rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            simp [locMate, colSucc_eq_some.2 hp, add_add_self]
  | eIn =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [locMate, colPred_col0, stSrc]
    · simp [locMate, h0] at hm
  | eOut =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp [locMate, colSucc_colLast, stDst]
    · simp [locMate, h0] at hm

end P1Net
