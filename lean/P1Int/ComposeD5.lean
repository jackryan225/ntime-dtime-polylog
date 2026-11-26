import P1Int.ComposeStage

/-!
# P1Int.ComposeD5: composition layer 3a, the D5 stage order (owner: P1-lean-integ)

Decision D5 (G3-chief, PLAN.md section 9): family codes 0 C1, 1 C2, 2 C3, 3 C4, 4-8 C5-C9, 9 C10, 10 C11, 11 C12,
12 C13link, 13 C13ends, 14 C14, 15 accept; stage order C1-C3, C14, C4, per level C5-C9 then C10, C11, C12, C13.

* `D5Index`: the index data of one input: the number of levels `top`, the index count `cnt c` of family `c`, and the
  level `lev c i` of index `i` of a per-level family (C5-C10).
* `D5Index.stg`: the stage of check `(c, i)`; `K = 7 + 2 top` stages:
  0 OUT (family 15, every index `i ≥ cnt c`, every per-level index with level `≥ top`), 1 C1-C3, 2 C14, 3 C4,
  `4 + 2 l` C5-C9 at level `l`, `5 + 2 l` C10 at level `l` (`l < top`), `4 + 2 top` C11, `5 + 2 top` C12,
  `6 + 2 top` C13link + C13ends.
* `D5Groups U`: one predicate per group ("group true", in the owner lane's vocabulary); `D5Groups.P` numbers them.
* `D5Steps`: the NAMED inputs, one field per group (the step of the owner lane) plus `out` and `form`.
* `groupEquiv_of_d5 : D5Steps .. → GroupEquiv ..` (then `stagedEquiv_of_groups`, `pass_iff_of_staged`).
-/

namespace P1Int

namespace P11

/-- The D5 index data of one input. -/
structure D5Index where
  /-- number of levels with a pass (C5-C10 run at levels `l < top`) -/
  top : ℕ
  /-- index count of family `c` (indices `i ≥ cnt c` accept: the lanes' `Ck_out`) -/
  cnt : ℕ → ℕ
  /-- level of index `i` of a per-level family `c` (C5-C10) -/
  lev : ℕ → ℕ → ℕ

namespace D5Index

variable (X : D5Index)

/-- Number of stages. -/
def K : ℕ := 7 + 2 * X.top

/-- The stage of check `(c, i)` (decision D5). -/
def stg (c i : ℕ) : ℕ :=
  if c = 15 ∨ X.cnt c ≤ i then 0
  else if c ≤ 2 then 1
  else if c = 14 then 2
  else if c = 3 then 3
  else if c ≤ 8 then (if X.lev c i < X.top then 4 + 2 * X.lev c i else 0)
  else if c = 9 then (if X.lev c i < X.top then 5 + 2 * X.lev c i else 0)
  else if c = 10 then 4 + 2 * X.top
  else if c = 11 then 5 + 2 * X.top
  else 6 + 2 * X.top

theorem stg_lt (c i : ℕ) : X.stg c i < 7 + 2 * X.top := by
  unfold stg
  split_ifs <;> omega

theorem stg_eq_one (c i : ℕ) : X.stg c i = 1 ↔ c ≤ 2 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2⟩
    unfold stg
    rw [if_neg (by omega), if_pos h1]

theorem stg_eq_two (c i : ℕ) : X.stg c i = 2 ↔ c = 14 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2⟩
    subst h1
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem stg_eq_three (c i : ℕ) : X.stg c i = 3 ↔ c = 3 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2⟩
    subst h1
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem stg_eq_greedy {l : ℕ} (hl : l < X.top) (c i : ℕ) :
    X.stg c i = 4 + 2 * l ↔ 4 ≤ c ∧ c ≤ 8 ∧ i < X.cnt c ∧ X.lev c i = l := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h4, h8, h2, hlev⟩
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h8,
      if_pos (by omega)] <;> omega

theorem stg_eq_c10 {l : ℕ} (hl : l < X.top) (c i : ℕ) :
    X.stg c i = 5 + 2 * l ↔ c = 9 ∧ i < X.cnt c ∧ X.lev c i = l := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2, hlev⟩
    subst h1
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl, if_pos (by omega)] <;> omega

theorem stg_eq_c11 (c i : ℕ) : X.stg c i = 4 + 2 * X.top ↔ c = 10 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2⟩
    subst h1
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl]

theorem stg_eq_c12 (c i : ℕ) : X.stg c i = 5 + 2 * X.top ↔ c = 11 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h2⟩
    subst h1
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem stg_eq_c13 (c i : ℕ) (hc : c < 16) :
    X.stg c i = 6 + 2 * X.top ↔ 12 ≤ c ∧ c ≤ 13 ∧ i < X.cnt c := by
  constructor
  · intro h
    unfold stg at h
    split_ifs at h <;> omega
  · rintro ⟨h1, h3, h2⟩
    unfold stg
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end D5Index

/-- One predicate per D5 group: "the fields of this group are true" (the owner lane's vocabulary). -/
structure D5Groups (U : Type*) where
  dir : U → Prop
  c14 : U → Prop
  c4 : U → Prop
  greedy : ℕ → U → Prop
  c10 : ℕ → U → Prop
  c11 : U → Prop
  c12 : U → Prop
  c13 : U → Prop

namespace D5Groups

variable {U : Type*} (G : D5Groups U)

/-- The group predicates numbered by stage (stage 0 = OUT: `True`). -/
def P (top j : ℕ) (u : U) : Prop :=
  if j = 0 then True
  else if j = 1 then G.dir u
  else if j = 2 then G.c14 u
  else if j = 3 then G.c4 u
  else if j < 4 + 2 * top then (if j % 2 = 0 then G.greedy ((j - 4) / 2) u else G.c10 ((j - 5) / 2) u)
  else if j = 4 + 2 * top then G.c11 u
  else if j = 5 + 2 * top then G.c12 u
  else G.c13 u

theorem P_zero (top : ℕ) (u : U) : G.P top 0 u = True := by
  unfold P; rw [if_pos rfl]

theorem P_one (top : ℕ) (u : U) : G.P top 1 u = G.dir u := by
  unfold P; rw [if_neg (by omega), if_pos rfl]

theorem P_two (top : ℕ) (u : U) : G.P top 2 u = G.c14 u := by
  unfold P; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem P_three (top : ℕ) (u : U) : G.P top 3 u = G.c4 u := by
  unfold P; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem P_greedy {top l : ℕ} (hl : l < top) (u : U) : G.P top (4 + 2 * l) u = G.greedy l u := by
  unfold P
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos (by omega)]
  congr 1
  omega

theorem P_c10 {top l : ℕ} (hl : l < top) (u : U) : G.P top (5 + 2 * l) u = G.c10 l u := by
  unfold P
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg (by omega)]
  congr 1
  omega

theorem P_c11 (top : ℕ) (u : U) : G.P top (4 + 2 * top) u = G.c11 u := by
  unfold P
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem P_c12 (top : ℕ) (u : U) : G.P top (5 + 2 * top) u = G.c12 u := by
  unfold P
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem P_c13 (top : ℕ) (u : U) : G.P top (6 + 2 * top) u = G.c13 u := by
  unfold P
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

end D5Groups

/-- **The named inputs of the composition, one per D5 group.** `ni = 2 ^ (k - 4)` index words; `ck c u i`: the
decision of family `c` on witness `u` at index `i`. Owners: `out` every family lane (`Ck_out`); `dir`, `c14`, `c4`,
`greedy`, `c11`, `c12`, `c13`: P1-lean-checks (`c13` with P1-lean-eval for the cone); `c10`: P1-lean-c10;
`form`: P1-lean-integ. -/
structure D5Steps {U Tup : Type*} (enc : Tup → U) (Good : Tup → Prop) (ck : ℕ → U → ℕ → Bool) (ni : ℕ)
    (X : D5Index) (G : D5Groups U) : Prop where
  out : ∀ u, ∀ c < 16, ∀ i < ni, X.stg c i = 0 → ck c u i = true
  dir : ∀ u, (∀ c ≤ 2, ∀ i < ni, i < X.cnt c → ck c u i = true) ↔ G.dir u
  c14 : ∀ u, G.dir u → ((∀ i < ni, i < X.cnt 14 → ck 14 u i = true) ↔ G.c14 u)
  c4 : ∀ u, G.dir u → G.c14 u → ((∀ i < ni, i < X.cnt 3 → ck 3 u i = true) ↔ G.c4 u)
  greedy : ∀ l < X.top, ∀ u, (∀ k < 4 + 2 * l, G.P X.top k u) →
    ((∀ c, 4 ≤ c → c ≤ 8 → ∀ i < ni, i < X.cnt c → X.lev c i = l → ck c u i = true) ↔ G.greedy l u)
  c10 : ∀ l < X.top, ∀ u, (∀ k < 5 + 2 * l, G.P X.top k u) →
    ((∀ i < ni, i < X.cnt 9 → X.lev 9 i = l → ck 9 u i = true) ↔ G.c10 l u)
  c11 : ∀ u, (∀ k < 4 + 2 * X.top, G.P X.top k u) →
    ((∀ i < ni, i < X.cnt 10 → ck 10 u i = true) ↔ G.c11 u)
  c12 : ∀ u, (∀ k < 5 + 2 * X.top, G.P X.top k u) →
    ((∀ i < ni, i < X.cnt 11 → ck 11 u i = true) ↔ G.c12 u)
  c13 : ∀ u, (∀ k < 6 + 2 * X.top, G.P X.top k u) →
    ((∀ c, 12 ≤ c → c ≤ 13 → ∀ i < ni, i < X.cnt c → ck c u i = true) ↔ G.c13 u)
  form : ∀ u, (∀ k < X.K, G.P X.top k u) ↔ ∃ t, Good t ∧ enc t = u

/-- **Layer 3a: the D5 stage order gives the group form.** -/
theorem groupEquiv_of_d5 {U Tup : Type*} {enc : Tup → U} {Good : Tup → Prop} {ck : ℕ → U → ℕ → Bool}
    {ni : ℕ} (X : D5Index) (G : D5Groups U) (h : D5Steps enc Good ck ni X G) :
    GroupEquiv enc Good ck 16 ni := by
  refine ⟨X.K, X.stg, G.P X.top, fun c _ i _ => X.stg_lt c i, ?_, h.form⟩
  intro j hj u hu
  have hK : X.K = 7 + 2 * X.top := rfl
  by_cases h0 : j = 0
  · subst h0
    rw [G.P_zero]
    exact ⟨fun _ => trivial, fun _ c hc i hi hs => h.out u c hc i hi hs⟩
  by_cases h1 : j = 1
  · subst h1
    rw [G.P_one, ← h.dir u]
    constructor
    · intro hall c hc i hi hcnt
      exact hall c (by omega) i hi ((X.stg_eq_one c i).2 ⟨hc, hcnt⟩)
    · intro hall c _ i hi hs
      obtain ⟨hc, hcnt⟩ := (X.stg_eq_one c i).1 hs
      exact hall c hc i hi hcnt
  have hdir : G.dir u := by
    have := hu 1 (by omega)
    rwa [G.P_one] at this
  by_cases h2 : j = 2
  · subst h2
    rw [G.P_two, ← h.c14 u hdir]
    constructor
    · intro hall i hi hcnt
      exact hall 14 (by omega) i hi ((X.stg_eq_two 14 i).2 ⟨rfl, hcnt⟩)
    · intro hall c _ i hi hs
      obtain ⟨hc, hcnt⟩ := (X.stg_eq_two c i).1 hs
      subst hc
      exact hall i hi hcnt
  have hc14 : G.c14 u := by
    have := hu 2 (by omega)
    rwa [G.P_two] at this
  by_cases h3 : j = 3
  · subst h3
    rw [G.P_three, ← h.c4 u hdir hc14]
    constructor
    · intro hall i hi hcnt
      exact hall 3 (by omega) i hi ((X.stg_eq_three 3 i).2 ⟨rfl, hcnt⟩)
    · intro hall c _ i hi hs
      obtain ⟨hc, hcnt⟩ := (X.stg_eq_three c i).1 hs
      subst hc
      exact hall i hi hcnt
  by_cases hlv : j < 4 + 2 * X.top
  · by_cases hpar : j % 2 = 0
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < X.top ∧ j = 4 + 2 * l := ⟨(j - 4) / 2, by omega, by omega⟩
      rw [G.P_greedy hl, ← h.greedy l hl u hu]
      constructor
      · intro hall c hc4 hc8 i hi hcnt hlev
        exact hall c (by omega) i hi ((X.stg_eq_greedy hl c i).2 ⟨hc4, hc8, hcnt, hlev⟩)
      · intro hall c _ i hi hs
        obtain ⟨hc4, hc8, hcnt, hlev⟩ := (X.stg_eq_greedy hl c i).1 hs
        exact hall c hc4 hc8 i hi hcnt hlev
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < X.top ∧ j = 5 + 2 * l := ⟨(j - 5) / 2, by omega, by omega⟩
      rw [G.P_c10 hl, ← h.c10 l hl u hu]
      constructor
      · intro hall i hi hcnt hlev
        exact hall 9 (by omega) i hi ((X.stg_eq_c10 hl 9 i).2 ⟨rfl, hcnt, hlev⟩)
      · intro hall c _ i hi hs
        obtain ⟨hc, hcnt, hlev⟩ := (X.stg_eq_c10 hl c i).1 hs
        subst hc
        exact hall i hi hcnt hlev
  by_cases h11 : j = 4 + 2 * X.top
  · subst h11
    rw [G.P_c11, ← h.c11 u hu]
    constructor
    · intro hall i hi hcnt
      exact hall 10 (by omega) i hi ((X.stg_eq_c11 10 i).2 ⟨rfl, hcnt⟩)
    · intro hall c _ i hi hs
      obtain ⟨hc, hcnt⟩ := (X.stg_eq_c11 c i).1 hs
      subst hc
      exact hall i hi hcnt
  by_cases h12 : j = 5 + 2 * X.top
  · subst h12
    rw [G.P_c12, ← h.c12 u hu]
    constructor
    · intro hall i hi hcnt
      exact hall 11 (by omega) i hi ((X.stg_eq_c12 11 i).2 ⟨rfl, hcnt⟩)
    · intro hall c _ i hi hs
      obtain ⟨hc, hcnt⟩ := (X.stg_eq_c12 c i).1 hs
      subst hc
      exact hall i hi hcnt
  obtain rfl : j = 6 + 2 * X.top := by omega
  rw [G.P_c13, ← h.c13 u hu]
  constructor
  · intro hall c hc12 hc13 i hi hcnt
    exact hall c (by omega) i hi ((X.stg_eq_c13 c i (by omega)).2 ⟨hc12, hc13, hcnt⟩)
  · intro hall c hc i hi hs
    obtain ⟨hc12, hc13, hcnt⟩ := (X.stg_eq_c13 c i hc).1 hs
    exact hall c hc12 hc13 i hi hcnt

/-- **Layer 3a, end to end for one input**: the D5 steps give the Bool equivalence. -/
theorem pass_iff_of_d5 {U Tup : Type*} {enc : Tup → U} {Good : Tup → Prop} {ck : ℕ → U → ℕ → Bool}
    {ni : ℕ} (X : D5Index) (G : D5Groups U) (h : D5Steps enc Good ck ni X G) (u : U) :
    (∀ c < 16, ∀ i < ni, ck c u i = true) ↔ ∃ t, Good t ∧ enc t = u :=
  pass_iff_of_staged (stagedEquiv_of_groups (groupEquiv_of_d5 X G h)) u

end P11

end P1Int

#print axioms P1Int.P11.groupEquiv_of_d5
#print axioms P1Int.P11.pass_iff_of_d5
