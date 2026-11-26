import P1P5.EvalCorrect

/-!
# P1, task P8a: the cone table algorithm is correct for ANY enumeration order

`enumL α = Finset.univ.toList` (EvalDefs.lean) is a noncomputable order, so no program can reproduce the keys
and pointers of `encLevels`. Here every order is a parameter:

* `LevelOrd t`: for one term `t`, the list `old` of old keys (the state read), the list `new` of new keys
  (the state written), for each new site `w` a list `pre w` of its preimage sites and a list `plc w` of
  the placed old half-assignments;
* `levelDataO t o`: the level with entries `(t.kernel w x z, pointers into old)` in these orders;
* `stepEval_levelDataO`: if `pre w` and `plc w` list each element exactly once and `old` contains every
  key `(u, x_u)` needed by the entries, one step writes `new.map (t.push F)`;
* `ChainOrd c`, `runLevels_encLevelsO`, `Wv_eq_runO`: the same along a chain, final value `W_v(z)` at the
  position of `(v, z)` in the final key list.

Only nodup and completeness of `pre` and `plc` are used; `old`, `new` may be any lists containing the
needed keys (duplicates allowed). `P1P5.Wv_eq_run` is the special case of the lists of `enumL`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression

open scoped Classical

noncomputable section

variable {R : Type} [CommRing R]

/-- The orders used by one level. -/
structure LevelOrd {N : Network} (t : Term R N) where
  old : List (Key N)
  new : List (Key t.output)
  pre : ∀ w, List (t.Preimage w)
  plc : ∀ w, List (Placed t.place N.Half w)

/-- A list that contains every element of the type exactly once. -/
def IsEnum {α : Type} (l : List α) : Prop := l.Nodup ∧ ∀ a, a ∈ l

/-- The state of the keys `keys` (any list). -/
def stateOfO {N : Network} (keys : List (Key N)) (F : Factors R N) : List R :=
  keys.map fun key => F key.1 key.2

/-- Pointers of one placed old half-assignment, in the order `pre`, into the key list `old`. -/
def pointersO {N : Network} (t : Term R N) (old : List (Key N)) {w : t.output.Site}
    (pre : List (t.Preimage w)) (x : Placed t.place N.Half w) : List ℕ :=
  pre.map fun u => old.idxOf (⟨u.1, x u.1 u.2⟩ : Key N)

/-- The entry of the new key `(w, z)` in the orders `o`. -/
def levelEntryO {N : Network} (t : Term R N) (o : LevelOrd t) (key : Key t.output) :
    List (R × List ℕ) :=
  (o.plc key.1).map fun x => (t.kernel key.1 x key.2, pointersO t o.old (o.pre key.1) x)

/-- The level data in the orders `o`. -/
def levelDataO {N : Network} (t : Term R N) (o : LevelOrd t) : Level R :=
  o.new.map (levelEntryO t o)

/-- Good orders for one level: `pre`, `plc` enumerate, and `old` contains the keys the entries read. -/
def LevelOrd.Good {N : Network} {t : Term R N} (o : LevelOrd t) : Prop :=
  (∀ w, IsEnum (o.pre w)) ∧ (∀ w, IsEnum (o.plc w)) ∧
    ∀ key ∈ o.new, ∀ (u : t.Preimage key.1) (x : N.Half u.1), (⟨u.1, x⟩ : Key N) ∈ o.old

theorem sum_isEnum {α : Type} [Fintype α] {M : Type*} [AddCommMonoid M] {l : List α} (h : IsEnum l)
    (g : α → M) : (l.map g).sum = ∑ a, g a := by
  have hl : l.toFinset = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun a => List.mem_toFinset.mpr (h.2 a))
  rw [← hl, List.sum_toFinset _ h.1]

theorem prod_isEnum {α : Type} [Fintype α] {M : Type*} [CommMonoid M] {l : List α} (h : IsEnum l)
    (g : α → M) : (l.map g).prod = ∏ a, g a := by
  have hl : l.toFinset = Finset.univ := Finset.eq_univ_iff_forall.mpr (fun a => List.mem_toFinset.mpr (h.2 a))
  rw [← hl, List.prod_toFinset _ h.1]

theorem stateOfO_getD {N : Network} (keys : List (Key N)) (F : Factors R N) {key : Key N}
    (h : key ∈ keys) : (stateOfO keys F).getD (keys.idxOf key) 0 = F key.1 key.2 := by
  have hlt : keys.idxOf key < keys.length := List.idxOf_lt_length_iff.mpr h
  unfold stateOfO
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf hlt]

/-- One entry computes one value of `Term.push`, in any good orders. -/
theorem entryEval_levelEntryO {N : Network} (t : Term R N) (o : LevelOrd t) (ho : o.Good)
    (F : Factors R N) (key : Key t.output) (hkey : key ∈ o.new) :
    entryEval (stateOfO o.old F) (levelEntryO t o key) = t.push F key.1 key.2 := by
  have hx : ∀ x : Placed t.place N.Half key.1,
      ((pointersO t o.old (o.pre key.1) x).map fun i => (stateOfO o.old F).getD i 0).prod =
        t.placedProduct F key.1 x := by
    intro x
    unfold pointersO
    rw [List.map_map]
    trans ((o.pre key.1).map (fun u => F u.1 (x u.1 u.2))).prod
    · congr 1
      apply List.map_congr_left
      intro u _
      exact stateOfO_getD o.old F (ho.2.2 key hkey u (x u.1 u.2))
    · rw [prod_isEnum (ho.1 key.1), Term.placedProduct]
      exact prod_preimage t F key.1 x
  unfold entryEval levelEntryO
  rw [List.map_map]
  trans ((o.plc key.1).map (fun x => t.placedProduct F key.1 x * t.kernel key.1 x key.2)).sum
  · congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [hx x]
  · rw [sum_isEnum (ho.2.1 key.1)]
    rfl

/-- One level writes the pushed factors on the new key list. -/
theorem stepEval_levelDataO {N : Network} (t : Term R N) (o : LevelOrd t) (ho : o.Good)
    (F : Factors R N) :
    stepEval (levelDataO t o) (stateOfO o.old F) = stateOfO o.new (t.push F) := by
  unfold stepEval levelDataO stateOfO
  rw [List.map_map]
  apply List.map_congr_left
  intro key hkey
  exact entryEval_levelEntryO t o ho F key hkey

/-- Orders along a chain: one `LevelOrd` per level. -/
def ChainOrd : {N Y : Network} → TermChain R N Y → Type
  | _, _, .done _ => PUnit
  | _, _, .more t _ tail => LevelOrd t × ChainOrd tail

/-- The levels in the orders `o`. -/
def encLevelsO : {N Y : Network} → (c : TermChain R N Y) → ChainOrd c → List (Level R)
  | _, _, .done _, _ => []
  | _, _, .more t _ tail, o => levelDataO t o.1 :: encLevelsO tail o.2

/-- The key list read by the first level (for the empty chain: the given final list). -/
def ChainOrd.first : {N Y : Network} → (c : TermChain R N Y) → ChainOrd c → List (Key Y) →
    List (Key N)
  | _, _, .done _, _, fin => fin
  | _, _, .more _ _ _, o, _ => o.1.old

/-- Good orders along a chain ending with the key list `fin`: each level is good and writes exactly the
list that the next level reads (the last level writes `fin`). -/
def ChainOrd.Good : {N Y : Network} → (c : TermChain R N Y) → ChainOrd c → List (Key Y) → Prop
  | _, _, .done _, _, _ => True
  | _, _, .more _ _ tail, o, fin => o.1.Good ∧ o.1.new = ChainOrd.first tail o.2 fin ∧
      ChainOrd.Good tail o.2 fin

/-- The whole algorithm along a chain writes the pushed factors on the final key list. -/
theorem runLevels_encLevelsO : ∀ {N Y : Network} (c : TermChain R N Y) (o : ChainOrd c)
    (fin : List (Key Y)), ChainOrd.Good c o fin → ∀ (F : Factors R N),
    runLevels (encLevelsO c o) (stateOfO (ChainOrd.first c o fin) F) = stateOfO fin (chainPush c F)
  | _, _, .done _, _, _, _, _ => rfl
  | _, _, .more t _ tail, o, fin, h, F => by
    obtain ⟨h1, h2, h3⟩ := h
    show runLevels (encLevelsO tail o.2) (stepEval (levelDataO t o.1) (stateOfO o.1.old F)) = _
    rw [stepEval_levelDataO t o.1 h1 F, h2]
    exact runLevels_encLevelsO tail o.2 fin h3 (t.push F)

/-- **Correctness of the cone evaluation in any good orders.** If the final key list contains `(v, z)`,
the run returns `W_v(z) = chainPush c F v z` at the position of `(v, z)`. -/
theorem Wv_eq_runO {N Y : Network} (c : TermChain R N Y) (o : ChainOrd c) (fin : List (Key Y))
    (ho : ChainOrd.Good c o fin) (F : Factors R N) (v : Y.Site) (z : Y.Half v)
    (hz : (⟨v, z⟩ : Key Y) ∈ fin) :
    chainPush c F v z =
      (runLevels (encLevelsO c o) (stateOfO (ChainOrd.first c o fin) F)).getD (fin.idxOf ⟨v, z⟩) 0 := by
  rw [runLevels_encLevelsO c o fin ho F]
  exact (stateOfO_getD fin (chainPush c F) hz).symm

end

end P1P5
