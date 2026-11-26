import P1P5.EvalDefs

/-!
# P1, task P8a: correctness of the cone table algorithm

`Wv_eq_run`: for every term chain (in particular the selected chain of every branch of
`B.execute`), every final site `v` and half-assignment `z`, the pushed factor is the entry
`finalIndex z` of the table algorithm run on the cone encoding:
`chainPush c F v z = (runLevels (encLevels c v) (stateOf N (cone of v) F)).getD (finalIndex Y v z) 0`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression

open scoped Classical

noncomputable section

variable {R : Type} [CommRing R]

theorem mem_enumL {α : Type} [Fintype α] (a : α) : a ∈ enumL α := by
  simp [enumL]

theorem mem_keysOf {N : Network} {S : N.Site → Prop} {u : N.Site} (hu : S u) (x : N.Half u) :
    (⟨u, x⟩ : Key N) ∈ keysOf N S := by
  unfold keysOf
  rw [List.mem_flatMap]
  exact ⟨u, List.mem_filter.mpr ⟨mem_enumL u, by simpa using hu⟩,
    List.mem_map.mpr ⟨x, mem_enumL x, rfl⟩⟩

theorem fst_of_mem_keysOf {N : Network} {S : N.Site → Prop} {key : Key N}
    (h : key ∈ keysOf N S) : S key.1 := by
  unfold keysOf at h
  rw [List.mem_flatMap] at h
  obtain ⟨u, hu, hk⟩ := h
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hk
  simpa using (List.mem_filter.mp hu).2

/-- Reading a state at the position of one of its keys. -/
theorem stateOf_getD {N : Network} (S : N.Site → Prop) (F : Factors R N) {key : Key N}
    (h : key ∈ keysOf N S) :
    (stateOf N S F).getD ((keysOf N S).idxOf key) 0 = F key.1 key.2 := by
  have hlt : (keysOf N S).idxOf key < (keysOf N S).length := List.idxOf_lt_length_iff.mpr h
  unfold stateOf
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf hlt]

/-- A product over the placement fibre equals the dependent product over all old sites. -/
theorem prod_preimage {N : Network} (t : Term R N) (F : Factors R N) (w : t.output.Site)
    (x : Placed t.place N.Half w) :
    (∏ u : t.Preimage w, F u.1 (x u.1 u.2)) =
      ∏ u, if h : w = t.place u then F u (x u h) else 1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun u => w = t.place u)
    (fun u => if h : w = t.place u then F u (x u h) else 1)]
  have h1 : (∏ u : {u // ¬ w = t.place u},
      (if h : w = t.place u.1 then F u.1 (x u.1 h) else 1)) = 1 :=
    Finset.prod_eq_one (fun u _ => dif_neg u.2)
  rw [h1, mul_one]
  exact Finset.prod_congr rfl (fun u _ => by rw [dif_pos u.2])

/-- One entry of the algorithm computes one value of `Term.push`. -/
theorem entryEval_levelEntry {N : Network} (t : Term R N) (S' : t.output.Site → Prop)
    (F : Factors R N) (key : Key t.output) (hw : S' key.1) :
    entryEval (stateOf N (fun u => S' (t.place u)) F) (levelEntry t (fun u => S' (t.place u)) key) =
      t.push F key.1 key.2 := by
  have hlook : ∀ (x : Placed t.place N.Half key.1) (u : t.Preimage key.1),
      (stateOf N (fun u => S' (t.place u)) F).getD
        ((keysOf N fun u => S' (t.place u)).idxOf (⟨u.1, x u.1 u.2⟩ : Key N)) 0 =
        F u.1 (x u.1 u.2) := by
    intro x u
    have hu : S' (t.place u.1) := u.2 ▸ hw
    exact stateOf_getD (fun u => S' (t.place u)) F
      (mem_keysOf (S := fun u => S' (t.place u)) (u := u.1) hu (x u.1 u.2))
  have hx : ∀ x : Placed t.place N.Half key.1,
      ((pointers t (fun u => S' (t.place u)) key.1 x).map fun i =>
        (stateOf N (fun u => S' (t.place u)) F).getD i 0).prod = t.placedProduct F key.1 x := by
    intro x
    unfold pointers
    rw [List.map_map]
    trans ((enumL (t.Preimage key.1)).map (fun u => F u.1 (x u.1 u.2))).prod
    · congr 1
      apply List.map_congr_left
      intro u _
      exact hlook x u
    · unfold enumL
      rw [Finset.prod_map_toList, Term.placedProduct]
      exact prod_preimage t F key.1 x
  have h2 : (levelEntry t (fun u => S' (t.place u)) key).map
      (fun p => (p.2.map fun i => (stateOf N (fun u => S' (t.place u)) F).getD i 0).prod * p.1) =
      (enumL (Placed t.place N.Half key.1)).map
        (fun x => t.placedProduct F key.1 x * t.kernel key.1 x key.2) := by
    unfold levelEntry
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [hx x]
  unfold entryEval
  rw [h2]
  unfold enumL
  rw [Finset.sum_map_toList]
  rfl

/-- One level of the algorithm computes `Term.push` on the new cone. -/
theorem stepEval_levelData {N : Network} (t : Term R N) (S' : t.output.Site → Prop)
    (F : Factors R N) :
    stepEval (levelData t (fun u => S' (t.place u)) S') (stateOf N (fun u => S' (t.place u)) F) =
      stateOf t.output S' (t.push F) := by
  unfold stepEval levelData
  rw [List.map_map]
  unfold stateOf
  apply List.map_congr_left
  intro key hkey
  exact entryEval_levelEntry t S' F key (fst_of_mem_keysOf hkey)

/-- The whole algorithm along a chain computes the pushed factors on the final cone. -/
theorem runLevels_encLevels : ∀ {N Y : Network} (c : TermChain R N Y) (v : Y.Site)
    (F : Factors R N),
    runLevels (encLevels c v) (stateOf N (fun u => toFinal c u = v) F) =
      stateOf Y (fun w => w = v) (chainPush c F) := by
  intro N Y c
  induction c with
  | done N =>
    intro v F
    rfl
  | more t recs tail ih =>
    intro v F
    show runLevels (encLevels tail v)
        (stepEval (levelData t (fun u => toFinal tail (t.place u) = v) (fun w => toFinal tail w = v))
          (stateOf _ (fun u => toFinal tail (t.place u) = v) F)) = _
    rw [stepEval_levelData t (fun w => toFinal tail w = v) F]
    exact ih v (t.push F)

/-- **Correctness of the cone evaluation.** -/
theorem Wv_eq_run {N Y : Network} (c : TermChain R N Y) (F : Factors R N) (v : Y.Site)
    (z : Y.Half v) :
    chainPush c F v z =
      (runLevels (encLevels c v) (stateOf N (fun u => toFinal c u = v) F)).getD
        (finalIndex Y v z) 0 := by
  rw [runLevels_encLevels, finalIndex]
  exact (stateOf_getD (fun w => w = v) (chainPush c F) (mem_keysOf (S := fun w => w = v) rfl z)).symm

end

end P1P5
