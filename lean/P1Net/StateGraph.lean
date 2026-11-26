import P1Net.Numbering

/-!
# P3 (lane P1-lean-net, copy A): the pre-network of `N_{x,σ}` and its compression state

* `locMate_ne`: no local loops.
* Owners: `bigQ σ k ι` = big block of head `k` at the start of big interval `ι` (from the skeleton candidate
  `σ`), `Owns`, `nextOwner`, `prevOwner` (`nextOwner_iff`: the owner links are symmetric).
* `interMate`: owner links `portOut — portIn` and chain links `eOut ι — eIn (ι + 1)` (slot `1`).
* `netMate` (local mates, else links), `netMate_symm`, `netMate_ne`; `netDisp` (lane displacement: the lane part of
  the stage flip on the cross arcs of the routings, `0` elsewhere), symmetric by construction.
* `preGraph I σ : PreGraph h`, base order: big interval major, then a fixed order of the local vertices.
* `netWidth`: payload widths (content `Wc`, state `Ws`, table tuple `Wt`) on the payload orientation of every mated
  half-edge, `0` on unmated half-edges; `stateNet I σ ha Wc Ws Wt : State a h`.
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

/-- No local loops. -/
theorem locMate_ne {l l' : Loc K h} {s s' : Fin 4} (hm : locMate l s = some (l', s')) : l' ≠ l := by
  cases l with
  | tabC =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      simp
    · simp [locMate, h0] at hm
  | tabP c =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hp : prevExt c with
      | some c' =>
        rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        intro e
        injection e with e
        exact prevExt_ne hp e
      | none =>
        rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        simp
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hn : nextExt c with
        | none => rw [hn] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, -⟩ := hm
          intro e
          injection e with e
          exact nextExt_ne hn e
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte, Option.some.injEq] at hm
          cases c <;> simp only [extAttach, Prod.mk.injEq] at hm <;> obtain ⟨rfl, -⟩ := hm <;> simp
        · simp [locMate, h0, h1, h2] at hm
  | portIn k δ =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      simp
    · simp [locMate, h0] at hm
  | portOut k δ =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      simp
    · simp [locMate, h0] at hm
  | rt k c π =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hs : colSucc c with
      | some c' =>
        rw [hs, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        intro e
        injection e with _ e
        exact colSucc_ne hs e
      | none =>
        rw [hs] at hm
        unfold rtDst at hm
        split_ifs at hm <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hm
        all_goals (obtain ⟨rfl, -⟩ := hm; simp)
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hs : colSucc c with
        | none => rw [hs] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, -⟩ := hm
          intro e
          injection e with _ e
          exact colSucc_ne hs e
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte] at hm
          cases hp : colPred c with
          | some c' =>
            rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            intro e
            injection e with _ e
            exact colPred_ne hp e
          | none =>
            rw [hp] at hm
            unfold rtSrc at hm
            split_ifs at hm <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hm
            all_goals (obtain ⟨rfl, -⟩ := hm; simp)
        · have h3 := fin4_three h0 h1 h2
          subst h3
          simp only [locMate, if_neg (show (3 : Fin 4) ≠ 0 by decide),
            if_neg (show (3 : Fin 4) ≠ 1 by decide), if_neg (show (3 : Fin 4) ≠ 2 by decide)] at hm
          cases hp : colPred c with
          | none => rw [hp] at hm; exact absurd hm (by simp)
          | some c' =>
            rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            intro e
            injection e with _ e
            exact colPred_ne hp e
  | st c π =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte] at hm
      cases hs : colSucc c with
      | some c' =>
        rw [hs, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        intro e
        injection e with e
        exact colSucc_ne hs e
      | none =>
        rw [hs, Option.some.injEq] at hm
        unfold stDst at hm
        split_ifs at hm <;> simp only [Prod.mk.injEq] at hm <;> obtain ⟨rfl, -⟩ := hm <;> simp
    · by_cases h1 : s = 1
      · subst h1
        simp only [locMate, if_neg (show (1 : Fin 4) ≠ 0 by decide), ↓reduceIte] at hm
        cases hs : colSucc c with
        | none => rw [hs] at hm; exact absurd hm (by simp)
        | some c' =>
          rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, -⟩ := hm
          intro e
          injection e with e
          exact colSucc_ne hs e
      · by_cases h2 : s = 2
        · subst h2
          simp only [locMate, if_neg (show (2 : Fin 4) ≠ 0 by decide),
            if_neg (show (2 : Fin 4) ≠ 1 by decide), ↓reduceIte] at hm
          cases hp : colPred c with
          | some c' =>
            rw [hp, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            intro e
            injection e with e
            exact colPred_ne hp e
          | none =>
            rw [hp, Option.some.injEq] at hm
            unfold stSrc at hm
            split_ifs at hm <;> simp only [Prod.mk.injEq] at hm <;> obtain ⟨rfl, -⟩ := hm <;> simp
        · have h3 := fin4_three h0 h1 h2
          subst h3
          simp only [locMate, if_neg (show (3 : Fin 4) ≠ 0 by decide),
            if_neg (show (3 : Fin 4) ≠ 1 by decide), if_neg (show (3 : Fin 4) ≠ 2 by decide)] at hm
          cases hp : colPred c with
          | none => rw [hp] at hm; exact absurd hm (by simp)
          | some c' =>
            rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            intro e
            injection e with e
            exact colPred_ne hp e
  | eIn =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      simp
    · simp [locMate, h0] at hm
  | eOut =>
    by_cases h0 : s = 0
    · subst h0
      simp only [locMate, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, -⟩ := hm
      simp
    · simp [locMate, h0] at hm

/-! ## Owners of big blocks and links between big intervals -/

variable (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3)

/-- The big block of head `k` at the start of big interval `ι` (for the skeleton candidate `σ`). -/
def bigQ (k : K) (ι : ℕ) : ℤ := betaOf σ k (ι * 2 ^ h) / ((2 ^ h : ℕ) : ℤ)

/-- Big interval `ι` owns big block `Q` of tape `k`. -/
def Owns (k : K) (ι : ℕ) (Q : ℤ) : Prop := bigQ I σ k ι - 1 ≤ Q ∧ Q ≤ bigQ I σ k ι + 1

instance (k : K) (ι : ℕ) (Q : ℤ) : Decidable (Owns I σ k ι Q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The big block of port `δ` of big interval `ι`. -/
def portQ (k : K) (ι : ℕ) (δ : Fin 3) : ℤ := bigQ I σ k ι - 1 + (δ : ℤ)

/-- The port of big block `Q` in big interval `ι`. -/
def portSlot (k : K) (ι : ℕ) (Q : ℤ) : Fin 3 := finOfInt 3 (Q - bigQ I σ k ι + 1)

theorem owns_portQ (k : K) (ι : ℕ) (δ : Fin 3) : Owns I σ k ι (portQ I σ k ι δ) := by
  have := δ.isLt
  unfold Owns portQ
  constructor <;> omega

theorem portSlot_portQ (k : K) (ι : ℕ) (δ : Fin 3) : portSlot I σ k ι (portQ I σ k ι δ) = δ := by
  unfold portSlot portQ
  rw [show bigQ I σ k ι - 1 + (δ : ℤ) - bigQ I σ k ι + 1 = ((δ : ℕ) : ℤ) by ring]
  exact finOfInt_coe 3 δ

theorem portQ_portSlot {k : K} {ι : ℕ} {Q : ℤ} (hQ : Owns I σ k ι Q) :
    portQ I σ k ι (portSlot I σ k ι Q) = Q := by
  unfold portQ portSlot
  obtain ⟨h1, h2⟩ := hQ
  rw [finOfInt_val 3 (by omega) (by push_cast; omega)]
  ring

/-- The next owner of big block `Q` after big interval `ι`. -/
def nextOwner (k : K) (ι : Fin I) (Q : ℤ) : Option (Fin I) :=
  if hS : (Finset.univ.filter fun j : Fin I => ι < j ∧ Owns I σ k j Q).Nonempty then
    some ((Finset.univ.filter fun j : Fin I => ι < j ∧ Owns I σ k j Q).min' hS) else none

/-- The previous owner of big block `Q` before big interval `ι`. -/
def prevOwner (k : K) (ι : Fin I) (Q : ℤ) : Option (Fin I) :=
  if hS : (Finset.univ.filter fun j : Fin I => j < ι ∧ Owns I σ k j Q).Nonempty then
    some ((Finset.univ.filter fun j : Fin I => j < ι ∧ Owns I σ k j Q).max' hS) else none

variable {I σ}

theorem nextOwner_spec {k : K} {ι ι' : Fin I} {Q : ℤ} (hn : nextOwner I σ k ι Q = some ι') :
    ι < ι' ∧ Owns I σ k ι' Q ∧ ∀ j : Fin I, ι < j → Owns I σ k j Q → ι' ≤ j := by
  unfold nextOwner at hn
  by_cases hS : (Finset.univ.filter fun j : Fin I => ι < j ∧ Owns I σ k j Q).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hn
    subst hn
    have hm := Finset.min'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    refine ⟨hm.1, hm.2, fun j hj hjo => Finset.min'_le _ _ ?_⟩
    simp [hj, hjo]
  · rw [dif_neg hS] at hn
    exact absurd hn (by simp)

theorem prevOwner_spec {k : K} {ι ι' : Fin I} {Q : ℤ} (hp : prevOwner I σ k ι Q = some ι') :
    ι' < ι ∧ Owns I σ k ι' Q ∧ ∀ j : Fin I, j < ι → Owns I σ k j Q → j ≤ ι' := by
  unfold prevOwner at hp
  by_cases hS : (Finset.univ.filter fun j : Fin I => j < ι ∧ Owns I σ k j Q).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hp
    subst hp
    have hm := Finset.max'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    refine ⟨hm.1, hm.2, fun j hj hjo => Finset.le_max' _ _ ?_⟩
    simp [hj, hjo]
  · rw [dif_neg hS] at hp
    exact absurd hp (by simp)

/-- **Owner links are symmetric.** -/
theorem nextOwner_iff {k : K} {ι ι' : Fin I} {Q : ℤ} (hι : Owns I σ k ι Q) (hι' : Owns I σ k ι' Q) :
    nextOwner I σ k ι Q = some ι' ↔ prevOwner I σ k ι' Q = some ι := by
  constructor
  · intro hn
    obtain ⟨hlt, -, hmin⟩ := nextOwner_spec hn
    unfold prevOwner
    have hS : (Finset.univ.filter fun j : Fin I => j < ι' ∧ Owns I σ k j Q).Nonempty :=
      ⟨ι, by simp [hlt, hι]⟩
    rw [dif_pos hS, Option.some.injEq]
    apply le_antisymm
    · apply Finset.max'_le
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hc
      exact absurd hj.1 (not_lt.2 (hmin j (lt_of_not_ge hc) hj.2))
    · exact Finset.le_max' _ _ (by simp [hlt, hι])
  · intro hp
    obtain ⟨hlt, -, hmax⟩ := prevOwner_spec hp
    unfold nextOwner
    have hS : (Finset.univ.filter fun j : Fin I => ι < j ∧ Owns I σ k j Q).Nonempty :=
      ⟨ι', by simp [hlt, hι']⟩
    rw [dif_pos hS, Option.some.injEq]
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [hlt, hι'])
    · apply Finset.le_min'
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hc
      exact absurd hj.1 (not_lt.2 (hmax j (lt_of_not_ge hc) hj.2))

variable (I σ)

/-- Links between big intervals: owner links (slot `1` of the ports) and the state chain (slot `1` of `eIn`,
`eOut`). -/
def interMate (ι : Fin I) (l : Loc K h) (s : Fin 4) : Option (Fin I × Loc K h × Fin 4) :=
  match l with
  | .portOut k δ =>
    if s = 1 then (nextOwner I σ k ι (portQ I σ k ι δ)).map fun ι' =>
      (ι', .portIn k (portSlot I σ k ι' (portQ I σ k ι δ)), 1) else none
  | .portIn k δ =>
    if s = 1 then (prevOwner I σ k ι (portQ I σ k ι δ)).map fun ι' =>
      (ι', .portOut k (portSlot I σ k ι' (portQ I σ k ι δ)), 1) else none
  | .eOut => if s = 1 then (colSucc ι).map fun ι' => (ι', .eIn, 1) else none
  | .eIn => if s = 1 then (colPred ι).map fun ι' => (ι', .eOut, 1) else none
  | _ => none

theorem locMate_link (l : Loc K h) : locMate l 1 = none ∨ (∀ ι, interMate I σ ι l 1 = none) := by
  cases l <;> simp [locMate, interMate]

theorem interMate_symm {ι ι' : Fin I} {l l' : Loc K h} {s s' : Fin 4}
    (hm : interMate I σ ι l s = some (ι', l', s')) :
    interMate I σ ι' l' s' = some (ι, l, s) ∧ locMate l' s' = none := by
  cases l with
  | portOut k δ =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hn : nextOwner I σ k ι (portQ I σ k ι δ) with
      | none => rw [hn] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        obtain ⟨-, hown, -⟩ := nextOwner_spec hn
        refine ⟨?_, by simp [locMate]⟩
        simp only [interMate, ↓reduceIte, portQ_portSlot I σ hown]
        rw [(nextOwner_iff (owns_portQ I σ k ι δ) hown).1 hn]
        simp [portSlot_portQ]
    · simp [interMate, h1] at hm
  | portIn k δ =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hp : prevOwner I σ k ι (portQ I σ k ι δ) with
      | none => rw [hp] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        obtain ⟨-, hown, -⟩ := prevOwner_spec hp
        refine ⟨?_, by simp [locMate]⟩
        simp only [interMate, ↓reduceIte, portQ_portSlot I σ hown]
        rw [(nextOwner_iff hown (owns_portQ I σ k ι δ)).2 hp]
        simp [portSlot_portQ]
    · simp [interMate, h1] at hm
  | eOut =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hs : colSucc ι with
      | none => rw [hs] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        refine ⟨?_, by simp [locMate]⟩
        simp [interMate, colSucc_eq_some.1 hs]
    · simp [interMate, h1] at hm
  | eIn =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hp : colPred ι with
      | none => rw [hp] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        refine ⟨?_, by simp [locMate]⟩
        simp [interMate, colSucc_eq_some.2 hp]
    · simp [interMate, h1] at hm
  | tabC => simp [interMate] at hm
  | tabP c => simp [interMate] at hm
  | rt k c π => simp [interMate] at hm
  | st c π => simp [interMate] at hm

theorem interMate_ne {ι ι' : Fin I} {l l' : Loc K h} {s s' : Fin 4}
    (hm : interMate I σ ι l s = some (ι', l', s')) : ι' ≠ ι := by
  cases l with
  | portOut k δ =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hn : nextOwner I σ k ι (portQ I σ k ι δ) with
      | none => rw [hn] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        exact ne_of_gt (nextOwner_spec hn).1
    · simp [interMate, h1] at hm
  | portIn k δ =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hp : prevOwner I σ k ι (portQ I σ k ι δ) with
      | none => rw [hp] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        exact ne_of_lt (prevOwner_spec hp).1
    · simp [interMate, h1] at hm
  | eOut =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hs : colSucc ι with
      | none => rw [hs] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        exact colSucc_ne hs
    · simp [interMate, h1] at hm
  | eIn =>
    by_cases h1 : s = 1
    · subst h1
      simp only [interMate, ↓reduceIte] at hm
      cases hp : colPred ι with
      | none => rw [hp] at hm; exact absurd hm (by simp)
      | some j =>
        rw [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        exact colPred_ne hp
    · simp [interMate, h1] at hm
  | tabC => simp [interMate] at hm
  | tabP c => simp [interMate] at hm
  | rt k c π => simp [interMate] at hm
  | st c π => simp [interMate] at hm

/-- The half-edge partner in `N_{x,σ}`: the local mate, else the link to another big interval. -/
noncomputable def netMate (p : (Fin I × Loc K h) × Fin 4) : Option ((Fin I × Loc K h) × Fin 4) :=
  match locMate p.1.2 p.2 with
  | some q => some ((p.1.1, q.1), q.2)
  | none => (interMate I σ p.1.1 p.1.2 p.2).map fun r => ((r.1, r.2.1), r.2.2)

theorem netMate_symm {p q : (Fin I × Loc K h) × Fin 4} (hm : netMate I σ p = some q) :
    netMate I σ q = some p := by
  obtain ⟨⟨ι, l⟩, s⟩ := p
  obtain ⟨⟨ι', l'⟩, s'⟩ := q
  unfold netMate at hm ⊢
  simp only at hm ⊢
  cases hl : locMate l s with
  | some r =>
    rw [hl, Option.some.injEq] at hm
    obtain ⟨l₀, s₀⟩ := r
    simp only [Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    rw [locMate_symm hl]
  | none =>
    rw [hl] at hm
    cases hi : interMate I σ ι l s with
    | none => rw [hi] at hm; exact absurd hm (by simp)
    | some r =>
      rw [hi, Option.map_some, Option.some.injEq] at hm
      obtain ⟨ι₀, l₀, s₀⟩ := r
      simp only [Prod.mk.injEq] at hm
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
      obtain ⟨h1, h2⟩ := interMate_symm I σ hi
      rw [h2, h1]
      rfl

theorem netMate_ne {p q : (Fin I × Loc K h) × Fin 4} (hm : netMate I σ p = some q) : q.1 ≠ p.1 := by
  obtain ⟨⟨ι, l⟩, s⟩ := p
  obtain ⟨⟨ι', l'⟩, s'⟩ := q
  unfold netMate at hm
  simp only at hm ⊢
  cases hl : locMate l s with
  | some r =>
    rw [hl, Option.some.injEq] at hm
    obtain ⟨l₀, s₀⟩ := r
    simp only [Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
    intro e
    exact locMate_ne hl (congrArg Prod.snd e)
  | none =>
    rw [hl] at hm
    cases hi : interMate I σ ι l s with
    | none => rw [hi] at hm; exact absurd hm (by simp)
    | some r =>
      rw [hi, Option.map_some, Option.some.injEq] at hm
      obtain ⟨ι₀, l₀, s₀⟩ := r
      simp only [Prod.mk.injEq] at hm
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
      intro e
      exact interMate_ne I σ hi (congrArg Prod.fst e)

/-- The lane displacement contributed by the lower end of a routing cross arc. -/
def disp1 (p : (Fin I × Loc K h) × Fin 4) : BitWord h :=
  match p.1.2 with
  | .rt _ c _ => if p.2 = 1 then lnFlip 3 h c else 0
  | .st c _ => if p.2 = 1 then lnFlip 1 h c else 0
  | _ => 0

/-- The lane displacement of a half-edge (the same from both ends of an edge). -/
noncomputable def netDisp (p : (Fin I × Loc K h) × Fin 4) : BitWord h :=
  match netMate I σ p with
  | some q => disp1 I p + disp1 I q
  | none => 0

theorem netDisp_mate {p q : (Fin I × Loc K h) × Fin 4} (hm : netMate I σ p = some q) :
    netDisp I σ q = netDisp I σ p := by
  simp only [netDisp, hm, netMate_symm I σ hm, add_comm]

/-- **The pre-network of `N_{x,σ}`.** -/
noncomputable abbrev preGraph [NeZero I] : PreGraph h where
  V := Fin I × Loc K h
  vFintype := inferInstance
  vDecEq := inferInstance
  vNonempty := ⟨(0, .tabC)⟩
  vIndex := State.productIndex (Equiv.refl (Fin I)) (locEquiv K h)
  mate := netMate I σ
  mate_symm := fun _ _ hm => netMate_symm I σ hm
  mate_ne := fun _ _ hm => netMate_ne I σ hm
  disp := netDisp I σ
  disp_mate := fun _ _ hm => netDisp_mate I σ hm

/-- Payload width of a half-edge on its payload orientation (`Wc` content, `Ws` state, `Wt` table tuple). -/
def baseWidth (Wc Ws Wt : ℕ) (l : Loc K h) (s : Fin 4) : ℕ :=
  match l with
  | .tabC => if s = 0 then Wt else 0
  | .tabP c =>
    if s = 1 then Wt
    else if s = 2 then
      (match c with
        | .stOut => Ws
        | .cOut _ _ => Wc
        | _ => 0)
    else 0
  | .portIn _ _ => if s = 0 then Wc else 0
  | .portOut _ _ => if s = 1 then Wc else 0
  | .rt _ _ _ => if s = 0 ∨ s = 1 then Wc else 0
  | .st _ _ => if s = 0 ∨ s = 1 then Ws else 0
  | .eIn => if s = 0 then Ws else 0
  | .eOut => if s = 1 then Ws else 0

/-- Widths of `N_{x,σ}`: `0` on unmated half-edges. -/
noncomputable def netWidth (Wc Ws Wt : ℕ) (p : ((Fin I × Loc K h) × Fin 4) × BitWord h) : ℕ :=
  if netMate I σ p.1 = none then 0 else baseWidth Wc Ws Wt p.1.1.2 p.1.2

/-- **P3, the routed lane network** `N_{x,σ}` as an OpenAI compression state (degree `2^a ≥ 4`, `h` lane
bits). -/
noncomputable abbrev stateNet [NeZero I] {a : ℕ} (ha : 4 ≤ 2 ^ a) (Wc Ws Wt : ℕ) : State a h :=
  (preGraph (K := K) I σ).regularize ha (netWidth I σ Wc Ws Wt)

/-! ## The base order in closed form (computable address interface) -/

/-- The base order of the pre-network: `(ι, l) ↦ locNum l + locCount · ι` (big interval major). -/
theorem preGraph_vIndex_val [NeZero I] (ι : Fin I) (l : Loc K h) :
    ((preGraph (K := K) I σ).vIndex (ι, l) : ℕ) = locNum K h l + locCount K h * ι := by
  show ((finProdFinEquiv (ι, locEquiv K h l) : Fin (I * locCount K h)) : ℕ) = _
  rw [finProdFinEquiv_apply_val, locEquiv_val]

/-- **Base index of `N_{x,σ}`** in closed form: original `(ι, l, false) ↦ 2 (locNum l + locCount · ι)`, twin
`(ι, l, true) ↦` that `+ 1`. -/
theorem stateNet_baseIndex_val [NeZero I] {a : ℕ} (ha : 4 ≤ 2 ^ a) (Wc Ws Wt : ℕ) (ι : Fin I) (l : Loc K h)
    (t : Bool) :
    ((stateNet (K := K) I σ ha Wc Ws Wt).baseIndex ((ι, l), t) : ℕ) =
      (if t then 1 else 0) + 2 * (locNum K h l + locCount K h * ι) := by
  show ((finProdFinEquiv ((preGraph (K := K) I σ).vIndex (ι, l), finTwoEquiv.symm t) :
      Fin (Fintype.card (Fin I × Loc K h) * 2)) : ℕ) = _
  rw [finProdFinEquiv_apply_val, preGraph_vIndex_val]
  cases t <;> simp [finTwoEquiv]

/-- The number of base vertices of `N_{x,σ}`. -/
theorem card_stateNet_base [NeZero I] {a : ℕ} (ha : 4 ≤ 2 ^ a) (Wc Ws Wt : ℕ) :
    Fintype.card (stateNet (K := K) I σ ha Wc Ws Wt).Base = 2 * (I * locCount K h) := by
  have e : Fintype.card (stateNet (K := K) I σ ha Wc Ws Wt).Base = Fintype.card ((Fin I × Loc K h) × Bool) := rfl
  rw [e, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, card_loc, Fintype.card_bool]
  ring

end P1Net
