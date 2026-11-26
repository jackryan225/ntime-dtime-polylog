import P1Net.StateGraph

/-!
# P3 (lane P1-lean-net, copy A): the access permutation of one big interval and one tape

Paper `subsec:network` (c). Items are pairs `(t, j)`: a type number `t < 8` and a lane number `j < N = 2^h`.
Sources: `t < 3` the incoming port `δ = t` (small block `(q - 1 + δ) N + j`), `3 ≤ t < 6` the content output of
window `δ = t - 3` of small interval `ιN + j`, `t ≥ 6` dummies. Destinations: `t < 3` the outgoing port `δ = t`,
`3 ≤ t < 6` the content input of window `δ = t - 3` of small interval `ιN + j`, `t ≥ 6` dummies.
`accNext` sends every source to the next access of its block in time order (first access for an incoming port;
the outgoing port after the last access); dummies to themselves. `accPrev` is its left inverse, so `accNext`
is a permutation (`accPerm`). The window blocks stay in the big blocks `q - 1, q, q + 1` (`window_in_owned`, the
skeleton-candidate form of `lem:own`).
-/

namespace P1Net

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {h : ℕ}

theorem betaOf_succ_bound {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i : ℕ) :
    -1 ≤ betaOf σ k (i + 1) - betaOf σ k i ∧ betaOf σ k (i + 1) - betaOf σ k i ≤ 1 := by
  simp only [betaOf]
  split_ifs with hi
  · have := (σ ⟨i, hi⟩ k).isLt
    constructor <;> omega
  · constructor <;> omega

theorem betaOf_drift {n : ℕ} (σ : Fin n → K → Fin 3) (k : K) (i g : ℕ) :
    betaOf σ k i - g ≤ betaOf σ k (i + g) ∧ betaOf σ k (i + g) ≤ betaOf σ k i + g := by
  induction g with
  | zero => simp
  | succ g ih =>
    have := betaOf_succ_bound σ k (i + g)
    rw [show i + (g + 1) = i + g + 1 by ring]
    push_cast
    constructor <;> omega

variable (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

/-- The small block of head `k` at the start of lane `j` of big interval `ι`. -/
def laneBeta (j : ℕ) : ℤ := betaOf σ k (ι * 2 ^ h + j)

/-- Lane `j` accesses block `Z`. -/
def Acc (j : Fin (2 ^ h)) (Z : ℤ) : Prop := InWindow (laneBeta I σ ι k j) Z

instance (j : Fin (2 ^ h)) (Z : ℤ) : Decidable (Acc I σ ι k j Z) := by
  unfold Acc; infer_instance

/-- **`lem:own` for a skeleton candidate.** The window blocks of every lane lie in the big blocks
`q - 1, q, q + 1`. -/
theorem window_in_owned (j : Fin (2 ^ h)) {Z : ℤ} (hZ : Acc I σ ι k j Z) :
    (bigQ I σ k ι - 1) * 2 ^ h ≤ Z ∧ Z < (bigQ I σ k ι + 2) * 2 ^ h := by
  have hN : (0 : ℤ) < 2 ^ h := by positivity
  have hd := betaOf_drift σ k (ι * 2 ^ h) j
  have hj : ((j : ℕ) : ℤ) + 1 ≤ 2 ^ h := by
    have := j.isLt
    exact_mod_cast this
  unfold Acc laneBeta InWindow at hZ
  unfold bigQ
  set b0 := betaOf σ k (ι * 2 ^ h)
  have hNc : ((2 ^ h : ℕ) : ℤ) = 2 ^ h := by push_cast; rfl
  rw [hNc]
  have a1 := ediv_mul_le' b0 hN
  have a2 := lt_ediv_mul_add' b0 hN
  constructor <;> nlinarith

/-- The small block of port `δ` at lane `j`. -/
def portBlock (δ : ℕ) (j : ℕ) : ℤ := (bigQ I σ k ι - 1 + δ) * 2 ^ h + j

/-- The port type of a block of the owned big blocks. -/
def portType (Z : ℤ) : ℕ := (Z / 2 ^ h - bigQ I σ k ι + 1).toNat

/-- The lane of a block inside its big block. -/
def portLane (h : ℕ) (Z : ℤ) : Fin (2 ^ h) :=
  ⟨(Z % 2 ^ h).toNat, by
    have hN : (0 : ℤ) < 2 ^ h := by positivity
    have := Int.emod_lt_of_pos Z hN
    have := Int.emod_nonneg Z hN.ne'
    have h2 : ((2 ^ h : ℕ) : ℤ) = 2 ^ h := by push_cast; rfl
    omega⟩

theorem portBlock_type_lane (δ : ℕ) (hδ : δ < 3) (j : Fin (2 ^ h)) :
    portType I σ ι k (portBlock I σ ι k δ j) = δ ∧ portLane h (portBlock I σ ι k δ j) = j := by
  have hN : (0 : ℤ) < 2 ^ h := by positivity
  have hj : ((j : ℕ) : ℤ) < 2 ^ h := by have := j.isLt; exact_mod_cast this
  have hdiv : portBlock I σ ι k δ j / 2 ^ h = bigQ I σ k ι - 1 + δ := by
    unfold portBlock
    apply ediv_eq_of_bounds hN <;> nlinarith
  have hmod : portBlock I σ ι k δ j % 2 ^ h = j := by
    unfold portBlock
    rw [add_comm, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by positivity) hj
  constructor
  · unfold portType
    rw [hdiv]
    omega
  · apply Fin.ext
    simp only [portLane, hmod]
    simp

theorem portBlock_of_owned {Z : ℤ} (h1 : (bigQ I σ k ι - 1) * 2 ^ h ≤ Z)
    (h2 : Z < (bigQ I σ k ι + 2) * 2 ^ h) :
    portType I σ ι k Z < 3 ∧ portBlock I σ ι k (portType I σ ι k Z) (portLane h Z) = Z := by
  have hN : (0 : ℤ) < 2 ^ h := by positivity
  have a1 := ediv_mul_le' Z hN
  have a2 := lt_ediv_mul_add' Z hN
  have hq1 : bigQ I σ k ι - 1 ≤ Z / 2 ^ h := by
    by_contra hc
    have : Z / 2 ^ h + 1 ≤ bigQ I σ k ι - 1 := by omega
    nlinarith
  have hq2 : Z / 2 ^ h ≤ bigQ I σ k ι + 1 := by
    by_contra hc
    have : bigQ I σ k ι + 2 ≤ Z / 2 ^ h := by omega
    nlinarith
  have ht : ((portType I σ ι k Z : ℕ) : ℤ) = Z / 2 ^ h - bigQ I σ k ι + 1 := by
    unfold portType
    rw [Int.toNat_of_nonneg (by omega)]
  have hl : (((portLane h Z : Fin (2 ^ h)) : ℕ) : ℤ) = Z % 2 ^ h := by
    simp only [portLane]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg Z hN.ne')]
  constructor
  · omega
  · unfold portBlock
    rw [ht, hl]
    have := Int.ediv_mul_add_emod Z (2 ^ h)
    linarith

/-- The window slot of block `Z` at lane `j`. -/
def slotAt (j : Fin (2 ^ h)) (Z : ℤ) : ℕ := (Z - laneBeta I σ ι k j + 1).toNat

theorem slotAt_lt {j : Fin (2 ^ h)} {Z : ℤ} (hZ : Acc I σ ι k j Z) : slotAt I σ ι k j Z < 3 := by
  unfold Acc InWindow at hZ
  unfold slotAt
  omega

theorem slotAt_block {j : Fin (2 ^ h)} {Z : ℤ} (hZ : Acc I σ ι k j Z) :
    laneBeta I σ ι k j - 1 + (slotAt I σ ι k j Z : ℤ) = Z := by
  unfold Acc InWindow at hZ
  unfold slotAt
  rw [Int.toNat_of_nonneg (by omega)]
  ring

theorem slotAt_slot (j : Fin (2 ^ h)) (δ : ℕ) (hδ : δ < 3) :
    slotAt I σ ι k j (laneBeta I σ ι k j - 1 + δ) = δ := by
  unfold slotAt
  rw [show laneBeta I σ ι k j - 1 + (δ : ℤ) - laneBeta I σ ι k j + 1 = (δ : ℤ) by ring]
  simp

theorem acc_slot (j : Fin (2 ^ h)) (δ : ℕ) (hδ : δ < 3) :
    Acc I σ ι k j (laneBeta I σ ι k j - 1 + δ) := by
  unfold Acc InWindow
  constructor <;> omega

/-! ## First, last, next and previous accesses -/

/-- The first lane accessing `Z`. -/
def firstAcc (Z : ℤ) : Option (Fin (2 ^ h)) :=
  if hS : (Finset.univ.filter fun j => Acc I σ ι k j Z).Nonempty then
    some ((Finset.univ.filter fun j => Acc I σ ι k j Z).min' hS) else none

/-- The last lane accessing `Z`. -/
def lastAcc (Z : ℤ) : Option (Fin (2 ^ h)) :=
  if hS : (Finset.univ.filter fun j => Acc I σ ι k j Z).Nonempty then
    some ((Finset.univ.filter fun j => Acc I σ ι k j Z).max' hS) else none

/-- The next lane after `j` accessing `Z`. -/
def nextAcc (Z : ℤ) (j : Fin (2 ^ h)) : Option (Fin (2 ^ h)) :=
  if hS : (Finset.univ.filter fun j' => j < j' ∧ Acc I σ ι k j' Z).Nonempty then
    some ((Finset.univ.filter fun j' => j < j' ∧ Acc I σ ι k j' Z).min' hS) else none

/-- The previous lane before `j` accessing `Z`. -/
def prevAcc (Z : ℤ) (j : Fin (2 ^ h)) : Option (Fin (2 ^ h)) :=
  if hS : (Finset.univ.filter fun j' => j' < j ∧ Acc I σ ι k j' Z).Nonempty then
    some ((Finset.univ.filter fun j' => j' < j ∧ Acc I σ ι k j' Z).max' hS) else none

variable {I σ ι k}

theorem firstAcc_spec {Z : ℤ} {j : Fin (2 ^ h)} (hf : firstAcc I σ ι k Z = some j) :
    Acc I σ ι k j Z ∧ ∀ j', Acc I σ ι k j' Z → j ≤ j' := by
  unfold firstAcc at hf
  by_cases hS : (Finset.univ.filter fun j => Acc I σ ι k j Z).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hf
    subst hf
    have hm := Finset.min'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact ⟨hm, fun j' hj' => Finset.min'_le _ _ (by simp [hj'])⟩
  · rw [dif_neg hS] at hf; exact absurd hf (by simp)

theorem firstAcc_none {Z : ℤ} (hf : firstAcc I σ ι k Z = none) (j : Fin (2 ^ h)) :
    ¬ Acc I σ ι k j Z := by
  intro hj
  unfold firstAcc at hf
  rw [dif_pos ⟨j, by simp [hj]⟩] at hf
  exact absurd hf (by simp)

theorem lastAcc_spec {Z : ℤ} {j : Fin (2 ^ h)} (hf : lastAcc I σ ι k Z = some j) :
    Acc I σ ι k j Z ∧ ∀ j', Acc I σ ι k j' Z → j' ≤ j := by
  unfold lastAcc at hf
  by_cases hS : (Finset.univ.filter fun j => Acc I σ ι k j Z).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hf
    subst hf
    have hm := Finset.max'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact ⟨hm, fun j' hj' => Finset.le_max' _ _ (by simp [hj'])⟩
  · rw [dif_neg hS] at hf; exact absurd hf (by simp)

theorem lastAcc_none {Z : ℤ} (hf : lastAcc I σ ι k Z = none) (j : Fin (2 ^ h)) :
    ¬ Acc I σ ι k j Z := by
  intro hj
  unfold lastAcc at hf
  rw [dif_pos ⟨j, by simp [hj]⟩] at hf
  exact absurd hf (by simp)

theorem nextAcc_spec {Z : ℤ} {j j' : Fin (2 ^ h)} (hn : nextAcc I σ ι k Z j = some j') :
    j < j' ∧ Acc I σ ι k j' Z ∧ ∀ j'', j < j'' → Acc I σ ι k j'' Z → j' ≤ j'' := by
  unfold nextAcc at hn
  by_cases hS : (Finset.univ.filter fun j' => j < j' ∧ Acc I σ ι k j' Z).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hn
    subst hn
    have hm := Finset.min'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact ⟨hm.1, hm.2, fun j'' h1 h2 => Finset.min'_le _ _ (by simp [h1, h2])⟩
  · rw [dif_neg hS] at hn; exact absurd hn (by simp)

theorem nextAcc_none {Z : ℤ} {j : Fin (2 ^ h)} (hn : nextAcc I σ ι k Z j = none) (j' : Fin (2 ^ h))
    (hj : j < j') : ¬ Acc I σ ι k j' Z := by
  intro hj'
  unfold nextAcc at hn
  rw [dif_pos ⟨j', by simp [hj, hj']⟩] at hn
  exact absurd hn (by simp)

theorem prevAcc_spec {Z : ℤ} {j j' : Fin (2 ^ h)} (hp : prevAcc I σ ι k Z j = some j') :
    j' < j ∧ Acc I σ ι k j' Z ∧ ∀ j'', j'' < j → Acc I σ ι k j'' Z → j'' ≤ j' := by
  unfold prevAcc at hp
  by_cases hS : (Finset.univ.filter fun j' => j' < j ∧ Acc I σ ι k j' Z).Nonempty
  · rw [dif_pos hS, Option.some.injEq] at hp
    subst hp
    have hm := Finset.max'_mem _ hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact ⟨hm.1, hm.2, fun j'' h1 h2 => Finset.le_max' _ _ (by simp [h1, h2])⟩
  · rw [dif_neg hS] at hp; exact absurd hp (by simp)

theorem prevAcc_none {Z : ℤ} {j : Fin (2 ^ h)} (hp : prevAcc I σ ι k Z j = none) (j' : Fin (2 ^ h))
    (hj : j' < j) : ¬ Acc I σ ι k j' Z := by
  intro hj'
  unfold prevAcc at hp
  rw [dif_pos ⟨j', by simp [hj, hj']⟩] at hp
  exact absurd hp (by simp)

/-- The previous access of the next access is the access itself. -/
theorem prevAcc_nextAcc {Z : ℤ} {j j' : Fin (2 ^ h)} (hj : Acc I σ ι k j Z)
    (hn : nextAcc I σ ι k Z j = some j') : prevAcc I σ ι k Z j' = some j := by
  obtain ⟨hlt, -, hmin⟩ := nextAcc_spec hn
  unfold prevAcc
  have hS : (Finset.univ.filter fun j'' => j'' < j' ∧ Acc I σ ι k j'' Z).Nonempty :=
    ⟨j, by simp [hlt, hj]⟩
  rw [dif_pos hS, Option.some.injEq]
  apply le_antisymm
  · apply Finset.max'_le
    intro j'' hj''
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj''
    by_contra hc
    exact absurd hj''.1 (not_lt.2 (hmin j'' (lt_of_not_ge hc) hj''.2))
  · exact Finset.le_max' _ _ (by simp [hlt, hj])

/-- With no previous access, the first access is the lane itself. -/
theorem prevAcc_firstAcc {Z : ℤ} {j : Fin (2 ^ h)} (hf : firstAcc I σ ι k Z = some j) :
    prevAcc I σ ι k Z j = none := by
  obtain ⟨-, hmin⟩ := firstAcc_spec hf
  unfold prevAcc
  rw [dif_neg]
  rintro ⟨j', hj'⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
  exact absurd hj'.1 (not_lt.2 (hmin j' hj'.2))

/-- With no next access, the lane is the last access. -/
theorem lastAcc_of_nextAcc_none {Z : ℤ} {j : Fin (2 ^ h)} (hj : Acc I σ ι k j Z)
    (hn : nextAcc I σ ι k Z j = none) : lastAcc I σ ι k Z = some j := by
  unfold lastAcc
  have hS : (Finset.univ.filter fun j' => Acc I σ ι k j' Z).Nonempty := ⟨j, by simp [hj]⟩
  rw [dif_pos hS, Option.some.injEq]
  apply le_antisymm
  · apply Finset.max'_le
    intro j' hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    by_contra hc
    exact nextAcc_none hn j' (lt_of_not_ge hc) hj'
  · exact Finset.le_max' _ _ (by simp [hj])

/-! ## The access permutation -/

/-- A type number. -/
def typ (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by norm_num)⟩

theorem typ_val {n : ℕ} (hn : n < 8) : ((typ n : Fin 8) : ℕ) = n := Nat.mod_eq_of_lt hn

variable (I σ ι k)

/-- The block of an item: incoming/outgoing port `t` at lane `j`, or window `t - 3` of lane `j`. -/
def itemBlock (t : ℕ) (j : Fin (2 ^ h)) : ℤ :=
  if t < 3 then portBlock I σ ι k t j else laneBeta I σ ι k j - 1 + (t - 3 : ℕ)

/-- Next access: sources to destinations. -/
def accNext (x : Fin 8 × Fin (2 ^ h)) : Fin 8 × Fin (2 ^ h) :=
  if (x.1 : ℕ) < 3 then
    match firstAcc I σ ι k (itemBlock I σ ι k x.1 x.2) with
    | some j' => (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k x.1 x.2)), j')
    | none => x
  else if (x.1 : ℕ) < 6 then
    match nextAcc I σ ι k (itemBlock I σ ι k x.1 x.2) x.2 with
    | some j' => (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k x.1 x.2)), j')
    | none => (typ (portType I σ ι k (itemBlock I σ ι k x.1 x.2)),
        portLane h (itemBlock I σ ι k x.1 x.2))
  else x

/-- Previous access: destinations to sources (the inverse of `accNext`). -/
def accPrev (y : Fin 8 × Fin (2 ^ h)) : Fin 8 × Fin (2 ^ h) :=
  if (y.1 : ℕ) < 3 then
    match lastAcc I σ ι k (itemBlock I σ ι k y.1 y.2) with
    | some j' => (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k y.1 y.2)), j')
    | none => y
  else if (y.1 : ℕ) < 6 then
    match prevAcc I σ ι k (itemBlock I σ ι k y.1 y.2) y.2 with
    | some j' => (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k y.1 y.2)), j')
    | none => (typ (portType I σ ι k (itemBlock I σ ι k y.1 y.2)),
        portLane h (itemBlock I σ ι k y.1 y.2))
  else y

theorem itemBlock_window {j' : Fin (2 ^ h)} {Z : ℤ} (hZ : Acc I σ ι k j' Z) :
    itemBlock I σ ι k (3 + slotAt I σ ι k j' Z) j' = Z := by
  unfold itemBlock
  rw [if_neg (show ¬ (3 + slotAt I σ ι k j' Z < 3) by omega),
    show 3 + slotAt I σ ι k j' Z - 3 = slotAt I σ ι k j' Z by omega]
  exact slotAt_block I σ ι k hZ

theorem itemBlock_port {Z : ℤ} (h1 : (bigQ I σ k ι - 1) * 2 ^ h ≤ Z)
    (h2 : Z < (bigQ I σ k ι + 2) * 2 ^ h) :
    itemBlock I σ ι k (portType I σ ι k Z) (portLane h Z) = Z := by
  obtain ⟨hlt, hb⟩ := portBlock_of_owned I σ ι k h1 h2
  unfold itemBlock
  rw [if_pos hlt]
  exact hb

/-- `accPrev` at a table input. -/
theorem accPrev_window {j' : Fin (2 ^ h)} {Z : ℤ} (hacc : Acc I σ ι k j' Z) :
    accPrev I σ ι k (typ (3 + slotAt I σ ι k j' Z), j') =
      match prevAcc I σ ι k Z j' with
      | some j'' => (typ (3 + slotAt I σ ι k j'' Z), j'')
      | none => (typ (portType I σ ι k Z), portLane h Z) := by
  have hs := slotAt_lt I σ ι k hacc
  have hv : ((typ (3 + slotAt I σ ι k j' Z) : Fin 8) : ℕ) = 3 + slotAt I σ ι k j' Z := typ_val (by omega)
  unfold accPrev
  simp only [hv]
  rw [if_neg (show ¬ (3 + slotAt I σ ι k j' Z < 3) by omega),
    if_pos (show 3 + slotAt I σ ι k j' Z < 6 by omega), itemBlock_window I σ ι k hacc]

/-- `accPrev` at an outgoing port. -/
theorem accPrev_port {Z : ℤ} (h1 : (bigQ I σ k ι - 1) * 2 ^ h ≤ Z)
    (h2 : Z < (bigQ I σ k ι + 2) * 2 ^ h) :
    accPrev I σ ι k (typ (portType I σ ι k Z), portLane h Z) =
      match lastAcc I σ ι k Z with
      | some j' => (typ (3 + slotAt I σ ι k j' Z), j')
      | none => (typ (portType I σ ι k Z), portLane h Z) := by
  obtain ⟨hlt, -⟩ := portBlock_of_owned I σ ι k h1 h2
  have hv : ((typ (portType I σ ι k Z) : Fin 8) : ℕ) = portType I σ ι k Z := typ_val (by omega)
  unfold accPrev
  simp only [hv]
  rw [if_pos hlt, itemBlock_port I σ ι k h1 h2]

theorem typ_window_eq (t : Fin 8) (h3 : ¬ (t : ℕ) < 3) (h6 : (t : ℕ) < 6) : typ (3 + ((t : ℕ) - 3)) = t := by
  apply Fin.ext
  rw [typ_val (by omega)]
  omega

/-- **`accPrev` inverts `accNext`.** -/
theorem accPrev_accNext (x : Fin 8 × Fin (2 ^ h)) : accPrev I σ ι k (accNext I σ ι k x) = x := by
  obtain ⟨t, j⟩ := x
  by_cases h3 : (t : ℕ) < 3
  · have hib : itemBlock I σ ι k t j = portBlock I σ ι k t j := by simp [itemBlock, h3]
    cases hf : firstAcc I σ ι k (itemBlock I σ ι k t j) with
    | some j' =>
      obtain ⟨hacc, -⟩ := firstAcc_spec hf
      have hnext : accNext I σ ι k (t, j) =
          (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k t j)), j') := by
        simp only [accNext, if_pos h3, hf]
      rw [hnext, accPrev_window I σ ι k hacc, prevAcc_firstAcc hf]
      have hown := window_in_owned I σ ι k j' hacc
      have hpt := portBlock_type_lane I σ ι k t h3 j
      simp only [hib] at hpt ⊢
      rw [hpt.1, hpt.2]
      simp only [Prod.mk.injEq, and_true]
      exact Fin.ext (typ_val (by omega))
    | none =>
      have hnext : accNext I σ ι k (t, j) = (t, j) := by simp only [accNext, if_pos h3, hf]
      rw [hnext]
      have hl : lastAcc I σ ι k (itemBlock I σ ι k t j) = none := by
        unfold lastAcc
        rw [dif_neg]
        rintro ⟨j', hj'⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        exact firstAcc_none hf j' hj'
      simp only [accPrev, if_pos h3, hl]
  · by_cases h6 : (t : ℕ) < 6
    · have hacc0 : Acc I σ ι k j (itemBlock I σ ι k t j) := by
        unfold itemBlock
        rw [if_neg h3]
        exact acc_slot I σ ι k j (t - 3) (by omega)
      have hsl : slotAt I σ ι k j (itemBlock I σ ι k t j) = t - 3 := by
        unfold itemBlock
        rw [if_neg h3]
        exact slotAt_slot I σ ι k j (t - 3) (by omega)
      cases hn : nextAcc I σ ι k (itemBlock I σ ι k t j) j with
      | some j' =>
        obtain ⟨-, hacc, -⟩ := nextAcc_spec hn
        have hnext : accNext I σ ι k (t, j) =
            (typ (3 + slotAt I σ ι k j' (itemBlock I σ ι k t j)), j') := by
          simp only [accNext, if_neg h3, if_pos h6, hn]
        rw [hnext, accPrev_window I σ ι k hacc, prevAcc_nextAcc hacc0 hn]
        simp only [hsl, Prod.mk.injEq, and_true]
        exact typ_window_eq t h3 h6
      | none =>
        have hown := window_in_owned I σ ι k j hacc0
        have hnext : accNext I σ ι k (t, j) = (typ (portType I σ ι k (itemBlock I σ ι k t j)),
            portLane h (itemBlock I σ ι k t j)) := by
          simp only [accNext, if_neg h3, if_pos h6, hn]
        rw [hnext, accPrev_port I σ ι k hown.1 hown.2, lastAcc_of_nextAcc_none hacc0 hn]
        simp only [hsl, Prod.mk.injEq, and_true]
        exact typ_window_eq t h3 h6
    · have hnext : accNext I σ ι k (t, j) = (t, j) := by simp only [accNext, if_neg h3, if_neg h6]
      rw [hnext]
      simp only [accPrev, if_neg h3, if_neg h6]

theorem accNext_injective : Function.Injective (accNext I σ ι k) :=
  Function.LeftInverse.injective (accPrev_accNext I σ ι k)

/-- **The access permutation** of big interval `ι` and tape `k`. -/
noncomputable def accPerm : Equiv.Perm (Fin 8 × Fin (2 ^ h)) :=
  Equiv.ofBijective (accNext I σ ι k)
    ⟨accNext_injective I σ ι k, Finite.injective_iff_surjective.1 (accNext_injective I σ ι k)⟩

theorem accPerm_apply (x : Fin 8 × Fin (2 ^ h)) : accPerm I σ ι k x = accNext I σ ι k x := rfl

end P1Net
