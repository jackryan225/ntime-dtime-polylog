import P1P5.EvalDefs
import P1P5.Cover

/-!
# P1, task P8a: size of the cone encoding

* Generic (any term chain): `dataSize_le_generic`: if every half-assignment set and every placed set
  on the chain has at most `A` elements (`ChainSiteLe c A`) and the occurrence count of `v` is at most
  `Q`, the cone data have size `≤ 4 A^3 (Q+1)^2 Q + length + A Q + A`.
* For `B.execute` (`encSize_le'`): `A = 2^((C + 2·2^{d₀}) M)` (OpenAI's records bound every recorded
  field by `M = C^T (W₀+1)` and every site by `C` fields; the slot records contain the new sites'
  half-fields: `slotRecords_newCovered`), `Q = C^T`, length `≤ (steps+1) T`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh

open scoped Classical

noncomputable section

section Lists

theorem enumL_length (α : Type) [Fintype α] : (enumL α).length = Fintype.card α := by
  simp [enumL, Finset.length_toList]

theorem sum_map_filter_list {α : Type} (l : List α) (p : α → Prop) (g : α → ℕ) :
    ((l.filter fun a => decide (p a)).map g).sum = (l.map fun a => if p a then g a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem sum_le_length_mul {α : Type} (l : List α) (f : α → ℕ) (b : ℕ) (h : ∀ a ∈ l, f a ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

end Lists

section Chain

variable {R : Type} [CommRing R]

theorem keysOf_length (N : Network) (S : N.Site → Prop) :
    (keysOf N S).length = ∑ u, if S u then Fintype.card (N.Half u) else 0 := by
  unfold keysOf
  rw [List.length_flatMap]
  simp only [List.length_map, enumL_length]
  rw [sum_map_filter_list]
  unfold enumL
  rw [Finset.sum_map_toList]

/-- Every half-assignment set and every placed set on the chain has at most `A` elements. -/
def ChainSiteLe {k : Type*} : {N Y : Network} → TermChain k N Y → ℕ → Prop
  | _, _, .done N, A => ∀ u, Fintype.card (N.Half u) ≤ A
  | _, _, @TermChain.more _ N _ t _ tail, A =>
      (∀ u, Fintype.card (N.Half u) ≤ A) ∧
        (∀ w, Fintype.card (Placed t.place N.Half w) ≤ A) ∧ ChainSiteLe tail A

theorem siteLe_cast {k : Type*} {N Y Z : Network} (h : N = Y) (c : TermChain k Y Z) (A : ℕ) :
    ChainSiteLe (h.symm ▸ c : TermChain k N Z) A ↔ ChainSiteLe c A := by
  subst h
  rfl

theorem siteLe_init {N Y : Network} (c : TermChain R N Y) {A : ℕ} (h : ChainSiteLe c A) (u : N.Site) :
    Fintype.card (N.Half u) ≤ A := by
  cases c with
  | done => exact h u
  | more => exact h.1 u

theorem siteLe_final : ∀ {N Y : Network} (c : TermChain R N Y) {A : ℕ}, ChainSiteLe c A →
    ∀ w : Y.Site, Fintype.card (Y.Half w) ≤ A := by
  intro N Y c
  induction c with
  | done => intro A h w; exact h w
  | more t recs tail ih => intro A h w; exact ih h.2.2 w

theorem encLevels_length : ∀ {N Y : Network} (c : TermChain R N Y) (v : Y.Site),
    (encLevels c v).length = c.length := by
  intro N Y c
  induction c with
  | done => intro v; rfl
  | more t recs tail ih => intro v; simp [encLevels, TermChain.length, ih v]

theorem sum_preimage {N : Network} (t : Term R N) (f : N.Site → ℕ) (w : t.output.Site) :
    ∑ u : t.Preimage w, f u.1 = ∑ u, if w = t.place u then f u else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun u => by simp) f).symm

/-- Regrouping a sum over old sites by their new sites. -/
theorem sum_regroup {N : Network} (t : Term R N) (P : t.output.Site → Prop) (f : N.Site → ℕ) :
    (∑ u, if P (t.place u) then f u else 0) =
      ∑ w, if P w then ∑ u : t.Preimage w, f u.1 else 0 := by
  have h1 : (∑ u, if P (t.place u) then f u else 0) =
      ∑ w, ∑ u, if w = t.place u then (if P (t.place u) then f u else 0) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_ite_eq']
    simp
  rw [h1]
  apply Finset.sum_congr rfl
  intro w _
  rw [sum_preimage]
  by_cases hw : P w
  · rw [if_pos hw]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : w = t.place u
    · subst h; simp [hw]
    · simp [h]
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro u _
    by_cases h : w = t.place u
    · subst h; simp [hw]
    · simp [h]

/-- The initial weights of the cone of `v` are part of its occurrence count. -/
theorem sum_cone_le : ∀ {N Y : Network} (c : TermChain R N Y) (init : N.Site → ℕ) (v : Y.Site),
    (∑ u, if toFinal c u = v then init u else 0) ≤ c.occurrences init v := by
  intro N Y c
  induction c with
  | done N =>
    intro init v
    show (∑ u, if u = v then init u else 0) ≤ init v
    simp
  | more t recs tail ih =>
    intro init v
    show (∑ u, if toFinal tail (t.place u) = v then init u else 0) ≤
      tail.occurrences (t.pushHistorySize recs init) v
    refine le_trans ?_ (ih _ v)
    rw [sum_regroup t (fun w => toFinal tail w = v) init]
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · unfold Term.pushHistorySize; omega
    · exact le_rfl

theorem pointers_size {N : Network} (t : Term R N) (S : N.Site → Prop) (w : t.output.Site)
    (x : Placed t.place N.Half w) :
    ((pointers t S w x).map fun i => i + 1).sum ≤
      Fintype.card (t.Preimage w) * ((keysOf N S).length + 1) := by
  unfold pointers
  rw [List.map_map]
  refine (sum_le_length_mul _ _ ((keysOf N S).length + 1) (fun u _ => ?_)).trans_eq ?_
  · simp only [Function.comp_apply]
    exact Nat.add_le_add_right (List.idxOf_le_length) 1
  · rw [enumL_length]

theorem entry_size {N : Network} (t : Term R N) (S : N.Site → Prop) (key : Key t.output) :
    ((levelEntry t S key).map fun p => 1 + (p.2.map fun i => i + 1).sum).sum + 1 ≤
      Fintype.card (Placed t.place N.Half key.1) *
        (1 + Fintype.card (t.Preimage key.1) * ((keysOf N S).length + 1)) + 1 := by
  apply Nat.add_le_add_right
  unfold levelEntry
  rw [List.map_map]
  refine (sum_le_length_mul _ _ (1 + Fintype.card (t.Preimage key.1) * ((keysOf N S).length + 1))
    (fun x _ => ?_)).trans_eq ?_
  · simp only [Function.comp_apply]
    exact Nat.add_le_add_left (pointers_size t S key.1 x) 1
  · rw [enumL_length]

/-- A level's size is bounded site by site on the new cone. -/
theorem levelSize_le {N : Network} (t : Term R N) (S : N.Site → Prop) (S' : t.output.Site → Prop) :
    levelSize (levelData t S S') ≤ ∑ w, if S' w then Fintype.card (t.output.Half w) *
      (Fintype.card (Placed t.place N.Half w) *
        (1 + Fintype.card (t.Preimage w) * ((keysOf N S).length + 1)) + 1) else 0 := by
  unfold levelSize levelData
  rw [List.map_map]
  conv_lhs => rw [keysOf]
  rw [List.map_flatMap, sum_flatMap', sum_map_filter_list]
  unfold enumL
  rw [Finset.sum_map_toList]
  apply Finset.sum_le_sum
  intro w _
  split_ifs
  · rw [List.map_map]
    refine (sum_le_length_mul _ _ (Fintype.card (Placed t.place N.Half w) *
        (1 + Fintype.card (t.Preimage w) * ((keysOf N S).length + 1)) + 1) (fun z _ => ?_)).trans_eq ?_
    · exact entry_size t S ⟨w, z⟩
    · rw [Finset.length_toList, Finset.card_univ]
  · exact le_rfl

/-- **Generic size bound of the levels.** `W = 4 A^3 (Q+1)^2` per cone site of every level. -/
theorem levels_size : ∀ {N Y : Network} (c : TermChain R N Y) (v : Y.Site) (A Q : ℕ), 1 ≤ A →
    ChainSiteLe c A → ∀ init : N.Site → ℕ, (∀ u, 1 ≤ init u) → c.occurrences init v ≤ Q →
    ((encLevels c v).map levelSize).sum +
        4 * A ^ 3 * (Q + 1) ^ 2 * (∑ u, if toFinal c u = v then init u else 0) ≤
      4 * A ^ 3 * (Q + 1) ^ 2 * Q := by
  intro N Y c
  induction c with
  | done N =>
    intro v A Q _ _ init _ hQ
    show 0 + 4 * A ^ 3 * (Q + 1) ^ 2 * (∑ u, if u = v then init u else 0) ≤ _
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.zero_add]
    exact Nat.mul_le_mul_left _ hQ
  | @more N0 Y0 t recs tail ih =>
    intro v A Q hA hS init hinit hQ
    obtain ⟨hHalf, hPlaced, hS'⟩ := hS
    set W := 4 * A ^ 3 * (Q + 1) ^ 2 with hW
    set init' := t.pushHistorySize recs init with hinit'
    have hQ' : tail.occurrences init' v ≤ Q := hQ
    have hinit'1 : ∀ w, 1 ≤ init' w := by
      intro w; simp only [hinit', Term.pushHistorySize, SiteRecords.count]; omega
    have hIH := ih v A Q hA hS' init' hinit'1 hQ'
    -- cone of the old network inside the occurrence count
    have hK : (∑ u, if toFinal tail (t.place u) = v then init u else 0) ≤ Q :=
      (sum_cone_le (TermChain.more t recs tail) init v).trans hQ
    have hL : (keysOf N0 fun u => toFinal tail (t.place u) = v).length ≤ A * Q := by
      rw [keysOf_length]
      refine le_trans ?_ (Nat.mul_le_mul_left A hK)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact (hHalf u).trans (Nat.le_mul_of_pos_right A (hinit u))
      · exact le_rfl
    have hK' : (∑ w, if toFinal tail w = v then init' w else 0) ≤ Q :=
      (sum_cone_le tail init' v).trans hQ'
    have hPre : ∀ w, toFinal tail w = v → Fintype.card (t.Preimage w) ≤ Q := by
      intro w hw
      refine le_trans ?_ hK'
      refine le_trans ?_ (Finset.single_le_sum (f := fun w => if toFinal tail w = v then init' w else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
      simp only [hw, if_true, hinit', Term.pushHistorySize]
      calc Fintype.card (t.Preimage w) = ∑ _u : t.Preimage w, 1 := by simp
        _ ≤ ∑ u : t.Preimage w, init u.1 := Finset.sum_le_sum (fun u _ => hinit u.1)
        _ ≤ _ := Nat.le_add_left _ _
    have hsite : ∀ w, toFinal tail w = v →
        Fintype.card (t.output.Half w) * (Fintype.card (Placed t.place N0.Half w) *
          (1 + Fintype.card (t.Preimage w) *
            ((keysOf N0 fun u => toFinal tail (t.place u) = v).length + 1)) + 1) ≤ W := by
      intro w hw
      have h1 := siteLe_init tail hS' w
      have h2 := hPlaced w
      have h3 := hPre w hw
      calc _ ≤ A * (A * (1 + Q * (A * Q + 1)) + 1) := by
            apply Nat.mul_le_mul h1
            apply Nat.add_le_add_right
            apply Nat.mul_le_mul h2
            apply Nat.add_le_add_left
            exact Nat.mul_le_mul h3 (Nat.add_le_add_right hL 1)
        _ ≤ W := by
            rw [hW]
            have hA2 : A ≤ A ^ 2 := by nlinarith
            have hA3 : A ^ 2 ≤ A ^ 3 := by nlinarith
            nlinarith [Nat.zero_le Q, Nat.zero_le A]
    have hlevel : levelSize (levelData t (fun u => toFinal tail (t.place u) = v)
        (fun w => toFinal tail w = v)) ≤ ∑ w, if toFinal tail w = v then W else 0 := by
      refine (levelSize_le t _ _).trans (Finset.sum_le_sum (fun w _ => ?_))
      split_ifs with hw
      · exact hsite w hw
      · exact le_rfl
    have hregroup := sum_regroup t (fun w => toFinal tail w = v) init
    show levelSize (levelData t (fun u => toFinal tail (t.place u) = v) (fun w => toFinal tail w = v)) +
        ((encLevels tail v).map levelSize).sum +
        W * (∑ u, if toFinal tail (t.place u) = v then init u else 0) ≤ W * Q
    have hcombine : (∑ w, if toFinal tail w = v then W else 0) +
        W * (∑ u, if toFinal tail (t.place u) = v then init u else 0) ≤
        W * (∑ w, if toFinal tail w = v then init' w else 0) := by
      rw [hregroup, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · simp only [hinit', Term.pushHistorySize, SiteRecords.count]
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega
      · simp
    rw [← hW] at hIH
    omega

/-- **Generic size bound of the whole input.** -/
theorem dataSize_le_generic {N Y : Network} (c : TermChain R N Y) (F : Factors R N) (v : Y.Site)
    (z : Y.Half v) (A Q : ℕ) (hA : 1 ≤ A) (hS : ChainSiteLe c A)
    (hQ : c.occurrences (fun _ => 1) v ≤ Q) :
    dataSize (encLevels c v) (stateOf N (fun u => toFinal c u = v) F) (finalIndex Y v z) ≤
      4 * A ^ 3 * (Q + 1) ^ 2 * Q + c.length + A * Q + A := by
  have h1 := levels_size c v A Q hA hS (fun _ => 1) (fun _ => le_rfl) hQ
  have hK : (∑ u, if toFinal c u = v then (fun _ => 1) u else 0) ≤ Q :=
    (sum_cone_le c (fun _ => 1) v).trans hQ
  have hst : (stateOf N (fun u => toFinal c u = v) F).length ≤ A * Q := by
    unfold stateOf
    rw [List.length_map, keysOf_length]
    refine le_trans ?_ (Nat.mul_le_mul_left A hK)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    split_ifs
    · simpa using siteLe_init c hS u
    · exact le_rfl
  have hi : finalIndex Y v z ≤ A := by
    unfold finalIndex
    refine List.idxOf_le_length.trans ?_
    rw [keysOf_length]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact siteLe_final c hS v
  unfold dataSize
  rw [encLevels_length]
  omega

end Chain

end

end P1P5
