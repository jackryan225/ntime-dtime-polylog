import P1Benes.Settings

/-!
# P1Benes.Tab: the canonical settings computed on tables (lane P1-lean-benes, level-0 factor-table program, part (a))

G3-chief (board 11:13Z): benes owns the level-0 factor-table program: (a) `settingsTab` with `settingsTab_eq`,
(b) a `Prog` for the switch bits of all stages (cost `c m N^3`), (c) the `Prog` for the level-0 factor table of one
site of `rnState`.

This file is part (a). A permutation `π` of `Fin N` is given by its TABLE `tabOf π = [π 0, …, π (N-1)]` (natural
numbers) and the table of `π⁻¹`. On tables, one level of the looping rule is:
* `flipT x` = `x` with its lowest bit flipped (the partner at the same input switch, `Net.flip0`);
* `rhoT P Q x = Q[flipT (P[flipT x])]` (one step `ρ = τ ∘ σ` along a cycle of the constraint graph);
* `iterMin f k y = min_{i ≤ k} f^[i] y`, so `iterMin (rhoT P Q) N y` is the least label of the `ρ`-orbit of `y`
  (`orbMin_val`; every orbit has fewer than `N` elements);
* `colT P Q x = (least label of the orbit of flipT x) < (least label of the orbit of x)` (`Loop.colour`);
* first stage `firstT P Q l = colT (2l)`, last stage `lastT P Q l = colT (Q[2l])`, the half tables
  `subT P Q b`, `subInvT P Q b` (`Net.sub`).
`settingsTab n P Q : Net.Settings n` recurses on the half tables; `settingsTab_eq`:
`settingsTab n (tabOf π) (tabOf π⁻¹) = Net.settings n π`. Every step is a loop over a table, so the cost is
`O(N^2)` table look-ups per level (`O(N^3)` steps with look-ups by scanning), the model of part (b).
-/

namespace P1Benes.Tab

open Equiv Equiv.Perm P1Benes.Net

/-! ## Table operations -/

/-- Flip the lowest bit of a number. -/
def flipT (x : ℕ) : ℕ := if x % 2 = 1 then x - 1 else x + 1

/-- One step `ρ = τ ∘ σ` along a cycle, on tables `P = π`, `Q = π⁻¹`. -/
def rhoT (P Q : List ℕ) (x : ℕ) : ℕ := Q.getD (flipT (P.getD (flipT x) 0)) 0

/-- `iterMin f k y = min_{i ≤ k} f^[i] y`. -/
def iterMin (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, y => y
  | k + 1, y => min y (iterMin f k (f y))

/-- The canonical colour on tables (`Loop.colour`). -/
def colT (P Q : List ℕ) (x : ℕ) : Bool :=
  decide (iterMin (rhoT P Q) P.length (flipT x) < iterMin (rhoT P Q) P.length x)

/-- First-stage setting of the switch `l` (`Net.firstOf`). -/
def firstT (P Q : List ℕ) (l : ℕ) : Bool := colT P Q (2 * l)

/-- Last-stage setting of the switch `l` (`Net.lastOf`). -/
def lastT (P Q : List ℕ) (l : ℕ) : Bool := colT P Q (Q.getD (2 * l) 0)

/-- The table of the induced permutation of the half `b` (`Net.sub`). -/
def subT (P Q : List ℕ) (b : Bool) : List ℕ :=
  (List.range (P.length / 2)).map fun l =>
    P.getD (2 * l + if xor (firstT P Q l) b then 1 else 0) 0 / 2

/-- The table of its inverse. -/
def subInvT (P Q : List ℕ) (b : Bool) : List ℕ :=
  (List.range (P.length / 2)).map fun l =>
    Q.getD (2 * l + if xor (lastT P Q l) b then 1 else 0) 0 / 2

/-- **The canonical settings computed on tables.** -/
def settingsTab : (n : ℕ) → List ℕ → List ℕ → Net.Settings n
  | 0, P, _ => .leaf (decide (P.getD 0 0 % 2 = 1))
  | n + 1, P, Q =>
    .node (fun l => firstT P Q l.val) (fun b => settingsTab n (subT P Q b) (subInvT P Q b))
      (fun l => lastT P Q l.val)

/-- The table of a permutation. -/
def tabOf {N : ℕ} (π : Perm (Fin N)) : List ℕ := List.ofFn fun x => (π x).val

/-! ## Tables of permutations -/

theorem tabOf_length {N : ℕ} (π : Perm (Fin N)) : (tabOf π).length = N := List.length_ofFn

theorem tabOf_getD {N : ℕ} (π : Perm (Fin N)) (x : Fin N) : (tabOf π).getD x.val 0 = (π x).val := by
  simp [tabOf, List.getD_eq_getElem?_getD]

theorem tabOf_getD' {N : ℕ} (π : Perm (Fin N)) (x : Fin N) (v : ℕ) (hv : x.val = v) :
    (tabOf π).getD v 0 = (π x).val := by
  subst hv
  exact tabOf_getD π x

variable {n : ℕ}

theorem flipT_val (x : Fin (2 ^ (n + 1))) : flipT x.val = (flip0 n x).val := by
  show _ = 2 * (x.val / 2) + (if xor (decide (x.val % 2 = 1)) true then 1 else 0)
  unfold flipT
  by_cases hx : x.val % 2 = 1
  · simp [hx] <;> omega
  · simp [hx] <;> omega

theorem rhoT_val (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    rhoT (tabOf π) (tabOf π.symm) x.val = (Loop.rho (flip0 n) (tau π) x).val := by
  unfold rhoT
  rw [flipT_val, tabOf_getD, flipT_val, tabOf_getD]
  rfl

theorem iter_val (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    ∀ i : ℕ, (rhoT (tabOf π) (tabOf π.symm))^[i] x.val = ((Loop.rho (flip0 n) (tau π) ^ i) x).val
  | 0 => rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply', iter_val π x i, rhoT_val, pow_succ' (Loop.rho (flip0 n) (tau π)) i,
      Perm.mul_apply]

/-! ## Minima along iterates -/

theorem iterMin_le (f : ℕ → ℕ) : ∀ (k y i : ℕ), i ≤ k → iterMin f k y ≤ f^[i] y
  | 0, y, i, hi => by
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | k + 1, y, 0, _ => min_le_left _ _
  | k + 1, y, i + 1, hi => by
    rw [Function.iterate_succ_apply]
    exact (min_le_right _ _).trans (iterMin_le f k (f y) i (by omega))

theorem iterMin_mem (f : ℕ → ℕ) : ∀ (k y : ℕ), ∃ i ≤ k, iterMin f k y = f^[i] y
  | 0, y => ⟨0, le_rfl, rfl⟩
  | k + 1, y => by
    obtain ⟨i, hi, e⟩ := iterMin_mem f k (f y)
    by_cases hy : y ≤ iterMin f k (f y)
    · exact ⟨0, Nat.zero_le _, min_eq_left hy⟩
    · refine ⟨i + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply]
      show min y (iterMin f k (f y)) = _
      rw [min_eq_right (by omega), e]

/-- Every element of the cycle of `x` is reached in fewer than `card α` steps. -/
theorem exists_pow_lt_card {α : Type*} [Fintype α] [DecidableEq α] {f : Perm α} {x y : α}
    (h : f.SameCycle x y) : ∃ i < Fintype.card α, (f ^ i) x = y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨i, hi, e⟩ := h.exists_pow_eq_of_mem_support hx
    exact ⟨i, lt_of_lt_of_le hi (Finset.card_le_univ _), e⟩
  · rw [Equiv.Perm.notMem_support] at hx
    refine ⟨0, Fintype.card_pos_iff.2 ⟨x⟩, ?_⟩
    rw [pow_zero, Perm.one_apply]
    exact h.eq_of_left hx

/-- The least label of an orbit, on tables. -/
theorem orbMin_val (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    (Loop.orbMin (Loop.rho (flip0 n) (tau π)) x).val =
      iterMin (rhoT (tabOf π) (tabOf π.symm)) (2 ^ (n + 1)) x.val := by
  apply le_antisymm
  · obtain ⟨i, _, e⟩ := iterMin_mem (rhoT (tabOf π) (tabOf π.symm)) (2 ^ (n + 1)) x.val
    rw [e, iter_val π x i]
    exact Fin.le_iff_val_le_val.1
      (Loop.orbMin_le (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))
  · obtain ⟨i, hi, e⟩ := exists_pow_lt_card (Loop.sameCycle_orbMin (Loop.rho (flip0 n) (tau π)) x)
    rw [Fintype.card_fin] at hi
    have h1 := iterMin_le (rhoT (tabOf π) (tabOf π.symm)) (2 ^ (n + 1)) x.val i hi.le
    rw [iter_val π x i, e] at h1
    exact h1

/-! ## One level of the looping rule on tables -/

theorem colT_eq (π : Perm (Fin (2 ^ (n + 1)))) (x : Fin (2 ^ (n + 1))) :
    colT (tabOf π) (tabOf π.symm) x.val = col π x := by
  unfold colT col Loop.colour
  rw [tabOf_length, flipT_val, ← orbMin_val π (flip0 n x), ← orbMin_val π x]
  exact decide_eq_decide.2 Fin.lt_iff_val_lt_val.symm

theorem firstT_eq (π : Perm (Fin (2 ^ (n + 1 + 1)))) (l : Fin (2 ^ (n + 1))) :
    firstT (tabOf π) (tabOf π.symm) l.val = firstOf π l := by
  unfold firstT firstOf
  rw [← colT_eq]
  rw [splitLow_symm_val]
  simp

theorem lastT_eq (π : Perm (Fin (2 ^ (n + 1 + 1)))) (l : Fin (2 ^ (n + 1))) :
    lastT (tabOf π) (tabOf π.symm) l.val = lastOf π l := by
  unfold lastT lastOf
  rw [tabOf_getD' π.symm ((splitLow (n + 1)).symm (false, l)) (2 * l.val) rfl, colT_eq]

theorem half_length (P : List ℕ) (hP : P.length = 2 ^ (n + 1 + 1)) : (P.length / 2) = 2 ^ (n + 1) := by
  rw [hP, pow_succ]
  simp

theorem subT_eq (π : Perm (Fin (2 ^ (n + 1 + 1)))) (b : Bool) :
    subT (tabOf π) (tabOf π.symm) b = tabOf (sub π b) := by
  apply List.ext_getElem
  · rw [tabOf_length]
    simp only [subT, List.length_map, List.length_range]
    exact half_length _ (tabOf_length π)
  · intro i h1 h2
    have hi : i < 2 ^ (n + 1) := by rw [tabOf_length] at h2; exact h2
    simp only [subT, List.getElem_map, List.getElem_range]
    rw [show firstT (tabOf π) (tabOf π.symm) i = firstT (tabOf π) (tabOf π.symm) (⟨i, hi⟩ : Fin _).val from rfl,
      firstT_eq,
      tabOf_getD' π ((splitLow (n + 1)).symm (xor (firstOf π ⟨i, hi⟩) b, ⟨i, hi⟩))
        (2 * i + if xor (firstOf π ⟨i, hi⟩) b then 1 else 0) rfl]
    simp [tabOf, sub_apply, subFun, splitLow_val_snd]

theorem sub_symm_apply (π : Perm (Fin (2 ^ (n + 1 + 1)))) (b : Bool) (l : Fin (2 ^ (n + 1))) :
    (sub π b).symm l = subInv π b l := rfl

theorem subInvT_eq (π : Perm (Fin (2 ^ (n + 1 + 1)))) (b : Bool) :
    subInvT (tabOf π) (tabOf π.symm) b = tabOf (sub π b).symm := by
  apply List.ext_getElem
  · rw [tabOf_length]
    simp only [subInvT, List.length_map, List.length_range]
    exact half_length _ (tabOf_length π)
  · intro i h1 h2
    have hi : i < 2 ^ (n + 1) := by rw [tabOf_length] at h2; exact h2
    simp only [subInvT, List.getElem_map, List.getElem_range]
    rw [show lastT (tabOf π) (tabOf π.symm) i = lastT (tabOf π) (tabOf π.symm) (⟨i, hi⟩ : Fin _).val from rfl,
      lastT_eq,
      tabOf_getD' π.symm ((splitLow (n + 1)).symm (xor (lastOf π ⟨i, hi⟩) b, ⟨i, hi⟩))
        (2 * i + if xor (lastOf π ⟨i, hi⟩) b then 1 else 0) rfl]
    simp [tabOf, sub_symm_apply, subInv, splitLow_val_snd]

/-! ## The canonical settings on tables -/

/-- **Part (a).** The table algorithm computes the canonical settings. -/
theorem settingsTab_eq : ∀ (n : ℕ) (π : Perm (Fin (2 ^ (n + 1)))),
    settingsTab n (tabOf π) (tabOf π.symm) = Net.settings n π
  | 0, π => by
    simp only [settingsTab, Net.settings]
    rw [tabOf_getD' π ((splitLow 0).symm (false, ⟨0, by simp⟩)) 0 rfl]
    rfl
  | n + 1, π => by
    simp only [settingsTab, Net.settings]
    congr 1
    · funext l
      exact firstT_eq π l
    · funext b
      rw [subT_eq, subInvT_eq]
      exact settingsTab_eq n (sub π b)
    · funext l
      exact lastT_eq π l

/-! ## One switch bit along one path of the recursion -/

/-- The setting of the switch of stage `κ` that contains the address `a`, computed on the tables `P = π`,
`Q = π⁻¹` along ONE path of the recursion (the form of `Net.cross`): at most `n + 1` levels, each one table
step. This is the query that the level-0 routing factors need (two switch bits per routing position). -/
def crossT : (n : ℕ) → List ℕ → List ℕ → ℕ → ℕ → Bool
  | 0, P, _, κ, _ => decide (κ = 0) && decide (P.getD 0 0 % 2 = 1)
  | n + 1, P, Q, κ, a =>
    if κ = 0 then firstT P Q (a / 2)
    else if κ ≤ 2 * n + 1 then
      crossT n (subT P Q (decide (a % 2 = 1))) (subInvT P Q (decide (a % 2 = 1))) (κ - 1) (a / 2)
    else if κ = 2 * n + 2 then lastT P Q (a / 2)
    else false

theorem crossT_settingsTab : ∀ (n : ℕ) (P Q : List ℕ) (κ : ℕ) (a : Fin (2 ^ (n + 1))),
    crossT n P Q κ a.val = Net.cross (settingsTab n P Q) κ a
  | 0, _, _, _, _ => rfl
  | n + 1, P, Q, κ, a => by
    have ih := crossT_settingsTab n (subT P Q (decide (a.val % 2 = 1)))
      (subInvT P Q (decide (a.val % 2 = 1))) (κ - 1) (splitLow (n + 1) a).2
    simp only [crossT, settingsTab, Net.cross]
    split_ifs
    · rfl
    · exact ih
    · rfl
    · rfl

/-- **One switch bit on tables.** -/
theorem crossT_eq (n : ℕ) (π : Perm (Fin (2 ^ (n + 1)))) (κ : ℕ) (a : Fin (2 ^ (n + 1))) :
    crossT n (tabOf π) (tabOf π.symm) κ a.val = Net.cross (Net.settings n π) κ a := by
  rw [crossT_settingsTab, settingsTab_eq]

/-- **The switch bits of `P1Benes.settings`** (the parameter `NetBridge.bset (m+1)` of lane net) from the tables
of `π` in label coordinates (`label m a = Σ a_i 2^(m-i)`). -/
theorem settings_eq_crossT (m : ℕ) (π : Perm (Addr (m + 1))) (κ : ℕ) (r : Addr (m + 1)) :
    P1Benes.settings m π κ r =
      crossT m (tabOf ((label m).permCongr π)) (tabOf ((label m).permCongr π).symm) κ (label m r).val := by
  rw [crossT_eq]
  rfl

end P1Benes.Tab
