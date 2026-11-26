import P1Benes.Routing
import P1Benes.Wires

/-!
# P1Benes.Settings: canonical Beneš settings, in the network semantics of lane net (lane P2)

Brief: ORG/briefs/P1-lean-benes.md. Owner: P1-lean-benes. Network semantics: `P1Benes.Routing`, a verbatim copy
of lane net's `P1Net/Routing.lean` (namespace renamed): `Addr m = Fin m → ZMod 2`; stage `κ = 0, …, 2m-2` pairs
`a` and `a + flip m κ` on the bit `stageBit m κ` (`m-1, …, 1, 0, 1, …, m-1`); `s κ (rep m κ a) = true` crosses
the switch of that pair; `route s` = all `2m - 1` stages. For the lane network `m = h + 3` (the three port-type
bits and the `h` lane bits are all address bits, so the type bits are part of every label) and, for the state
chain, `m = h + 1`.

The label of an address `a : Addr (m+1)` is `label m a = Σ_i a_i 2^(m-i)` (index `0` most significant, as in
OpenAI's `bitWordFinEquiv`). `label m` identifies the stage structure of `Routing` with the butterfly of
`P1Benes.Net` (`label_add_flip`, `label_stage`): stage `κ` flips the label bit `Net.stageBit m κ`
(`0, 1, …, m, …, 1, 0`).

The canonical settings (`settings m π`): the looping rule of `P1Benes.Net.settings` on the labels. At the outer
bit (stages `0` and `2m`, address index `m`) the items are the edges of the graph of input pairs and output
pairs; the colouring `P1Benes.Loop.colour` alternates along every cycle and gives the least label of each cycle
the colour `false` (it is the ONLY such colouring: `P1Benes.Loop.colour_unique`); an item of colour `b` goes
through the half `b`; recursion on the two induced permutations of the halves. Everything is a computable
function of `π` (no choice).

Targets (brief): `settings`, `route_settings`, `unique_internal`, `settings_cost`.
-/

namespace P1Benes

open Equiv

/-- `ZMod 2 ≃ Bool` (`1 ↦ true`). -/
def zbool : ZMod 2 ≃ Bool where
  toFun z := decide (z = 1)
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

theorem zbool_add_one (z : ZMod 2) : zbool (z + 1) = !zbool z := by
  revert z; decide

/-- The label of an address: `label m a = Σ_i a_i 2^(m-i)` (index `m` = lowest bit). -/
def label : (m : ℕ) → Addr (m + 1) ≃ Fin (2 ^ (m + 1))
  | 0 =>
    { toFun := fun a => (Net.splitLow 0).symm (zbool (a 0), ⟨0, by simp⟩)
      invFun := fun x _ => zbool.symm (Net.splitLow 0 x).1
      left_inv := fun a => by
        funext i
        have hi : i = 0 := by ext; simp only [Fin.val_zero]; have := i.isLt; omega
        subst hi
        simp
      right_inv := fun x => by
        have hu : (Net.splitLow 0 x).2 = ⟨0, by simp⟩ :=
          Fin.ext (by have := (Net.splitLow 0 x).2.isLt; simp at this; omega)
        simp only [Equiv.apply_symm_apply]
        rw [← hu, Prod.mk.eta, Equiv.symm_apply_apply] }
  | m + 1 =>
    { toFun := fun a =>
        (Net.splitLow (m + 1)).symm (zbool (a (Fin.last (m + 1))), label m (Fin.init a))
      invFun := fun x => Fin.snoc (α := fun _ => ZMod 2)
        ((label m).symm (Net.splitLow (m + 1) x).2) (zbool.symm (Net.splitLow (m + 1) x).1)
      left_inv := fun a => by
        simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        exact Fin.snoc_init_self a
      right_inv := fun x => by
        simp only [Fin.snoc_last, Fin.init_snoc, Equiv.apply_symm_apply]
        rw [Prod.mk.eta, Equiv.symm_apply_apply] }

theorem label_zero (a : Addr 1) : label 0 a = (Net.splitLow 0).symm (zbool (a 0), ⟨0, by simp⟩) :=
  rfl

theorem label_succ (m : ℕ) (a : Addr (m + 2)) :
    label (m + 1) a =
      (Net.splitLow (m + 1)).symm (zbool (a (Fin.last (m + 1))), label m (Fin.init a)) :=
  rfl

/-- Adding the unit vector of index `i` flips the label bit `m - i`. -/
theorem label_add_single : ∀ (m : ℕ) (a : Addr (m + 1)) (i : Fin (m + 1)),
    label m (a + Pi.single i 1) = Net.flipBit m (m - i.val) (label m a)
  | 0, a, i => by
    have hi : i = 0 := by ext; simp only [Fin.val_zero]; have := i.isLt; omega
    subst hi
    rw [label_zero, label_zero]
    simp only [Fin.val_zero, Nat.sub_zero, Net.flipBit, Equiv.apply_symm_apply, Pi.add_apply,
      Pi.single_eq_same, zbool_add_one]
  | m + 1, a, i => by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hj : m + 1 - (Fin.castSucc j).val = (m - j.val) + 1 := by
        have := j.isLt; simp only [Fin.coe_castSucc]; omega
      rw [hj, label_succ, label_succ]
      simp only [Net.flipBit, Equiv.apply_symm_apply]
      have h1 : (a + Pi.single (Fin.castSucc j) 1 : Addr (m + 2)) (Fin.last (m + 1)) =
          a (Fin.last (m + 1)) := by
        rw [Pi.add_apply, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne', add_zero]
      have h2 : Fin.init (a + Pi.single (Fin.castSucc j) (1 : ZMod 2)) =
          Fin.init a + Pi.single j 1 := by
        funext k
        simp only [Fin.init, Pi.add_apply, Pi.single_apply, Fin.castSucc_inj]
      rw [h1, h2, label_add_single m (Fin.init a) j]
    · have hj : m + 1 - (Fin.last (m + 1)).val = 0 := by simp
      rw [hj, label_succ, label_succ]
      simp only [Net.flipBit, Equiv.apply_symm_apply]
      have h1 : (a + Pi.single (Fin.last (m + 1)) 1 : Addr (m + 2)) (Fin.last (m + 1)) =
          a (Fin.last (m + 1)) + 1 := by
        rw [Pi.add_apply, Pi.single_eq_same]
      have h2 : Fin.init (a + Pi.single (Fin.last (m + 1)) (1 : ZMod 2)) = Fin.init a := by
        funext k
        simp only [Fin.init, Pi.add_apply]
        rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last k).ne, add_zero]
      rw [h1, h2, zbool_add_one]

/-- The stage bits of `Routing` and of `Net` correspond under `label`. -/
theorem stageBit_label (m κ : ℕ) (hκ : κ ≤ 2 * m) :
    m - (stageBit (m + 1) κ).val = Net.stageBit m κ := by
  simp only [stageBit, Net.stageBit]
  split_ifs with h1 h2 h2
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · omega
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem label_add_flip (m κ : ℕ) (hκ : κ ≤ 2 * m) (a : Addr (m + 1)) :
    label m (a + flip (m + 1) κ) = Net.flipBit m (Net.stageBit m κ) (label m a) := by
  rw [flip, label_add_single, stageBit_label m κ hκ]

/-- The representative of a pair is one of its two members. -/
theorem rep_cases (m : ℕ) [NeZero m] (κ : ℕ) (a : Addr m) :
    rep m κ a = a ∨ rep m κ a = a + flip m κ := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (a (stageBit m κ)) with h | h
  · left
    funext j
    by_cases hj : j = stageBit m κ
    · subst hj; simp [rep, h]
    · simp [rep, Function.update_of_ne hj]
  · right
    funext j
    by_cases hj : j = stageBit m κ
    · subst hj
      simp only [rep, flip, Function.update_self, Pi.add_apply, Pi.single_eq_same, h]
      decide
    · simp [rep, flip, Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-! ## The canonical settings and correctness -/

/-- **P2, the canonical settings** of the Beneš network on `m + 1` address bits for the permutation `π`
(looping rule; module doc). `settings m π κ r` is the setting of the switch of stage `κ` with representative
`r`: the setting of the label network `Net.settings m (label-conjugate of π)` at the label of `r`. -/
def settings (m : ℕ) (π : Equiv.Perm (Addr (m + 1))) : Settings (m + 1) :=
  fun κ r => Net.cross (Net.settings m ((label m).permCongr π)) κ (label m r)

/-- Both members of a pair read the same switch. -/
theorem settings_rep (m : ℕ) (π : Equiv.Perm (Addr (m + 1))) (κ : ℕ) (a : Addr (m + 1)) :
    settings m π κ (rep (m + 1) κ a) = Net.cross (Net.settings m ((label m).permCongr π)) κ (label m a) := by
  show Net.cross _ κ (label m (rep (m + 1) κ a)) = _
  by_cases hκ : κ ≤ 2 * m
  · rcases rep_cases (m + 1) κ a with h | h
    · rw [h]
    · rw [h, label_add_flip m κ hκ, Net.cross_flipBit _ κ _ hκ]
  · rw [Net.cross_eq_false _ κ _ (by omega), Net.cross_eq_false _ κ _ (by omega)]

/-- One stage of `Routing` is one stage of the label network. -/
theorem label_stage (m : ℕ) (π : Equiv.Perm (Addr (m + 1))) (κ : ℕ) (a : Addr (m + 1)) :
    label m (stage (settings m π) κ a) =
      Net.stageFun (Net.settings m ((label m).permCongr π)) κ (label m a) := by
  unfold stage Net.stageFun
  rw [settings_rep]
  by_cases hc : Net.cross (Net.settings m ((label m).permCongr π)) κ (label m a) = true
  · have hκ : κ ≤ 2 * m := by
      by_contra h
      rw [Net.cross_eq_false _ κ _ (by omega)] at hc
      exact absurd hc (by simp)
    rw [if_pos hc, if_pos hc, label_add_flip m κ hκ]
  · rw [if_neg hc, if_neg hc]

theorem label_routeUpTo (m : ℕ) (π : Equiv.Perm (Addr (m + 1))) :
    ∀ (κ : ℕ) (a : Addr (m + 1)), label m (routeUpTo (settings m π) κ a) =
      Net.upTo (Net.settings m ((label m).permCongr π)) κ (label m a)
  | 0, a => rfl
  | κ + 1, a => by
    rw [routeUpTo_succ_apply, label_stage, label_routeUpTo m π κ a]
    rfl

/-- **P2, correctness.** The canonical settings route `π`. -/
theorem route_settings (m : ℕ) (π : Equiv.Perm (Addr (m + 1))) : route (settings m π) = π := by
  ext1 a
  apply (label m).injective
  have h := label_routeUpTo m π (2 * (m + 1) - 1) a
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at h
  rw [route, show 2 * (m + 1) - 1 = 2 * m + 1 by omega, h]
  have h2 := congrArg (fun p : Equiv.Perm (Fin (2 ^ (m + 1))) => p (label m a))
    (Net.flatRoute_settings m ((label m).permCongr π))
  simp only [Net.flatRoute, Equiv.permCongr_apply, Equiv.symm_apply_apply] at h2
  exact h2

/-! ## Uniqueness of the internal values -/

/-- **P2, uniqueness of the internal values.** For any settings `s`, two labellings of the butterfly that obey
the switch semantics (each position puts its item on its selected out-arc, each position of the next column
holds the item of its selected in-arc) and agree on column `0` agree at every column and on every selected
arc. (Used for the parity count: given the inputs, the routing part of the network has exactly one consistent
assignment.) -/
theorem unique_internal {m : ℕ} [NeZero m] {P : Type*} (s : Settings m)
    (pos pos' : ℕ → Addr m → P) (arc arc' : ℕ → Addr m → Bool → P)
    (hout : ∀ κ a, arc κ a (s κ (rep m κ a)) = pos κ a)
    (hin : ∀ κ a', pos (κ + 1) a' = arc κ (stage s κ a') (s κ (rep m κ a')))
    (hout' : ∀ κ a, arc' κ a (s κ (rep m κ a)) = pos' κ a)
    (hin' : ∀ κ a', pos' (κ + 1) a' = arc' κ (stage s κ a') (s κ (rep m κ a')))
    (h0 : pos 0 = pos' 0) :
    ∀ κ, pos κ = pos' κ ∧ ∀ a, arc κ a (s κ (rep m κ a)) = arc' κ a (s κ (rep m κ a)) := by
  have hp : ∀ κ, pos κ = pos' κ := by
    intro κ
    funext b
    have e1 := forcing s pos arc hout hin κ ((routeUpTo s κ).symm b)
    have e2 := forcing s pos' arc' hout' hin' κ ((routeUpTo s κ).symm b)
    rw [Equiv.apply_symm_apply] at e1 e2
    rw [e1, e2, h0]
  intro κ
  exact ⟨hp κ, fun a => by rw [hout, hout', hp κ]⟩

/-- Full form: if moreover every unselected out-arc carries a fixed value `z` (the paper's factor puts `0`
there), the whole labelling of arcs is determined by column `0`. -/
theorem unique_internal_full {m : ℕ} [NeZero m] {P : Type*} (s : Settings m) (z : P)
    (pos pos' : ℕ → Addr m → P) (arc arc' : ℕ → Addr m → Bool → P)
    (hout : ∀ κ a, arc κ a (s κ (rep m κ a)) = pos κ a)
    (hin : ∀ κ a', pos (κ + 1) a' = arc κ (stage s κ a') (s κ (rep m κ a')))
    (hz : ∀ κ a, arc κ a (!s κ (rep m κ a)) = z)
    (hout' : ∀ κ a, arc' κ a (s κ (rep m κ a)) = pos' κ a)
    (hin' : ∀ κ a', pos' (κ + 1) a' = arc' κ (stage s κ a') (s κ (rep m κ a')))
    (hz' : ∀ κ a, arc' κ a (!s κ (rep m κ a)) = z)
    (h0 : pos 0 = pos' 0) : pos = pos' ∧ arc = arc' := by
  have hu := unique_internal s pos pos' arc arc' hout hin hout' hin' h0
  refine ⟨funext fun κ => (hu κ).1, ?_⟩
  funext κ a b
  by_cases hb : b = s κ (rep m κ a)
  · subst hb; exact (hu κ).2 a
  · have : b = !s κ (rep m κ a) := by
      cases hc : s κ (rep m κ a) <;> cases b <;> simp_all
    rw [this, hz, hz']

/-! ## Cost -/

/-- Operation count of the looping algorithm on `2^(n+1)` items, for an implementation that keeps every
permutation as a table (coarse model). Level `n + 1` (`N = 2^(n+2)` items): the `N` colours needed for the
first and last stages, each two orbit scans of `N` steps of `ρ` (5 table operations per step: two look-ups of
`π` or `π⁻¹`, two bit flips, one comparison), then the tables of the two induced half permutations and their
inverses (`4 N` look-ups), then the two halves. Level `0`: one look-up. -/
def settingsSteps : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ (n + 2) * (2 * (5 * 2 ^ (n + 2))) + 4 * 2 ^ (n + 2) + 2 * settingsSteps n

/-- **P2, cost.** The settings are computed with `O(N^2)` operations, `N = 2^(n+1)` the number of items. -/
theorem settings_cost (n : ℕ) : settingsSteps n ≤ 28 * (2 ^ (n + 1)) ^ 2 := by
  induction n with
  | zero => simp [settingsSteps]
  | succ n ih =>
    show settingsSteps (n + 1) ≤ 28 * (2 ^ (n + 1 + 1)) ^ 2
    have e : settingsSteps (n + 1) =
        40 * (2 ^ (n + 1)) ^ 2 + 8 * 2 ^ (n + 1) + 2 * settingsSteps n := by
      simp only [settingsSteps]; ring
    have e2 : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    have h4 : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    rw [e, e2]
    nlinarith [ih, h4, Nat.mul_le_mul h4 h4]

end P1Benes
