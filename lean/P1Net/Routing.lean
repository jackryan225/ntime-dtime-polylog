import Mathlib

/-!
# P3 (lane P1-lean-net): routing semantics of the Beneš stages used by the lane network

Addresses are binary words `Addr m = Fin m → ZMod 2` (for the content routing of one tape in one big interval:
the three port-type bits and the `h` lane bits; for the state chain: one type bit and the lane bits).
Stage `κ` (`κ = 0, ..., 2m - 2`) pairs the addresses `a` and `a + flip κ`, where `flip κ` is the unit vector of
the stage bit (bits `m-1, ..., 1, 0, 1, ..., m-1`). A switch setting `s κ (rep κ a) : Bool` (cross = `true`)
is read at the representative of the pair (stage bit cleared), so both members of a pair use one switch.

* `stage`: the map of one stage (an involution), `routeUpTo s κ`: the first `κ` stages, `route s`: all stages.
* `forcing`: in any labelling of the butterfly in which every position passes its item to its selected out-arc
  and takes the item of its selected in-arc, the item at position `(κ, routeUpTo s κ a)` is the item at
  `(0, a)`. Hence the destination `π a` receives the source `a` when `route s = π`.

The canonical settings (`route (settings π) = π`, lane P1-lean-benes) enter the network as a parameter.
-/

namespace P1Net.Routing

/-- Binary addresses with `m` bits. -/
abbrev Addr (m : ℕ) := Fin m → ZMod 2

variable {m : ℕ} [NeZero m]

/-- The address bit switched at stage `κ`: bits `m-1, ..., 1, 0, 1, ..., m-1` for `κ = 0, ..., 2m-2`. -/
def stageBit (m : ℕ) [NeZero m] (κ : ℕ) : Fin m :=
  ⟨(if κ < m then m - 1 - κ else κ + 1 - m) % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

/-- The unit vector of the stage bit. -/
def flip (m : ℕ) [NeZero m] (κ : ℕ) : Addr m := Pi.single (stageBit m κ) 1

/-- The representative of the pair `{a, a + flip κ}`: the stage bit cleared. -/
def rep (m : ℕ) [NeZero m] (κ : ℕ) (a : Addr m) : Addr m := Function.update a (stageBit m κ) 0

/-- Switch settings: `s κ (rep κ a) = true` means that the switch of stage `κ` on the pair of `a` crosses. -/
abbrev Settings (m : ℕ) := ℕ → Addr m → Bool

theorem flip_add_flip (κ : ℕ) : flip m κ + flip m κ = 0 := by
  funext j
  simp only [flip, Pi.add_apply, Pi.zero_apply]
  by_cases hj : j = stageBit m κ
  · subst hj; simp only [Pi.single_eq_same]; decide
  · simp [Pi.single_eq_of_ne hj]

theorem rep_add_flip (κ : ℕ) (a : Addr m) : rep m κ (a + flip m κ) = rep m κ a := by
  funext j
  simp only [rep, flip]
  by_cases hj : j = stageBit m κ
  · subst hj; simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

/-- One stage of the network. -/
def stage (s : Settings m) (κ : ℕ) (a : Addr m) : Addr m :=
  if s κ (rep m κ a) then a + flip m κ else a

theorem rep_stage (s : Settings m) (κ : ℕ) (a : Addr m) : rep m κ (stage s κ a) = rep m κ a := by
  unfold stage
  split_ifs
  · exact rep_add_flip κ a
  · rfl

theorem stage_stage (s : Settings m) (κ : ℕ) (a : Addr m) : stage s κ (stage s κ a) = a := by
  have hr := rep_stage s κ a
  unfold stage at hr ⊢
  by_cases h : s κ (rep m κ a) = true
  · rw [if_pos h] at hr ⊢
    rw [hr, if_pos h, add_assoc, flip_add_flip, add_zero]
  · rw [if_neg h] at hr ⊢
    rw [if_neg h]

/-- One stage as a permutation (an involution). -/
def stagePerm (s : Settings m) (κ : ℕ) : Equiv.Perm (Addr m) :=
  Function.Involutive.toPerm (stage s κ) (stage_stage s κ)

/-- The first `κ` stages. -/
def routeUpTo (s : Settings m) : ℕ → Equiv.Perm (Addr m)
  | 0 => 1
  | κ + 1 => stagePerm s κ * routeUpTo s κ

/-- The permutation routed by all `2m - 1` stages. -/
def route (s : Settings m) : Equiv.Perm (Addr m) := routeUpTo s (2 * m - 1)

theorem routeUpTo_succ_apply (s : Settings m) (κ : ℕ) (a : Addr m) :
    routeUpTo s (κ + 1) a = stage s κ (routeUpTo s κ a) := rfl

/-- **Forcing.** In a labelling of the butterfly where each position `(κ, a)` puts its item `pos κ a` on its
selected out-arc (`arc κ a b`, `b` = the switch of its pair) and each position `(κ + 1, a')` holds the item of its
selected in-arc (from `(κ, stage s κ a')`), the item at `(κ, routeUpTo s κ a)` is the source item `pos 0 a`. -/
theorem forcing {P : Type*} (s : Settings m) (pos : ℕ → Addr m → P) (arc : ℕ → Addr m → Bool → P)
    (hout : ∀ κ a, arc κ a (s κ (rep m κ a)) = pos κ a)
    (hin : ∀ κ a', pos (κ + 1) a' = arc κ (stage s κ a') (s κ (rep m κ a'))) :
    ∀ κ a, pos κ (routeUpTo s κ a) = pos 0 a := by
  intro κ
  induction κ with
  | zero => intro a; rfl
  | succ κ ih =>
    intro a
    rw [routeUpTo_succ_apply, hin, stage_stage]
    -- the switch read at `stage a'` is the switch of the same pair
    have hsw : s κ (rep m κ (stage s κ (routeUpTo s κ a))) = s κ (rep m κ (routeUpTo s κ a)) := by
      rw [rep_stage]
    rw [hsw, hout, ih]

/-- At the last column the destination `route s a` holds the source item `a`. -/
theorem forcing_route {P : Type*} (s : Settings m) (pos : ℕ → Addr m → P) (arc : ℕ → Addr m → Bool → P)
    (hout : ∀ κ a, arc κ a (s κ (rep m κ a)) = pos κ a)
    (hin : ∀ κ a', pos (κ + 1) a' = arc κ (stage s κ a') (s κ (rep m κ a'))) (a : Addr m) :
    pos (2 * m - 1) (route s a) = pos 0 a :=
  forcing s pos arc hout hin (2 * m - 1) a

/-- **Forcing on the first `n` stages** (the hypotheses are needed only there). -/
theorem forcing_le {P : Type*} (s : Settings m) (pos : ℕ → Addr m → P) (arc : ℕ → Addr m → Bool → P)
    (n : ℕ) (hout : ∀ κ < n, ∀ a, arc κ a (s κ (rep m κ a)) = pos κ a)
    (hin : ∀ κ < n, ∀ a', pos (κ + 1) a' = arc κ (stage s κ a') (s κ (rep m κ a'))) :
    ∀ κ ≤ n, ∀ a, pos κ (routeUpTo s κ a) = pos 0 a := by
  intro κ
  induction κ with
  | zero => intro _ a; rfl
  | succ κ ih =>
    intro hκ a
    rw [routeUpTo_succ_apply, hin κ (by omega), stage_stage]
    have hsw : s κ (rep m κ (stage s κ (routeUpTo s κ a))) = s κ (rep m κ (routeUpTo s κ a)) := by
      rw [rep_stage]
    rw [hsw, hout κ (by omega), ih (by omega)]

end P1Net.Routing
