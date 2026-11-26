import P1Benes.Settings
import P1Net.Routing

/-!
# P1Benes.Link: the P2 theorems in lane net's own routing semantics (`P1Net.Routing`)

`P1Benes.Routing` is a verbatim copy of `P1Net.Routing`; the definitions agree by `rfl`, so the net lane can
use `route_settings_net` and `unique_internal_net` directly (as `P1Net.Assumed.benes`).
-/

namespace P1Benes

theorem settings_eq_net (m : ℕ) : P1Benes.Settings m = P1Net.Routing.Settings m := rfl

theorem rep_eq_net (m : ℕ) [NeZero m] : P1Benes.rep m = P1Net.Routing.rep m := rfl

theorem stage_eq_net (m : ℕ) [NeZero m] (s : Settings m) :
    P1Benes.stage s = P1Net.Routing.stage s := rfl

theorem routeUpTo_eq_net (m : ℕ) [NeZero m] (s : Settings m) (κ : ℕ) :
    P1Benes.routeUpTo s κ = P1Net.Routing.routeUpTo s κ := by
  induction κ with
  | zero => rfl
  | succ κ ih =>
    show P1Benes.stagePerm s κ * P1Benes.routeUpTo s κ = P1Net.Routing.stagePerm s κ * P1Net.Routing.routeUpTo s κ
    rw [ih]
    rfl

theorem route_eq_net (m : ℕ) [NeZero m] (s : Settings m) :
    P1Benes.route s = P1Net.Routing.route s := routeUpTo_eq_net m s _

/-- **P2 for lane net**: the canonical settings route `π` in `P1Net.Routing`'s semantics. -/
theorem route_settings_net (m : ℕ) (π : Equiv.Perm (P1Net.Routing.Addr (m + 1))) :
    P1Net.Routing.route (settings m π) = π := by
  rw [← route_eq_net]
  exact route_settings m π

/-- **P2 uniqueness for lane net**, in `P1Net.Routing`'s semantics. -/
theorem unique_internal_net {m : ℕ} [NeZero m] {P : Type*} (s : P1Net.Routing.Settings m)
    (pos pos' : ℕ → P1Net.Routing.Addr m → P) (arc arc' : ℕ → P1Net.Routing.Addr m → Bool → P)
    (hout : ∀ κ a, arc κ a (s κ (P1Net.Routing.rep m κ a)) = pos κ a)
    (hin : ∀ κ a', pos (κ + 1) a' = arc κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a')))
    (hout' : ∀ κ a, arc' κ a (s κ (P1Net.Routing.rep m κ a)) = pos' κ a)
    (hin' : ∀ κ a', pos' (κ + 1) a' =
      arc' κ (P1Net.Routing.stage s κ a') (s κ (P1Net.Routing.rep m κ a')))
    (h0 : pos 0 = pos' 0) :
    ∀ κ, pos κ = pos' κ ∧
      ∀ a, arc κ a (s κ (P1Net.Routing.rep m κ a)) = arc' κ a (s κ (P1Net.Routing.rep m κ a)) :=
  unique_internal s pos pos' arc arc' hout hin hout' hin' h0

end P1Benes
