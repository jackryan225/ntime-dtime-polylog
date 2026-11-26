import P1P7.Defs

/-!
# P7, shrink half, step (1): address transport along balls

Generic over OpenAI's `State`: if two states agree (by address) on the neighbour addresses of every base within distance
`r` of `x`, then every base `y` within distance `r + 1` of `x` has a partner `y'` in the other state with the same
address and at most the same distance from `x'`. This is the ball bookkeeping that both shrink congruence theorems need.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression

variable {a g g' : ℕ}

/-- Addresses identify bases. -/
theorem addr_injective (X : State a g) : Function.Injective (addr X) := by
  intro y z h
  exact X.baseIndex.injective (Fin.ext h)

/-- One edge: if `v` and `v'` have equal addresses and equal neighbour addresses, every neighbour `w` of `v` has a
partner neighbour `w'` of `v'` with the same address. -/
theorem adj_transport (X : State a g) (X' : State a g') (v w : X.Base) (v' : X'.Base)
    (hnb : ∀ k, addr X (X.slots.base.target (v, k)).1 = addr X' (X'.slots.base.target (v', k)).1 ∧
        addr X (X.slots.base.target.symm (v, k)).1 = addr X' (X'.slots.base.target.symm (v', k)).1)
    (h : (baseGraph X).Adj v w) :
    ∃ w' : X'.Base, addr X' w' = addr X w ∧ (baseGraph X').Adj v' w' := by
  rw [baseGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, ⟨k, hk⟩ | ⟨k, hk⟩⟩ := h
  · -- `w` is an out-neighbour of `v`
    refine ⟨(X'.slots.base.target (v', k)).1, ?_, ?_⟩
    · rw [← hk]
      exact ((hnb k).1).symm
    · rw [baseGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun he => X'.slots.base.ends_ne (v', k) he.symm, Or.inl ⟨k, rfl⟩⟩
  · -- `w` is an in-neighbour of `v`
    have hwv : X.slots.base.target (w, k) = (v, (X.slots.base.target (w, k)).2) := Prod.ext hk rfl
    have hw : X.slots.base.target.symm (v, (X.slots.base.target (w, k)).2) = (w, k) := by
      rw [Equiv.symm_apply_eq, hwv]
    set k₂ := (X.slots.base.target (w, k)).2
    refine ⟨(X'.slots.base.target.symm (v', k₂)).1, ?_, ?_⟩
    · have := (hnb k₂).2
      rw [hw] at this
      exact this.symm
    · have hq : X'.slots.base.target (X'.slots.base.target.symm (v', k₂)) = (v', k₂) :=
        Equiv.apply_symm_apply _ _
      rw [baseGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inr ⟨(X'.slots.base.target.symm (v', k₂)).2, ?_⟩⟩
      · intro he
        have hne := X'.slots.base.ends_ne (X'.slots.base.target.symm (v', k₂))
        rw [hq] at hne
        exact hne he
      · rw [Prod.mk.eta, hq]

/-- Transport along the first `i` steps of a walk from `x`. -/
theorem addr_transport_getVert (X : State a g) (X' : State a g') (x : X.Base) (x' : X'.Base)
    (hx : addr X x = addr X' x') (r : ℕ)
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ r →
      ∀ k, addr X (X.slots.base.target (y, k)).1 = addr X' (X'.slots.base.target (y', k)).1 ∧
        addr X (X.slots.base.target.symm (y, k)).1 = addr X' (X'.slots.base.target.symm (y', k)).1)
    {y : X.Base} (p : (baseGraph X).Walk x y) (hp : p.length ≤ r + 1) :
    ∀ i, i ≤ p.length → (baseGraph X).edist x (p.getVert i) ≤ i ∧
      ∃ v' : X'.Base, addr X' v' = addr X (p.getVert i) ∧ (baseGraph X').edist x' v' ≤ i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [SimpleGraph.Walk.getVert_zero]
    exact ⟨by simp, x', hx.symm, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨hdist, v', hv', hd'⟩ := ih (by omega)
    have hadj := p.adj_getVert_succ (i := i) (by omega)
    have hir : (baseGraph X).edist x (p.getVert i) ≤ r :=
      hdist.trans (by exact_mod_cast (by omega : i ≤ r))
    obtain ⟨w', hw', hadj'⟩ := adj_transport X X' _ _ v' (hagree _ _ hv'.symm hir) hadj
    refine ⟨?_, w', hw', ?_⟩
    · calc (baseGraph X).edist x (p.getVert (i + 1))
          ≤ (baseGraph X).edist x (p.getVert i) + (baseGraph X).edist (p.getVert i) (p.getVert (i + 1)) :=
            SimpleGraph.edist_triangle
        _ ≤ i + 1 := by
            rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
            exact add_le_add hdist le_rfl
        _ = ((i + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    · calc (baseGraph X').edist x' w'
          ≤ (baseGraph X').edist x' v' + (baseGraph X').edist v' w' := SimpleGraph.edist_triangle
        _ ≤ i + 1 := by
            rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj']
            exact add_le_add hd' le_rfl
        _ = ((i + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- Transport of a whole ball: partners exist and are not farther from `x'`. -/
theorem addr_transport (X : State a g) (X' : State a g') (x : X.Base) (x' : X'.Base)
    (hx : addr X x = addr X' x') (r : ℕ)
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ r →
      ∀ k, addr X (X.slots.base.target (y, k)).1 = addr X' (X'.slots.base.target (y', k)).1 ∧
        addr X (X.slots.base.target.symm (y, k)).1 = addr X' (X'.slots.base.target.symm (y', k)).1)
    (y : X.Base) (hy : (baseGraph X).edist x y ≤ r + 1) :
    ∃ y' : X'.Base, addr X' y' = addr X y ∧ (baseGraph X').edist x' y' ≤ (baseGraph X).edist x y := by
  have hne : (baseGraph X).edist x y ≠ ⊤ := ne_top_of_le_ne_top (by simp) hy
  obtain ⟨w, hw⟩ := (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
  have hlen : w.length ≤ r + 1 := by
    have : ((w.length : ℕ) : ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) := by rw [hw]; exact_mod_cast hy
    exact_mod_cast this
  obtain ⟨-, y', hy', hd⟩ := addr_transport_getVert X X' x x' hx r hagree w hlen w.length le_rfl
  rw [SimpleGraph.Walk.getVert_length] at hy'
  exact ⟨y', hy', hw ▸ hd⟩

end P1P7
