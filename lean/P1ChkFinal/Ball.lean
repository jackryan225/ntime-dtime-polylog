import P1P7.Defs

/-!
# P1, wave 2, checks C10-C13 (lane P1-lean-W2-chkfinal): the ball of a base, walked by stored addresses

Paper `research/papers/ntime-dtime-polylog.tex`, rem:G1 (l.858-870): the verifier walks through a ball by the
neighbour addresses stored in the base records (P1). `bfs nb x ρ` lists the addresses reached from `x` in at most
`ρ` rounds, where one round adds the listed neighbours `nb y` of every address `y` reached so far.

`mem_bfs_iff`: for the TRUE base records of an OpenAI `State` (neighbour addresses = `P1P7.outNbr`, `P1P7.inNbr`),
the addresses reached in `ρ` rounds are exactly the addresses of the bases at distance at most `ρ` in
`P1P7.baseGraph`, the graph in which P7 states its locality lemmas.
-/

namespace P1ChkFinal

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open P1P7

/-! ## Walking by stored neighbour lists (no OpenAI data) -/

/-- Addresses reached from `x` in at most `ρ` rounds of the neighbour lists `nb`. -/
def bfs (nb : ℕ → List ℕ) (x : ℕ) : ℕ → List ℕ
  | 0 => [x]
  | ρ + 1 => bfs nb x ρ ++ (bfs nb x ρ).flatMap nb

theorem mem_bfs_zero {nb : ℕ → List ℕ} {x β : ℕ} : β ∈ bfs nb x 0 ↔ β = x := by
  simp [bfs]

theorem mem_bfs_succ {nb : ℕ → List ℕ} {x ρ β : ℕ} :
    β ∈ bfs nb x (ρ + 1) ↔ β ∈ bfs nb x ρ ∨ ∃ y ∈ bfs nb x ρ, β ∈ nb y := by
  simp only [bfs, List.mem_append, List.mem_flatMap]

/-- The neighbour lists that the verifier reads from stored data `old` through the decoder `nbrsOf`
(no neighbours at a non-address). -/
def nbOf {Δ : Type*} (nbrsOf : Δ → List ℕ) (old : ℕ → Option Δ) : ℕ → List ℕ :=
  fun α => (old α).elim [] nbrsOf

/-- The stored data of the ball of radius `ρ` around `x`, by address: `old α` for the addresses reached by `bfs`,
`none` elsewhere. This is all that check C10 passes to the recomputation. -/
def ballMap {Δ : Type*} (nb : ℕ → List ℕ) (old : ℕ → Option Δ) (x ρ : ℕ) : ℕ → Option Δ :=
  fun α => if α ∈ bfs nb x ρ then old α else none

/-! ## A graph fact: one more round -/

theorem exists_adj_of_length_succ {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {n : ℕ}
    (hp : p.length = n + 1) : ∃ w, G.Adj u w ∧ ∃ q : G.Walk w v, q.length = n := by
  cases p with
  | nil => simp at hp
  | cons h q => exact ⟨_, h, q, by simpa using hp⟩

/-- `edist x y ≤ ρ + 1` iff `y` is within `ρ` of `x` or adjacent to a base within `ρ` of `x`. -/
theorem edist_le_succ_iff {V : Type*} {G : SimpleGraph V} {x y : V} {ρ : ℕ} :
    G.edist x y ≤ ((ρ + 1 : ℕ) : ℕ∞) ↔ G.edist x y ≤ (ρ : ℕ∞) ∨ ∃ z, G.edist x z ≤ (ρ : ℕ∞) ∧ G.Adj z y := by
  constructor
  · intro h
    by_cases h' : G.edist x y ≤ (ρ : ℕ∞)
    · exact Or.inl h'
    · right
      have hne : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h
      obtain ⟨k, hk⟩ : ∃ k : ℕ, G.edist x y = k := ⟨_, (ENat.natCast_toNat hne).symm⟩
      rw [hk] at h h'
      have h1 : k ≤ ρ + 1 := by exact_mod_cast h
      have h2 : ¬ k ≤ ρ := by exact_mod_cast h'
      have hk1 : k = ρ + 1 := by omega
      obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hk
      have hr : w.reverse.length = ρ + 1 := by rw [SimpleGraph.Walk.length_reverse, hw, hk1]
      obtain ⟨z, hyz, q, hq⟩ := exists_adj_of_length_succ w.reverse hr
      refine ⟨z, ?_, hyz.symm⟩
      rw [SimpleGraph.edist_comm]
      calc G.edist z x ≤ q.length := SimpleGraph.edist_le q
        _ = ρ := by rw [hq]
  · rintro (h | ⟨z, hz, hadj⟩)
    · exact h.trans (by exact_mod_cast Nat.le_add_right ρ 1)
    · calc G.edist x y ≤ G.edist x z + G.edist z y := SimpleGraph.edist_triangle
        _ ≤ (ρ : ℕ∞) + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
          exact add_le_add hz (le_refl 1)
        _ = ((ρ + 1 : ℕ) : ℕ∞) := (Nat.cast_succ ρ).symm

/-! ## The true records of an OpenAI state -/

variable {a g : ℕ}

theorem addr_lt (X : State a g) (y : X.Base) : addr X y < Fintype.card X.Base :=
  (X.baseIndex y).isLt

theorem addr_injective (X : State a g) : Function.Injective (addr X) := by
  intro y z h
  exact X.baseIndex.injective (Fin.ext h)

/-- The base with address `α`, if `α` is an address. -/
def baseAt (X : State a g) (α : ℕ) : Option X.Base :=
  if h : α < Fintype.card X.Base then some (X.baseIndex.symm ⟨α, h⟩) else none

theorem baseAt_addr (X : State a g) (y : X.Base) : baseAt X (addr X y) = some y := by
  unfold baseAt
  rw [dif_pos (addr_lt X y)]
  congr 1
  apply X.baseIndex.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem baseAt_eq_some {X : State a g} {α : ℕ} {y : X.Base} : baseAt X α = some y ↔ addr X y = α := by
  constructor
  · intro h
    by_cases hα : α < Fintype.card X.Base
    · rw [baseAt, dif_pos hα, Option.some.injEq] at h
      rw [← h]
      show (X.baseIndex (X.baseIndex.symm ⟨α, hα⟩) : ℕ) = α
      rw [Equiv.apply_symm_apply]
    · rw [baseAt, dif_neg hα] at h
      exact absurd h (by simp)
  · rintro rfl
    exact baseAt_addr X y

theorem baseAt_eq_none {X : State a g} {α : ℕ} : baseAt X α = none ↔ Fintype.card X.Base ≤ α := by
  by_cases hα : α < Fintype.card X.Base
  · rw [baseAt, dif_pos hα]
    exact ⟨fun h => absurd h (by simp), fun h => absurd hα (not_lt.mpr h)⟩
  · rw [baseAt, dif_neg hα]
    exact ⟨fun _ => not_lt.mp hα, fun _ => rfl⟩

/-- Neighbour addresses of a base: the heads of its out-slots, then the tails of its in-slots (the address parts
of the base record (P1), `P1P7.outNbr` and `P1P7.inNbr`). -/
def nbrAddrs (X : State a g) (y : X.Base) : List ℕ :=
  List.ofFn (fun k => (outNbr X y k).1) ++ List.ofFn (fun k => (inNbr X y k).1)

/-- Neighbour addresses by address (none at a non-address). -/
def nbrAt (X : State a g) (α : ℕ) : List ℕ := ((baseAt X α).map (nbrAddrs X)).getD []

theorem nbrAt_addr (X : State a g) (y : X.Base) : nbrAt X (addr X y) = nbrAddrs X y := by
  simp [nbrAt, baseAt_addr]

theorem exists_of_mem_nbrAddrs (X : State a g) (z : X.Base) {β : ℕ} (h : β ∈ nbrAddrs X z) :
    ∃ y, addr X y = β ∧ ((∃ k, (X.slots.base.target (z, k)).1 = y) ∨ (∃ k, (X.slots.base.target (y, k)).1 = z)) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨k, hk⟩ := List.mem_ofFn.mp h
    exact ⟨(X.slots.base.target (z, k)).1, hk, Or.inl ⟨k, rfl⟩⟩
  · obtain ⟨k, hk⟩ := List.mem_ofFn.mp h
    refine ⟨(X.slots.base.target.symm (z, k)).1, hk, Or.inr ⟨(X.slots.base.target.symm (z, k)).2, ?_⟩⟩
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem adj_of_nbr (X : State a g) {z y : X.Base} (hzy : z ≠ y)
    (h : (∃ k, (X.slots.base.target (z, k)).1 = y) ∨ (∃ k, (X.slots.base.target (y, k)).1 = z)) :
    (baseGraph X).Adj z y := by
  rw [baseGraph, SimpleGraph.fromRel_adj]
  exact ⟨hzy, h⟩

theorem mem_nbrAddrs_of_adj (X : State a g) {z y : X.Base} (h : (baseGraph X).Adj z y) :
    addr X y ∈ nbrAddrs X z := by
  rw [baseGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, ?_⟩)
    simp only [outNbr, hk]
  · refine List.mem_append_right _ (List.mem_ofFn.mpr ⟨(X.slots.base.target (y, k)).2, ?_⟩)
    have he : X.slots.base.target.symm (z, (X.slots.base.target (y, k)).2) = (y, k) := by
      rw [Equiv.symm_apply_eq, ← hk]
    simp only [inNbr, he]

/-- **Ball lemma.** For the true records, the addresses reached in `ρ` rounds from `addr x` are exactly the
addresses of the bases at distance at most `ρ` from `x` in `P1P7.baseGraph`. -/
theorem mem_bfs_iff (X : State a g) (x : X.Base) :
    ∀ (ρ β : ℕ), β ∈ bfs (nbrAt X) (addr X x) ρ ↔ ∃ y, addr X y = β ∧ (baseGraph X).edist x y ≤ (ρ : ℕ∞)
  | 0, β => by
    rw [mem_bfs_zero]
    constructor
    · rintro rfl
      exact ⟨x, rfl, by simp⟩
    · rintro ⟨y, rfl, hd⟩
      have h0 : (baseGraph X).edist x y = 0 := le_antisymm (by simpa using hd) zero_le
      rw [SimpleGraph.edist_eq_zero_iff] at h0
      rw [h0]
  | ρ + 1, β => by
    rw [mem_bfs_succ]
    constructor
    · rintro (h | ⟨γ, hγ, hβ⟩)
      · obtain ⟨y, hy, hd⟩ := (mem_bfs_iff X x ρ β).mp h
        exact ⟨y, hy, hd.trans (by exact_mod_cast Nat.le_add_right ρ 1)⟩
      · obtain ⟨z, rfl, hz⟩ := (mem_bfs_iff X x ρ γ).mp hγ
        rw [nbrAt_addr] at hβ
        obtain ⟨y, rfl, hy⟩ := exists_of_mem_nbrAddrs X z hβ
        refine ⟨y, rfl, ?_⟩
        by_cases hzy : z = y
        · subst hzy
          exact hz.trans (by exact_mod_cast Nat.le_add_right ρ 1)
        · exact edist_le_succ_iff.mpr (Or.inr ⟨z, hz, adj_of_nbr X hzy hy⟩)
    · rintro ⟨y, rfl, hd⟩
      rcases edist_le_succ_iff.mp hd with hd | ⟨z, hz, hadj⟩
      · exact Or.inl ((mem_bfs_iff X x ρ _).mpr ⟨y, rfl, hd⟩)
      · refine Or.inr ⟨addr X z, (mem_bfs_iff X x ρ _).mpr ⟨z, rfl, hz⟩, ?_⟩
        rw [nbrAt_addr]
        exact mem_nbrAddrs_of_adj X hadj

end P1ChkFinal
