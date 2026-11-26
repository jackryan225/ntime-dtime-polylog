import OAI.Computability.VPVNP.CompressionState

/-!
# P3 (lane P1-lean-net, copy A): degree padding of a pre-network into an OpenAI compression state

The degree padding of paper `subsec:network` (f) / EG `exact.tex` l.109-115, in the form needed by OpenAI's
`Compression.State a h` (every base vertex has `d = 2^a` outgoing and `d` incoming slots, a permutation `target`
from outgoing to incoming slots without loops, one lane displacement per outgoing base slot, a width per slot and
lane).

A `PreGraph h` has finitely many vertices with four numbered half-edge slots; `mate` pairs used half-edges into
undirected edges (symmetric, no loops); every edge has one lane displacement in `BitWord h`, the same from both
ends (lanes are `ZMod 2`-vectors, so the reverse arc returns to the original lane). `regularize` builds:
* base `V × Bool` (`true` = twin);
* out-slot `i < 4` of `(v, t)` with mate `(u, j)` goes to in-slot `j` of `(u, t)` (twins copy the topology);
  every other out-slot `i` of `(v, t)` goes to in-slot `i` of `(v, !t)`;
* `target` is an involution, so a permutation; `ends_ne` holds because mates have different vertices and twins
  differ from their originals;
* widths: the given width on the original's first four slots, `0` on twins and on the padding slots.
So both orientations of every undirected edge are arcs (the payload on the one with nonzero width), and every
base vertex has exactly `2^a` in- and out-slots, as long as `4 ≤ 2^a`.
-/

namespace P1Net

open OAI.Computability.VPVNP Compression

/-- A pre-network on `h` lane bits with at most four half-edges per vertex. -/
structure PreGraph (h : ℕ) where
  V : Type
  vFintype : Fintype V
  vDecEq : DecidableEq V
  vNonempty : Nonempty V
  /-- The base order (data used by the compressor's greedy rules). -/
  vIndex : V ≃ Fin (@Fintype.card V vFintype)
  mate : V × Fin 4 → Option (V × Fin 4)
  mate_symm : ∀ p q, mate p = some q → mate q = some p
  mate_ne : ∀ p q, mate p = some q → q.1 ≠ p.1
  disp : V × Fin 4 → BitWord h
  disp_mate : ∀ p q, mate p = some q → disp q = disp p

attribute [instance] PreGraph.vFintype PreGraph.vDecEq

namespace PreGraph

variable {h : ℕ} (G : PreGraph h) {a : ℕ} (ha : 4 ≤ 2 ^ a)

/-- The half-edge index of a slot, if the slot is one of the first four. -/
def slot4 (i : Fin (2 ^ a)) : Option (Fin 4) := if hi : (i : ℕ) < 4 then some ⟨i, hi⟩ else none

theorem slot4_castLE (j : Fin 4) : slot4 (j.castLE ha) = some j := by
  simp [slot4, j.isLt]

theorem slot4_eq_some {i : Fin (2 ^ a)} {j : Fin 4} (h : slot4 i = some j) : j.castLE ha = i := by
  unfold slot4 at h
  split_ifs at h with hi
  simp only [Option.some.injEq] at h
  subst h
  rfl

/-- Where an outgoing slot of the padded base goes. -/
def slotMap (p : (G.V × Bool) × Fin (2 ^ a)) : (G.V × Bool) × Fin (2 ^ a) :=
  match slot4 p.2 with
  | some i =>
    match G.mate (p.1.1, i) with
    | some q => ((q.1, p.1.2), q.2.castLE ha)
    | none => ((p.1.1, !p.1.2), p.2)
  | none => ((p.1.1, !p.1.2), p.2)

theorem slotMap_slotMap (p : (G.V × Bool) × Fin (2 ^ a)) : G.slotMap ha (G.slotMap ha p) = p := by
  obtain ⟨⟨v, t⟩, i⟩ := p
  cases hs : slot4 (a := a) i with
  | none =>
    simp only [slotMap, hs, Bool.not_not]
  | some i4 =>
    cases hm : G.mate (v, i4) with
    | none =>
      simp only [slotMap, hs, hm, Bool.not_not]
    | some q =>
      obtain ⟨u, j⟩ := q
      have hm' := G.mate_symm _ _ hm
      simp only [slotMap, hs, hm, slot4_castLE, hm', slot4_eq_some ha hs]

theorem slotMap_ne (p : (G.V × Bool) × Fin (2 ^ a)) : (G.slotMap ha p).1 ≠ p.1 := by
  obtain ⟨⟨v, t⟩, i⟩ := p
  cases hs : slot4 (a := a) i with
  | none =>
    simp only [slotMap, hs, ne_eq, Prod.mk.injEq, and_true, Bool.not_eq_self, not_false_eq_true,
      and_false]
  | some i4 =>
    cases hm : G.mate (v, i4) with
    | none =>
      simp only [slotMap, hs, hm, ne_eq, Prod.mk.injEq, Bool.not_eq_self, and_false,
        not_false_eq_true]
    | some q =>
      have hne := G.mate_ne _ _ hm
      simp only [slotMap, hs, hm, ne_eq, Prod.mk.injEq, not_and]
      intro hq
      exact absurd hq hne

/-- The padded slot graph. -/
def slotGraph : SlotGraph (G.V × Bool) (2 ^ a) where
  target := Function.Involutive.toPerm (G.slotMap ha) (G.slotMap_slotMap ha)
  ends_ne := G.slotMap_ne ha

/-- Lane displacement of an outgoing padded slot (the edge displacement on mated half-edges, else `0`). -/
def displacement (p : (G.V × Bool) × Fin (2 ^ a)) : BitWord h :=
  match slot4 p.2 with
  | some i =>
    match G.mate (p.1.1, i) with
    | some _ => G.disp (p.1.1, i)
    | none => 0
  | none => 0

/-- Width of an outgoing padded slot at a lane: the given width on the original's first four slots, `0` on twins
and padding slots. -/
def padWidth (w : (G.V × Fin 4) × BitWord h → ℕ) (p : ((G.V × Bool) × Fin (2 ^ a)) × BitWord h) : ℕ :=
  match slot4 p.1.2 with
  | some i => if p.1.1.2 then 0 else w ((p.1.1.1, i), p.2)
  | none => 0

/-- **Degree padding.** The compression state of a pre-network with half-edge widths `w`. -/
abbrev regularize (w : (G.V × Fin 4) × BitWord h → ℕ) : State a h where
  Base := G.V × Bool
  baseFintype := inferInstance
  baseNonempty := G.vNonempty.map fun v => (v, false)
  baseIndex := State.productIndex G.vIndex finTwoEquiv.symm
  slots := ⟨G.slotGraph ha, G.displacement⟩
  width := G.padWidth w

theorem regularize_target (w : (G.V × Fin 4) × BitWord h → ℕ) (p : (G.V × Bool) × Fin (2 ^ a)) :
    (G.regularize ha w).slots.base.target p = G.slotMap ha p := rfl

/-- The arc of a mated half-edge `(v, i)` with mate `(u, j)` goes from the original `v` to the original `u`. -/
theorem regularize_target_mate (w : (G.V × Fin 4) × BitWord h → ℕ) {v u : G.V} {i j : Fin 4}
    (hm : G.mate (v, i) = some (u, j)) (t : Bool) :
    (G.regularize ha w).slots.base.target ((v, t), i.castLE ha) = ((u, t), j.castLE ha) := by
  show G.slotMap ha ((v, t), i.castLE ha) = _
  simp [slotMap, slot4_castLE, hm]

theorem regularize_displacement_mate (w : (G.V × Fin 4) × BitWord h → ℕ) {v u : G.V} {i j : Fin 4}
    (hm : G.mate (v, i) = some (u, j)) (t : Bool) :
    (G.regularize ha w).slots.displacement ((v, t), i.castLE ha) = G.disp (v, i) := by
  show G.displacement ((v, t), i.castLE ha) = _
  simp [displacement, slot4_castLE, hm]

theorem regularize_width (w : (G.V × Fin 4) × BitWord h → ℕ) (v : G.V) (i : Fin 4) (l : BitWord h) :
    (G.regularize ha w).width (((v, false), i.castLE ha), l) = w ((v, i), l) := by
  simp [regularize, padWidth, slot4_castLE]

theorem regularize_width_twin (w : (G.V × Fin 4) × BitWord h → ℕ) (v : G.V) (i : Fin (2 ^ a))
    (l : BitWord h) : (G.regularize ha w).width (((v, true), i), l) = 0 := by
  simp only [regularize, padWidth]
  split <;> simp

end PreGraph

end P1Net
