import OAI.Computability.VPVNP.IteratedCompression
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# P7: definitions and proved lemmas behind the locality statements (module P1P7.Defs)

The three locality theorems themselves are stated (and proved) in `P1P7.Statement`, which imports this file and the
proofs (P1P7/ShrinkLocal.lean, P1P7/ShrinkPanel.lean, P1P7/RefreshLocal.lean). Before 2026-11-25 09:50Z this file
was `P1P7.Statement` with the three theorems as `sorry`; nothing else was changed.

Problem P1 (C1, wall card W-ntime-dtime-polylog), Lean plan research/g3/leanplan/PLAN.md, task P7.
Paper: research/papers/ntime-dtime-polylog.tex, Lemma lem:locality (l.783-890).
OpenAI library: research/lean/openai-math/lean (commit 3344da5), folder OAI/Computability/VPVNP. The block is
`B.procedure f hf = S.assembleBlock (B.shrinkProcedure f hf) (B.refreshProcedure f hf)` (IteratedCompression.lean:30).
One shrinking substep is `X.shrinkStatePass B.shrink κ hκ ready` (ShrinkProcedure.lean:44, ShrinkStatePass.lean:91);
its next state is `X.shrinkNext B ready s` (ShrinkStatePass.lean:62). One refresh substep is `dyadicRefreshPass`
(RefreshProcedure.lean:33, DegreeRefreshPass.lean:58); its next state is `dyadicRefreshNext` (DegreeRefreshPass.lean:41).

The statements below say what the verifier of Lemma P needs:
* `panel` = the paper's (P1) base record and (P2) widths, read off an OpenAI `State` with addresses `X.baseIndex`.
* `shrink_records_local` (paper (a)(i)): neighbour addresses, displacements and all widths at the children
  `(x, j)` of `x` depend only on the panels, greedy colours, tag offsets and term choices of the bases within
  distance 3 of `x`, and on the one layout bit.
* `shrink_panel_local` (paper (a)(ii)): the full panel, with the far slot numbers, from distance 6.
* `refresh_panel_local` (paper (b)): the full panel of `(x, j)` from distance 1 and the block terms at `x`.
* `chosenLayout_eq_int`: the global layout bit is a comparison of two integer sums with coefficients 10,20,6,5.
* `orderedColor_local`, `orderedTagOffsets_local`: the greedy data obey a rule that reads only the neighbours
  (OpenAI's scan: neighbours LATER in base order still count with the initial value 0).
Locality is stated as congruence: two states that agree (by address) on a ball give the same panels.
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh

/-! ## Panels of a state (paper Definition def:panel, (P1) and (P2)) -/

section Panels

variable {a g : ℕ}

/-- Address of a base vertex: its number in the state's own base order (paper rem:G1). -/
def addr (X : State a g) (y : X.Base) : ℕ := (X.baseIndex y : ℕ)

/-- Out-slot `k` of `y`: address of the head base and the lane displacement of the arc. -/
def outNbr (X : State a g) (y : X.Base) (k : Fin (2 ^ a)) : ℕ × BitWord g :=
  (addr X (X.slots.base.target (y, k)).1, X.slots.displacement (y, k))

/-- In-slot `k` of `y`: address of the tail base and the lane displacement of the arc. -/
def inNbr (X : State a g) (y : X.Base) (k : Fin (2 ^ a)) : ℕ × BitWord g :=
  (addr X (X.slots.base.target.symm (y, k)).1, X.slots.displacement (X.slots.base.target.symm (y, k)))

/-- Far slot numbers: the incoming slot at the head of out-slot `k`, the outgoing slot at the tail of in-slot `k`. -/
def outFar (X : State a g) (y : X.Base) (k : Fin (2 ^ a)) : ℕ := ((X.slots.base.target (y, k)).2 : ℕ)

def inFar (X : State a g) (y : X.Base) (k : Fin (2 ^ a)) : ℕ := ((X.slots.base.target.symm (y, k)).2 : ℕ)

/-- (P2): the widths of the outgoing actual arcs at all lanes. -/
def outWidths (X : State a g) (y : X.Base) : Fin (2 ^ a) → BitWord g → ℕ :=
  fun k l => X.width ((y, k), l)

/-- The panel of a base without the far slot numbers. -/
def nearPanel (X : State a g) (y : X.Base) :=
  (outNbr X y, inNbr X y, outWidths X y)

/-- The full panel (P1)+(P2). -/
def panel (X : State a g) (y : X.Base) :=
  (outNbr X y, outFar X y, inNbr X y, inFar X y, outWidths X y)

/-- The undirected graph under the base slot graph; balls are taken in it. -/
def baseGraph (X : State a g) : SimpleGraph X.Base :=
  SimpleGraph.fromRel fun y z => ∃ k, (X.slots.base.target (y, k)).1 = z

end Panels

/-! ## The layout bit as an integer comparison (paper, Energy scores) -/

/-- `31/(80 q_e)` for OpenAI's relative masses `q = ![8/31, 4/31, 40/93, 16/31]` (ShrinkMotifGraph.lean:68). -/
def layoutCoeff : Fin 4 → ℕ := ![10, 20, 6, 5]

/-- Each group energy (ShrinkEnergy.lean:28) is `31/(80 p)` times an integer sum. -/
theorem groupEnergy_eq {M : Type*} [Fintype M] {p : ℝ} (hp : 0 < p) (w : M → Bool → Fin 4 → ℕ)
    (l : Bool) :
    groupEnergy p (fun e ↦ (relativeMass e : ℝ)) w l =
      (31 / (80 * p)) * ((∑ m, ∑ e, layoutCoeff e * w m l e ^ 2 : ℕ) : ℝ) := by
  have hp' : p ≠ 0 := hp.ne'
  unfold groupEnergy
  rw [Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  fin_cases e <;> simp [relativeMass, layoutCoeff] <;> field_simp <;> ring

/-- `chosenLayout` (ShrinkEnergy.lean:33) compares two real energies; it is the comparison of two integer sums.
Ties give `false` (paper layout 1). PROVED (the same proof was first checked locally on copies of the definitions). -/
theorem chosenLayout_eq_int {M : Type*} [Fintype M] {p : ℝ} (hp : 0 < p) (w : M → Bool → Fin 4 → ℕ) :
    chosenLayout p (fun e ↦ (relativeMass e : ℝ)) w =
      decide (∑ m, ∑ e, layoutCoeff e * w m true e ^ 2 < ∑ m, ∑ e, layoutCoeff e * w m false e ^ 2) := by
  have hc : (0 : ℝ) < 31 / (80 * p) := by positivity
  unfold chosenLayout
  rw [groupEnergy_eq hp, groupEnergy_eq hp]
  by_cases h : (∑ m, ∑ e, layoutCoeff e * w m false e ^ 2) ≤ ∑ m, ∑ e, layoutCoeff e * w m true e ^ 2
  · have hle : (31 / (80 * p)) * ((∑ m, ∑ e, layoutCoeff e * w m false e ^ 2 : ℕ) : ℝ) ≤
        (31 / (80 * p)) * ((∑ m, ∑ e, layoutCoeff e * w m true e ^ 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h) hc.le
    rw [if_pos hle]
    exact (decide_eq_false (not_lt.mpr h)).symm
  · have hlt : (∑ m, ∑ e, layoutCoeff e * w m true e ^ 2) < ∑ m, ∑ e, layoutCoeff e * w m false e ^ 2 :=
      not_le.mp h
    have hnle : ¬ (31 / (80 * p)) * ((∑ m, ∑ e, layoutCoeff e * w m false e ^ 2 : ℕ) : ℝ) ≤
        (31 / (80 * p)) * ((∑ m, ∑ e, layoutCoeff e * w m true e ^ 2 : ℕ) : ℝ) :=
      not_le.mpr (mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hc)
    rw [if_neg hnle]
    exact (decide_eq_true hlt).symm

/-! ## One shrinking substep -/

section Shrink

/-- The same classical equality test on bases that ShrinkStatePass.lean:27 uses. -/
noncomputable local instance instDecEqBase {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

/-- (P3) term data: the admitted outer index chosen for each motif whose old wire leaves base `y`, keyed by the
wire's out-slot, tag, remaining lane, colour bits and slot label (`none` for thick-thick wires). -/
noncomputable def choiceAt (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (y : X.Base)
    (i : Fin (2 ^ a)) (t : BitWord (packingTagBits (2 ^ a))) (l : BitWord g)
    (u : BitWord (2 * 2 ^ a + 1)) (h : BitWord a) : Option (Bool × Fin 4 → ℕ) :=
  let P := X.packingData
  let e : Arc X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1) :=
    (((y, (t, l)), i), (u, h))
  if hm : ¬ (P.thick (sourcePosition e) ∧ P.thick (sourcePosition (P.actual e))) then
    some (s ⟨e, hm⟩).val
  else none

/-- The level-ℓ data of base `y` in a shrinking substep: panel, greedy colour, greedy tag offset, term data. -/
noncomputable def shrinkData (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (y : X.Base) :=
  (panel X y, X.packingData.color y, X.packingData.offset y, choiceAt B X s y)

/-- The one global datum: the layout bit of `X.shrinkNext` (copied from ShrinkStatePass.lean:62-66). -/
noncomputable def layoutBit (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) : Bool :=
  let p := equalArcMass (Position X.Base (BitWord a) (BitWord (packingTagBits (2 ^ a)))
    (BitWord g) (2 * 2 ^ a + 1)) (2 ^ a)
  let w := X.packingData.termWidths B X.shrinkNumber X.packingWidth s
  chosenLayout p (fun e ↦ (relativeMass e : ℝ)) w

/-- The layout bit of `layoutBit` is the one used by OpenAI's next state. -/
theorem layoutBit_spec (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    X.shrinkNext B ready s =
      X.shrinkOutputState (layoutBit B X s) (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b))
        (fun m t ↦ X.packingData.termWidths B X.shrinkNumber X.packingWidth s m (layoutBit B X s) t)
        (X.shrinkStateIndex ready (layoutBit B X s)) := rfl

/-- The layout bit of a shrinking substep as an integer comparison (a global sum over all motifs). -/
theorem layoutBit_eq_int (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    layoutBit B X s =
      decide (∑ m, ∑ e, layoutCoeff e * X.packingData.termWidths B X.shrinkNumber X.packingWidth s m true e ^ 2 <
        ∑ m, ∑ e, layoutCoeff e * X.packingData.termWidths B X.shrinkNumber X.packingWidth s m false e ^ 2) := by
  dsimp only [layoutBit]
  apply chosenLayout_eq_int
  unfold equalArcMass
  exact div_pos one_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr (Nat.two_pow_pos a)))

/-- New addresses are product addresses (paper rem:G1): `addr (x, j) = J * addr x + j`. -/
theorem shrink_addr (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) (x : X.Base)
    (j : BitWord (packingTagBits (2 ^ a))) :
    addr (X.shrinkNext B ready s) (x, j) =
      2 ^ packingTagBits (2 ^ a) * addr X x + (bitWordFinEquiv (packingTagBits (2 ^ a)) j : ℕ) := by
  have h : addr (X.shrinkNext B ready s) (x, j) =
      (bitWordFinEquiv (packingTagBits (2 ^ a)) j : ℕ) + 2 ^ packingTagBits (2 ^ a) * addr X x := rfl
  rw [h, Nat.add_comm]

end Shrink

/-! ## The greedy data (paper C5, C6) -/

section Greedy

open SlotGraph

variable {V : Type*} {d N : ℕ}

theorem foldl_update_of_not_mem {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (select : V → (V → A) → A) (ids : List (Fin N)) (f : V → A) (y : V) (hy : order y ∉ ids) :
    ids.foldl (orderedUpdate order select) f y = f y := by
  induction ids generalizing f with
  | nil => rfl
  | cons i ids ih =>
    rw [List.foldl_cons, ih _ (fun h => hy (List.mem_cons.mpr (Or.inr h)))]
    have hne : y ≠ order.symm i := by
      intro h
      apply hy
      rw [h, Equiv.apply_symm_apply]
      exact List.mem_cons.mpr (Or.inl rfl)
    simp only [orderedUpdate, Function.update_of_ne hne]

theorem foldl_update_sorted {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (select : V → (V → A) → A) (ids : List (Fin N)) (hs : ids.Pairwise (· < ·))
    (f : V → A) (x : V) (hx : order x ∈ ids) :
    ids.foldl (orderedUpdate order select) f x =
      select x (fun y => if order y ∈ ids ∧ order y < order x then
        ids.foldl (orderedUpdate order select) f y else f y) := by
  induction ids generalizing f with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons i rest ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hlt, hrest⟩ := hs
    have hi : i ∉ rest := fun h => lt_irrefl i (hlt i h)
    rcases List.mem_cons.mp hx with hxi | hxr
    · have hxr : order x ∉ rest := hxi ▸ hi
      have hxs : x = order.symm i := by rw [← hxi, Equiv.symm_apply_apply]
      have hfun : (fun y => if order y ∈ i :: rest ∧ order y < order x then
          (i :: rest).foldl (orderedUpdate order select) f y else f y) = f := by
        funext y
        rw [if_neg]
        rintro ⟨hm, hl⟩
        rcases List.mem_cons.mp hm with h | h
        · rw [h, hxi] at hl; exact lt_irrefl _ hl
        · rw [hxi] at hl; exact lt_asymm hl (hlt _ h)
      rw [hfun, List.foldl_cons, foldl_update_of_not_mem order select rest _ x hxr]
      simp only [orderedUpdate, hxs, Function.update_self]
    · rw [List.foldl_cons, ih hrest _ hxr]
      congr 1
      funext y
      by_cases hy : order y = i
      · have hyr : order y ∉ rest := hy ▸ hi
        have hyx : order y < order x := hy ▸ hlt _ hxr
        rw [if_neg (fun h => hyr h.1), if_pos ⟨List.mem_cons.mpr (Or.inl hy), hyx⟩,
          foldl_update_of_not_mem order select rest _ y hyr]
      · have hys : y ≠ order.symm i := by
          intro h; apply hy; rw [h, Equiv.apply_symm_apply]
        have hmem : (order y ∈ i :: rest) ↔ order y ∈ rest := by
          rw [List.mem_cons]; exact ⟨fun h => h.resolve_left hy, Or.inr⟩
        by_cases hc : order y ∈ rest ∧ order y < order x
        · rw [if_pos hc, if_pos ⟨hmem.mpr hc.1, hc.2⟩]
        · rw [if_neg hc, if_neg (fun h => hc ⟨hmem.mp h.1, h.2⟩)]
          simp only [orderedUpdate, Function.update_of_ne hys]

/-- A scan in base order: the final value at `x` is the selection rule applied to the table holding the final
values of the earlier vertices and the initial value at the later ones. -/
theorem foldl_orderedUpdate_local {A : Type*} [DecidableEq V] (order : V ≃ Fin N)
    (select : V → (V → A) → A) (init : A) (x : V) :
    (List.finRange N).foldl (orderedUpdate order select) (fun _ ↦ init) x =
      select x (fun y => if order y < order x then
        (List.finRange N).foldl (orderedUpdate order select) (fun _ ↦ init) y else init) := by
  rw [foldl_update_sorted order select _ (List.sortedLT_finRange N).pairwise _ x (List.mem_finRange _)]
  congr 1
  funext y
  simp only [List.mem_finRange, true_and]

/-- OpenAI's greedy colour (SlotGreedyScan.lean:182) obeys a rule that reads the colours of the neighbours only:
earlier neighbours with their final colour, later neighbours with the initial colour 0. PROVED. -/
theorem orderedColor_local (G : SlotGraph V d) (order : V ≃ Fin N) (x : V) :
    G.orderedColor order x =
      G.chooseColor x (fun y => if order y < order x then G.orderedColor order y else 0) := by
  classical
  rw [G.orderedColor_fold order]
  exact foldl_orderedUpdate_local order G.chooseColor 0 x

/-- The same for the greedy tag offsets (SlotGreedyScan.lean:235), with initial offset 0. PROVED. -/
theorem orderedTagOffsets_local {Tag : Type*} [AddCommGroup Tag] {J : ℕ} (G : SlotGraph V d)
    (order : V ≃ Fin N) (index : Tag ≃ Fin J) (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < J) (x : V) :
    G.orderedTagOffsets order index τ hcard x =
      G.chooseTag index τ hcard x
        (fun y => if order y < order x then G.orderedTagOffsets order index τ hcard y else 0) := by
  classical
  rw [G.orderedTagOffsets_fold order index τ hcard]
  exact foldl_orderedUpdate_local order (G.chooseTag index τ hcard) 0 x

end Greedy

/-! ## One refresh substep -/

section Refresh

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)

/-- New addresses after a refresh: `addr (x, j) = 2^a * addr x + j`. -/
theorem refresh_addr (X : State a (a + g)) (c : DyadicRefreshChoice X P hdH hconn F) (x : X.Base)
    (j : Fin (2 ^ a)) :
    addr (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j) = 2 ^ a * addr X x + (j : ℕ) := by
  have h : addr (dyadicRefreshNext X P hdH hconn F hD hd c) (x, j) = (j : ℕ) + 2 ^ a * addr X x := rfl
  rw [h, Nat.add_comm]

end Refresh

end P1P7
