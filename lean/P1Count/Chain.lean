import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# P1Count.Chain: the λ-chain identity (task P9, target (2), lane P1-lean-W2-count)

Problem P1, Case 2. The compressor is run over a finite `F₂`-algebra `F` (lane wrap, task P0:
`P1Wrap.finite_subalgebra`, `P1Wrap.exists_functional` gives `l : F →ₗ[ZMod 2] ZMod 2` with `l 1 = 1`).
The vertex tensors `W_v` lie in `F`, not in `F₂`, so the parity count needs `l (∏_v W_v)`, and `l` is not
multiplicative. Fix a basis `b` of `F` over `F₂`, indexed by `Fin D`. Multiplication by `a` has the
matrix `mulEntry b a j j'` (coefficient of `b j'` in `a * b j`). Expanding the matrix product,
`l (W_{P-1} ⋯ W_0 · x)` is the sum over index chains `j 0, …, j P` of
`(b.repr x (j 0)) · ∏_i mulEntry b (W_i) (j i) (j (i+1)) · l (b (j P))` (`lambda_expand`).
All entries are in `F₂`, so the sum is the parity of the number of chains whose entries are all `1`
(`lambda_chain`). Each link condition reads one `W_i` and two consecutive chain entries; the two end
conditions read fixed tables of `F` (`b.repr 1`, `l ∘ b`). So the verifier checks the chain locally:
one check per link (it evaluates `W_i` in coordinates), and one check per end.

Mathlib only.
STATUS (P1-lean-W2-count, 09:45Z wind-down): COMPLETE DRAFT, no `sorry`, NOT YET COMPILED (project p1-count
became ready 09:41Z). First job after the restart: `lake build P1Count.Bookkeeping` (builds Chain too).
-/

namespace P1Count

open Module

noncomputable section

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {D : ℕ}

/-- Entry `(j, j')` of the matrix of multiplication by `a` in the basis `b`: the coefficient of
`b j'` in `a * b j`. -/
def mulEntry (b : Basis (Fin D) (ZMod 2) F) (a : F) (j j' : Fin D) : ZMod 2 :=
  b.repr (a * b j) j'

/-- The weight of the index chain `j 0, …, j P` that starts at `x`, for the factors `w 0, …, w (P-1)`. -/
def chainWeight (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (x : F) {P : ℕ}
    (w : Fin P → F) (j : Fin (P + 1) → Fin D) : ZMod 2 :=
  b.repr x (j 0) * (∏ i : Fin P, mulEntry b (w i) (j i.castSucc) (j i.succ)) *
    l (b (j (Fin.last P)))

/-- **The chain check.** The chain `j 0, …, j P` passes iff the start entry, every link and the end
entry are `1`. Link `i` reads only `w i`, `j i` and `j (i + 1)`. -/
def ChainOK (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ} (w : Fin P → F)
    (j : Fin (P + 1) → Fin D) : Prop :=
  b.repr 1 (j 0) = 1 ∧ (∀ i : Fin P, mulEntry b (w i) (j i.castSucc) (j i.succ) = 1) ∧
    l (b (j (Fin.last P))) = 1

/-- Coordinates of a product: `b.repr (a * x) j' = ∑_j (b.repr x j) · mulEntry b a j j'`. -/
theorem repr_mul_apply (b : Basis (Fin D) (ZMod 2) F) (a x : F) (j' : Fin D) :
    b.repr (a * x) j' = ∑ j, b.repr x j * mulEntry b a j j' := by
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, mulEntry]

/-- `l x = ∑_d (b.repr x d) · l (b d)`. -/
theorem functional_expand (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (x : F) :
    l x = ∑ d, b.repr x d * l (b d) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, smul_eq_mul]

/-- **λ-expansion.** `l ((∏_i w i) · x)` is the sum of the chain weights. -/
theorem lambda_expand (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) :
    ∀ (P : ℕ) (x : F) (w : Fin P → F),
      l ((∏ i, w i) * x) = ∑ j : Fin (P + 1) → Fin D, chainWeight b l x w j
  | 0, x, w => by
    have h1 : ∑ j : Fin (0 + 1) → Fin D, chainWeight b l x w j = ∑ d, b.repr x d * l (b d) :=
      Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin D)) _ _ (fun j => by
        simp only [chainWeight, Fin.prod_univ_zero, mul_one]
        rfl)
    rw [h1, Fin.prod_univ_zero, one_mul]
    exact functional_expand b l x
  | P + 1, x, w => by
    have hprod : (∏ i, w i) * x = (∏ i : Fin P, w i.succ) * (w 0 * x) := by
      rw [Fin.prod_univ_succ]; ring
    rw [hprod, lambda_expand b l P (w 0 * x) (fun i => w i.succ)]
    symm
    rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin D)
      (fun p => chainWeight b l x w (Fin.cons p.1 p.2)) _ (fun p => rfl)]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [chainWeight, repr_mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]
    rw [show Fin.last (P + 1) = (Fin.last P).succ from rfl, Fin.cons_succ]
    ring

/-- `l (∏_i w i) = ∑_j chainWeight b l 1 w j`. -/
theorem lambda_expand_one (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ}
    (w : Fin P → F) : l (∏ i, w i) = ∑ j : Fin (P + 1) → Fin D, chainWeight b l 1 w j := by
  rw [← lambda_expand b l P 1 w, mul_one]

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- In `ZMod 2`, `a = if a = 1 then 1 else 0`. -/
theorem zmod2_eq_ite (a : ZMod 2) : a = if a = 1 then 1 else 0 := by
  rcases zmod2_cases a with h | h <;> simp [h]

/-- In `ZMod 2`, a product is `1` iff every factor is `1`, and `0` otherwise. -/
theorem prod_zmod2 {ι : Type*} [Fintype ι] (f : ι → ZMod 2) [Decidable (∀ i, f i = 1)] :
    ∏ i, f i = if ∀ i, f i = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => h i
  · obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases zmod2_cases (f i) with h0 | h1
    · exact h0
    · exact absurd h1 hi

open scoped Classical in
/-- The chain weight is the indicator of the chain check. -/
theorem chainWeight_one_eq (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ}
    (w : Fin P → F) (j : Fin (P + 1) → Fin D) :
    chainWeight b l 1 w j = if ChainOK b l w j then 1 else 0 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  unfold chainWeight ChainOK
  rw [prod_zmod2]
  rcases zmod2_cases (b.repr 1 (j 0)) with h0 | h0 <;>
    rcases zmod2_cases (l (b (j (Fin.last P)))) with h1 | h1 <;>
    by_cases hl : ∀ i : Fin P, mulEntry b (w i) (j i.castSucc) (j i.succ) = 1 <;>
    simp [h0, h1, hl, h01]

open scoped Classical in
/-- **P9 (2), `lambda_chain`.** For a basis `b` of `F` over `F₂` and any `F₂`-linear `l : F → F₂`,
`l (∏_i w i)` is the parity of the number of index chains `j 0, …, j P` that pass the chain check
`ChainOK` (start entry, every link `mulEntry b (w i) (j i) (j (i+1))`, end entry all `1`). -/
theorem lambda_chain (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) {P : ℕ}
    (w : Fin P → F) :
    l (∏ i, w i) = ((Finset.univ.filter fun j : Fin (P + 1) → Fin D => ChainOK b l w j).card :
      ZMod 2) := by
  rw [lambda_expand_one, Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun j _ => chainWeight_one_eq b l w j

end

end P1Count
