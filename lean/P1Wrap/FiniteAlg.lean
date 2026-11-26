import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-!
# P0: from the algebraic closure of `F_2` to a finite algebra (task P0 of research/g3/leanplan/PLAN.md)

Case 2 needs a solution `κ : Entry → k` of OpenAI's template equations (finitely many integral polynomials) over a field
`k` of characteristic two; the port patch gives it for `k = AlgebraicClosure (ZMod 2)`. The values of `κ` generate a FINITE
`F_2`-subalgebra `F` (`finite_subalgebra`), the solution lives in `F` (`isSolution_restrict`, a statement about any family
of integral polynomials; OpenAI's `Templates.IsSolution` is of exactly this form: `∀ o, eval₂Hom (Int.castRingHom R) f
(P.equation o) = 0`), and there is an `F_2`-linear functional `λ : F → F_2` with `λ 1 = 1` (`exists_functional`).
Mathlib only.
-/

namespace P1Wrap

noncomputable section

/-- The subalgebra generated over `F_2` by the values of `κ`. -/
abbrev Fsub {ι : Type*} (κ : ι → AlgebraicClosure (ZMod 2)) : Subalgebra (ZMod 2) (AlgebraicClosure (ZMod 2)) :=
  Algebra.adjoin (ZMod 2) (Set.range κ)

/-- `κ` with values in `Fsub κ`. -/
def kappaF {ι : Type*} (κ : ι → AlgebraicClosure (ZMod 2)) (i : ι) : Fsub κ :=
  ⟨κ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩

theorem val_kappaF {ι : Type*} (κ : ι → AlgebraicClosure (ZMod 2)) (i : ι) :
    ((kappaF κ i : Fsub κ) : AlgebraicClosure (ZMod 2)) = κ i := rfl

/-- P0(a): the subalgebra is a finite-dimensional `F_2`-space. -/
instance moduleFinite_Fsub {ι : Type*} [Finite ι] (κ : ι → AlgebraicClosure (ZMod 2)) :
    Module.Finite (ZMod 2) (Fsub κ) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range κ)
    (fun x _ => Algebra.IsIntegral.isIntegral x)

/-- P0(a): `Finite (Algebra.adjoin (ZMod 2) (Set.range κ))`. -/
theorem finite_subalgebra {ι : Type*} [Finite ι] (κ : ι → AlgebraicClosure (ZMod 2)) :
    Finite (Algebra.adjoin (ZMod 2) (Set.range κ)) :=
  Module.finite_of_finite (ZMod 2)

/-- A nonzero algebra over a field has a linear functional with value `1` at `1`. -/
theorem exists_functional_one {k A : Type*} [Field k] [Ring A] [Nontrivial A] [Algebra k A] :
    ∃ l : A →ₗ[k] k, l 1 = 1 := by
  have h1 : (1 : A) ≠ 0 := one_ne_zero
  have h2 : ¬ ∀ φ : Module.Dual k A, φ 1 = 0 :=
    fun h => h1 ((Module.forall_dual_apply_eq_zero_iff k (1 : A)).1 h)
  obtain ⟨φ, hφ⟩ := not_forall.mp h2
  refine ⟨(φ 1)⁻¹ • φ, ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]

/-- P0(b): `∃ λ : F →ₗ[ZMod 2] ZMod 2, λ 1 = 1` for `F = Algebra.adjoin (ZMod 2) (Set.range κ)`. -/
theorem exists_functional {ι : Type*} (κ : ι → AlgebraicClosure (ZMod 2)) :
    ∃ l : Algebra.adjoin (ZMod 2) (Set.range κ) →ₗ[ZMod 2] ZMod 2, l 1 = 1 :=
  exists_functional_one

/-- Integral polynomial equations descend along an injective ring map. -/
theorem eval_zero_of_injective {σ O F L : Type*} [CommRing F] [CommRing L]
    (E : O → MvPolynomial σ ℤ) (φ : F →+* L) (hφ : Function.Injective φ) (f : σ → F)
    (h : ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom L) (fun i => φ (f i)) (E o) = 0) :
    ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom F) f (E o) = 0 := by
  intro o
  apply hφ
  rw [map_zero, MvPolynomial.map_eval₂Hom]
  have e : φ.comp (Int.castRingHom F) = Int.castRingHom L := RingHom.ext_int _ _
  rw [e]
  exact h o

/-- P0(c): a solution of any family of integral polynomial equations in the closure is a solution in `Fsub κ`.
(OpenAI's `Templates.IsSolution f := ∀ o, eval₂Hom (Int.castRingHom R) f (P.equation o) = 0`; the OAI form is
`P1Wrap.isSolution_kappaF` in `SolutionTransfer.lean`.) -/
theorem isSolution_restrict {ι O : Type*} (κ : ι → AlgebraicClosure (ZMod 2)) (E : O → MvPolynomial ι ℤ)
    (h : ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom (AlgebraicClosure (ZMod 2))) κ (E o) = 0) :
    ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom (Fsub κ)) (kappaF κ) (E o) = 0 :=
  eval_zero_of_injective E (Fsub κ).val.toRingHom Subtype.val_injective (kappaF κ) h

/-- P0 packaged: a finite `F_2`-algebra carrying a solution and a functional with `λ 1 = 1`. -/
theorem finite_model {ι O : Type*} [Finite ι] (κ : ι → AlgebraicClosure (ZMod 2)) (E : O → MvPolynomial ι ℤ)
    (h : ∀ o, MvPolynomial.eval₂Hom (Int.castRingHom (AlgebraicClosure (ZMod 2))) κ (E o) = 0) :
    Finite (Fsub κ) ∧ (∀ o, MvPolynomial.eval₂Hom (Int.castRingHom (Fsub κ)) (kappaF κ) (E o) = 0) ∧
      ∃ l : Fsub κ →ₗ[ZMod 2] ZMod 2, l 1 = 1 :=
  ⟨finite_subalgebra κ, isSolution_restrict κ E h, exists_functional κ⟩

end

end P1Wrap
