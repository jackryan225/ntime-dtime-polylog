import P1Wrap.FiniteAlg
import OAI.Computability.VPVNP.CompressionTemplates

/-!
# P0(c) in OpenAI's terms: a template solution over the closure of `F_2` restricts to a finite algebra

R-tier (needs OpenAI's `CompressionTemplates`, in the closure of p1-base). The proof is the Mathlib-only
`P1Wrap.finite_model` applied to `P.equation`.
-/

namespace P1Wrap

open OAI.Computability.VPVNP

/-- P0: for a solution `κ` of the joint template system over `AlgebraicClosure (ZMod 2)`, the subalgebra
`F = Algebra.adjoin (ZMod 2) (Set.range κ)` is finite, `κ` is a solution in `F`, and some `F_2`-linear
`λ : F → F_2` has `λ 1 = 1`. -/
theorem isSolution_kappaF {S : Compression.BlockSchedule (AlgebraicClosure (ZMod 2))} (P : S.Templates)
    (κ : P.Entry → AlgebraicClosure (ZMod 2)) (hκ : P.IsSolution κ) :
    Finite (Fsub κ) ∧ P.IsSolution (kappaF κ) ∧ ∃ l : Fsub κ →ₗ[ZMod 2] ZMod 2, l 1 = 1 :=
  finite_model κ P.equation hκ

end P1Wrap
