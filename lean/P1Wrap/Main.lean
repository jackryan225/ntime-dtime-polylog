import P1Wrap.InnerSpec
import P1Wrap.OuterSpec

/-!
# W3 (lane wrap): `P1Int.PortWrapper` from two IMPLEMENTATION lemmas

`port_wrapper_of_impls : (∀ j a b, InnerImpl j a b) → (∀ j a b, OuterImpl j a b) → P1Int.PortWrapper`.

What remains open is pure programming with costs (no counting, no arithmetic of the separation):
* `InnerImpl j a b`: a stack program computes `innerVerdict` (parse `1^n 0 x u 0^{(p+1) m}`, compare with `n₁`,
  run the Lemma P checker `R` on `(x, u, first k guess bits)`, negate) in time `K (|withGuess w y| + 1)`.
* `OuterImpl j a b`: a stack program computes `outerVerdict` (split the guess into `u` and the rest, parse the rest as
  `encT τ ++ 0^r`, run the W1 check of `τ` against `flipM M` on `padIn x u`) in time
  `C (|w| + ν + 1) + |withGuess w x|`.
Both need `m(n) = lpM2 (sOf j) a b n`, `padLen n`, `k(n)` computed from `n` (binary arithmetic in `Prog`).
-/

namespace P1Wrap.W3

theorem port_wrapper_of_impls (hA : ∀ j a b, InnerImpl j a b) (hB : ∀ j a b, OuterImpl j a b) :
    P1Int.PortWrapper :=
  port_wrapper_of_progs (fun j a b => innerProg_of_impl (hA j a b))
    (fun j a b => outerProg_of_impl (hB j a b))

end P1Wrap.W3
