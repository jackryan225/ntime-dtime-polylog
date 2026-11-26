import P1ChkFinal.C7RFam
import P1ChkFinal.FmtAgTarget
import P1ProgDir.DirFitTarget

/-!
# P1ChkFinal.GreedyCountTarget: test T5 of D15, the index counts of the greedy families fit in `2^(k-4)` (lane P1-lean-greedy)

At the real parameters (`rD`: A = Bt, Kc = portConsts Bt, V = toOAI V, aM = 1), for long inputs, the index counts of the
families 4-8 (C5, C6, C8: `cntBase`; C7 after D15: `cnt7all` = max (cntTerm, cntRef); C9: `cntLev`) are at most
`2 ^ (lpK2 a b n - 4)`, the number of index words. Then every live index of a greedy family is `< ni` and the D5 step
quantifier `∀ i < ni, i < cnt c` covers all of them.
Why it holds (owner's estimate, to be PROVED, not assumed): level-0 bases = `2 I locCount` with `I = ⌈2^λ / (B N)⌉`,
`B N = 2^(⌊p/2⌋ + ⌊19p/2⌋)`; term keys per base `≤ 2^h 2^a` (`a` bounded by the schedule); `2^levBits ≤ 2 (top + 1)`; so
every count is `≤ c₀ (top + 1) locCount 2^λ 2^h / (B N) = O(p² 2^λ / 2^(p/2))`, below `2^(λ - 4)` for large `λ`
(`locCount = O(|K| h)`, `top = O(p)`).
-/

namespace P1ChkFinal.GreedyCount

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1SolGreedy P1Int P1Int.P11 P1ChkFinal.C7R P1ChkFinal.FmtAgTarget P1ProgDir.DirFit

/-- **T5 (statement)**: the greedy index counts fit in the index words, for long inputs, at the real parameters. -/
def GreedyCountTarget.{u} : Prop :=
  ∀ {k : Type u} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ), 1 ≤ b →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      cntBase (rD Bt V a b d bigBias termBias n) ≤ 2 ^ (lpK2 a b n - 4) ∧
      cntLev (rD Bt V a b d bigBias termBias n) ≤ 2 ^ (lpK2 a b n - 4) ∧
      cnt7all (rD Bt V a b d bigBias termBias n) (agG (rD Bt V a b d bigBias termBias) n) ≤ 2 ^ (lpK2 a b n - 4)

end P1ChkFinal.GreedyCount
