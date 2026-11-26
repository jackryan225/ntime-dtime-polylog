import P1ProgDir.C4Final
import P1SolFmt.Fmt4

/-!
# P1ProgDir.C4Genuine: the program of check C4 at the GENUINE dims, with no open input

Lane P1-lean-checks (2026-11-25). `P1ProgDir.progC4` (C4Final.lean) needs only `P1ChkDir.FmtHyp4 dims`; the Sol prover
P1-sol-fmt4 proved it at the genuine C4 dims (`P1SolFmt.fmtHyp4_genuine`, file ChkFinal/P1SolFmt/Fmt4.lean, sha256
c82187ef929921cf96a2b2b535b80a95dcaccb8fa10afe8c8236b872df2a8650, copied unchanged; statement = the owner's exact text,
ORG/briefs/P1-sol-fmt4.md, checked by example in job chkdir-45). Genuine C4 dims at input length `n`: the P6 format
`P1Wit.SolSpace.genuineDims` at `t = lpTime a b n`, `g = a (n^2 + 1)`; `h = P1Wrap.Params.h t`; the payload widths of
`P1Net.rnState` (`Wc = Ws = strWidth V (Params.B t)`, `Wt = tupWidth V (Params.B t)`).
-/

namespace P1ProgDir

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- The genuine C4 dims at input length `n`. -/
noncomputable abbrev genuineC4Dims {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) (n : ℕ) : P1ChkDir.C4Dims :=
  { D := P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias
    h := P1Wrap.Params.h (P1Int.lpTime a b n)
    Wc := P1Net.strWidth V (P1Wrap.Params.B (P1Int.lpTime a b n))
    Ws := P1Net.strWidth V (P1Wrap.Params.B (P1Int.lpTime a b n))
    Wt := P1Net.tupWidth V (P1Wrap.Params.B (P1Int.lpTime a b n)) }

/-- **Check C4, program, at the genuine dims: no open input.** For every degree exponent `e` with `4 ≤ 2^e` and every
fixed tape numbering `τ`. -/
theorem progC4_genuine {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
    (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) {e : ℕ} (ha : 4 ≤ 2 ^ e) (τ : V.K → ℕ) :
    P1ChkDir.ProgC4 ha τ (genuineC4Dims A Kc V aM a b d bigBias termBias) :=
  progC4 ha τ _ (P1SolFmt.fmtHyp4_genuine A Kc V aM a b d bigBias termBias)

end P1ProgDir

#print axioms P1ProgDir.progC4_genuine
