import P1ProgDir.C4ProgWired

/-!
# P1ProgDir.C4Final: the program of check C4 (family 3), integrated from the Sol prover P1-sol-c4prog

Lane P1-lean-checks (2026-11-25). The target statement (P1-lean-checks, board 11:51Z, statement file
research/p1/lean/ChkDir/P1ChkDir/C4Wired.lean, compiled chkdir-27) is proved by the delivered theorem
`P1ProgDir.SolC4.progC4` (file P1ProgDir/C4ProgWired.lean, sha256 32bcc13dab9266a4c96ce37eedb54d7841eda9ef41fa1844e668622d38f1776e;
the 21 files P1ProgDir/C4Prog*.lean are copied UNCHANGED from research/agents/P1-sol-c4prog/lean/, sha256 = DONE.md of round 2).
The only outside input is the format hypothesis `P1ChkDir.FmtHyp4 dims` (format numbers as one Poly function of the
binary word of n).
-/

namespace P1ProgDir

/-- **Check C4, program (Task form of D8), for EVERY triple `(x, u, ρ)`.** -/
theorem progC4 {K : Type} [Fintype K] [DecidableEq K] {a : Nat} (ha : 4 ≤ 2 ^ a) (τ : K → Nat)
    (dims : Nat → P1ChkDir.C4Dims) (hf : P1ChkDir.FmtHyp4 dims) : P1ChkDir.ProgC4 ha τ dims :=
  SolC4.progC4 ha τ dims hf

/-- Statement check (owner rule, board 1800): the delivered theorem has exactly the needed type. -/
example {K : Type} [Fintype K] [DecidableEq K] {a : Nat} (ha : 4 ≤ 2 ^ a) (τ : K → Nat)
    (dims : Nat → P1ChkDir.C4Dims) (hf : P1ChkDir.FmtHyp4 dims) : P1ChkDir.ProgC4 ha τ dims :=
  @SolC4.progC4 K _ _ a ha τ dims hf

end P1ProgDir

#print axioms P1ProgDir.progC4
#print axioms P1ProgDir.SolC4.progC4_D8
