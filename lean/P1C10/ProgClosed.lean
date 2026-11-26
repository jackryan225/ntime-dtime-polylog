import P1SolC10P.Program
import P1SolC10P.Rounds
import P1SolC10P.RcCases

/-!
# P1, check C10: the bit program, closed (lane P1-lean-c10)

The Sol prover P1-sol-c10prog proved the three program targets of `P1C10/Prog.lean` (folder P1SolC10P/, 10 files compiled
UNCHANGED, sha256 list research/p1/lean/C10/accepted/P1SolC10P.sha256). Statement checks: the delivered theorems have
exactly the target types.
-/

namespace P1C10

theorem checkRounds_proved : CheckRoundsTarget := P1SolC10P.checkRounds

theorem rcCases_proved : RcCasesTarget := P1SolC10P.rcCasesPoly

/-- **Family 9 (C10) as a program** in the D8 form, from the format inputs, the length word and the two recomputations. -/
theorem progC10_proved : ProgC10Target := P1SolC10P.progC10

end P1C10
