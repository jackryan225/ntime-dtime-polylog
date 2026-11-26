import P1P5.LevelsPolyDefs
import P1P5.LevPoly

/-! # P1, P8a in `Poly` form: `runLevels_poly` (definitions in LevelsPolyDefs.lean).
PROVED by Sol P1-sol-levpoly (P1ProgEng.runLevels_poly', file P1P5/LevPoly.lean = the Sol file P1ProgEng/LevPoly.lean
UNCHANGED, sha256 e0999980..f97f, runner DONE 12:20:54Z); the statement below is the one compiled with `sorry` in job eval-4. -/

namespace P1P5

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter

noncomputable section

variable {R : Type} [CommRing R] [Fintype R]

/-- **Level evaluation in `Poly` form.** -/
theorem runLevels_poly :
    ∃ val : List (List (List (Label R × List Tally))) × List (Label R) → List (Label R), Poly val ∧
      ∀ (Ls : List (Level R)) (st : List R),
        val (Ls.map encLevel, st.map Label.mk) = (runLevels Ls st).map Label.mk :=
  P1ProgEng.runLevels_poly'

/-! Small cases of the statement (no levels: the state is returned; one empty level: the empty state). -/

example (st : List R) : (runLevels ([] : List (Level R)) st).map Label.mk = st.map Label.mk := rfl

example (st : List R) : (runLevels [([] : Level R)] st).map Label.mk = [] := rfl

example (st : List R) (K : R) :
    runLevels [[[(K, [])]]] st = [K] := by
  simp [runLevels, stepEval, entryEval]

end

end P1P5

#print axioms P1P5.runLevels_poly
