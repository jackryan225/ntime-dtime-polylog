import P1P5.EvalDefs
import OAI.Computability.MultitapeWeakETH.StackInterpreter
import OAI.Computability.IntegerMultiplication.Code.Loop

/-!
# P1, P8a in OpenAI's `Poly` form (route S1/D13): the level evaluation of a cone

`runLevels` (EvalDefs.lean) evaluates the pushed factor `W_v` level by level from the cone tables
(`P1P5.Wv_eq_runO`: `chainPush c F v z = (runLevels (encLevelsO c o) (stateOfO ..)).getD (fin.idxOf (v, z)) 0`
for any good orders). Its register-program form is `P1P5.Wv_evalO` (ProgEng `Prog`); the check C13link and the
cone program (`WHyp`) are `Code.Task`s, so they need the same evaluation in OpenAI's `Poly` calculus:

* `encLevel L`: a level in codec form, kernel values as ring letters `Label R`, pointers as tallies;
* the statement `runLevels_poly` is in LevelsPoly.lean (this file has only the definitions, so that a prover
  can import them).

Builds only in a project with the `MultitapeWeakETH` closure (p1-oai and clones).
-/

namespace P1P5

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter

noncomputable section

variable {R : Type} [CommRing R] [Fintype R]

/-- A level in OpenAI's codec form: kernel values as ring letters, pointers as tallies. -/
def encLevel (L : Level R) : List (List (Label R × List Tally)) :=
  L.map (List.map fun p => (Label.mk p.1, p.2.map tally))

end

end P1P5
