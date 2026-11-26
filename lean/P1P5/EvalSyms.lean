import P1P5.EvalCorrect
import P1P5.EvalExec
import OAI.Computability.IntegerMultiplication.TMProgram

/-!
# P1: the symbols of the register evaluator (owner P1-lean-eval, 14:50Z)

Definitions MOVED UNCHANGED from P1P5/EvalProg.lean (same names, same text): the alphabet `EvalSym R = R ⊕ Tok` and the
unary encodings `encPtr`, `encPair`, `encEntry`, `encState`. EvalProg.lean imports this file, so every user of EvalProg sees
the same constants. Files that need only these symbols (the Sol factor0 files, P1SolFactor/Specification.lean) import this
file instead of EvalProg, whose `encLevel` (register form) has the same name as `P1P5.encLevel` of LevelsPolyDefs.lean (Poly
form, used by the cone program); the two cannot be imported together.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication

open scoped Classical

noncomputable section

/-- Tokens of the encoding: a unary digit and four end markers. -/
abbrev Tok := Fin 5

def Tok.one : Tok := 0
def Tok.endPtr : Tok := 1
def Tok.endPair : Tok := 2
def Tok.endEntry : Tok := 3
def Tok.endLevel : Tok := 4

/-- Alphabet of the evaluator. -/
abbrev EvalSym (R : Type) := R ⊕ Tok

variable {R : Type} [CommRing R]

def encPtr (i : ℕ) : List (EvalSym R) := List.replicate i (.inr Tok.one) ++ [.inr Tok.endPtr]

def encPair (p : R × List ℕ) : List (EvalSym R) :=
  .inl p.1 :: (p.2.flatMap encPtr ++ [.inr Tok.endPair])

def encEntry (e : List (R × List ℕ)) : List (EvalSym R) := e.flatMap encPair ++ [.inr Tok.endEntry]

def encState (st : List R) : List (EvalSym R) := st.map .inl

end

end P1P5
