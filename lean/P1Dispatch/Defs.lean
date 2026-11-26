import P1Int.LemmaP
import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Code.Task

/-!
# P1Dispatch.Defs: from an OpenAI `Task` over trees to a check program on raw letter registers

Owner: P1-lean-dispatch (G3-chief D8, board 1593). Problem P1, Case 2, Lemma P.

The checker lanes write each check family as an OpenAI `Task` over the alphabet `Ltr`: query the tree
`send (x, u, ρ)` on top of register 0, reply `send (ck x u (bval ρ))`. The dispatcher `P1Count.R` (count lane)
runs a check program `Rc : Prog Ltr` on the RAW registers `inputRegs Ltr.bit x u ρ` (register 0 = `x`,
register 1 = `u`, register 2 = `ρ`, one letter `bit b` per bit, first bit on top; every other register
empty). This file gives the program `ofTaskProg c = conv ; c`: `conv` turns the raw registers into the tree
`send (x, u, ρ)` on register 0 (all other registers empty), then the Task program `c` runs.

`conv` uses registers 0 to 4:
1. `moveRev 0 3`, `moveRev 2 4`: move `x` to register 3 and `ρ` to register 4, reversed;
2. `build 4 0`: push `bit false`, then pop the bits of register 4 one by one, pushing `bit b` and `node`;
   this writes `spell (send ρ)` on register 0;
3. `moveRev 1 4`, `build 4 0`: the same for `u`; `push 0 node` makes `spell (send (u, ρ))`;
4. `build 3 0`, `push 0 node`: the same for `x`; register 0 is `spell (send (x, u, ρ))`.
Cost `19 (|x| + |u| + |ρ|) + 43` steps.
-/

namespace P1Dispatch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Reading of the top letter of register 0 when a program returns: `bit b` reads `b`, anything else
reads `false`. Satisfies the hypotheses of `P1Count.R_forall_iff_fam` with `letter = Ltr.bit`. -/
def answer : Option Ltr → Bool
  | some (.bit b) => b
  | _ => false

/-- One round of `moveRev s d`: if the top of register `s` is `bit b`, pop it, push `bit b` on register
`d`, and run the loop again; otherwise return. -/
def mvBody (s d : ℕ) : Cmd :=
  .look s fun o => match o with
    | some (.bit b) => .join (.pop s) (.join (.push d (.bit b)) (.again 0))
    | _ => .pass

/-- Move all bit letters of register `s` onto register `d` (the order is reversed). -/
def moveRev (s d : ℕ) : Cmd := .tie (mvBody s d)

/-- One round of `build s d`: pop `bit b` from register `s`, push `bit b` and then `node` on register `d`. -/
def bdBody (s d : ℕ) : Cmd :=
  .look s fun o => match o with
    | some (.bit b) => .join (.pop s) (.join (.push d (.bit b)) (.join (.push d .node) (.again 0)))
    | _ => .pass

/-- If register `s` holds the bits of `l` in REVERSED order, `build s d` writes `spell (send l)` on top of
register `d` and empties register `s`. -/
def build (s d : ℕ) : Cmd := .join (.push d (.bit false)) (.tie (bdBody s d))

/-- The conversion: raw letter registers `x, u, ρ` (registers 0, 1, 2) become the tree `send (x, u, ρ)` on
register 0, with registers 1 to 4 empty. -/
def conv : Cmd :=
  .join (moveRev 0 3) (.join (moveRev 2 4) (.join (build 4 0) (.join (moveRev 1 4)
    (.join (build 4 0) (.join (.push 0 .node) (.join (build 3 0) (.push 0 .node)))))))

/-- The check program of one family: the conversion, then the Task program `c`. -/
def ofTaskProg (c : Cmd) : Cmd := .join conv c

/-- `Ltr` is finite (for the `∃ (A : Type) (_ : Fintype A)` of `P1Int.LemmaP`). A `def`, not an instance,
so that it cannot clash with a local instance of another file. -/
def ltrFintype : Fintype Ltr :=
  ⟨{.node, .sep, .bit true, .bit false}, by
    intro x
    cases x with
    | bit b => cases b <;> simp
    | node => simp
    | sep => simp⟩

end P1Dispatch
