import P1ChkFinal.Wired
import P1ChkFinal.Skeleton
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-!
# P1, wave 2: the check programs of families 10-13 (lane P1-lean-W2-chkfinal), STATEMENTS (proofs open)

Form (G3-chief D8 + `P1Dispatch.ofTask`, board 11:05Z): an OpenAI `Task` over `Ltr` whose query is the tree
`send (x, u, ρ)` and whose reply is `send (decide (Ck x u (bval ρ)))`; `ofTask` turns it into a `Prog Rc` on the raw
registers. Domain: triples with `|u| = M |x|` and `|ρ| = K |x|` (so the bound holds on EVERY witness of the right
length, malformed ones included, G3 rule (5)). Budget: linear in `|x| + |u| + |ρ|` plus a polynomial in
`log |x| + |ρ|` (`budget c`).

Interfaces (explicit hypotheses, exact text; owners in brackets):
* `BatchHyp` = the statement of `P1Batch.batch_lookup` [P1-lean-W2-batch];
* `LenHyp`: the binary length word of `x` (`Nat.bits |x|`, LSB first) in linear time [OpenAI `Carry`, as in
  `P1Wrap.W3.PT`];
* `FmtHyp dims`: the format numbers that these checks need, `fmt (dims n)`, are `Poly` in the binary word of `n`
  [P6 / P10: the format is computable from `n`];
* C13link only: `WHyp`: the coordinates of `W_v(z|_v; ι(u))` in the basis `b` (one bit per basis vector) are
  computed from `(x, u, v)` within the budget [P5 `Wv_eval` / `kernel_entry_eval`, ProgEng].
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module

open scoped Classical

/-- A query `(x, u, ρ)`. -/
abbrev Qry := List Bool × List Bool × List Bool

/-- The domain of a check program: `|u| = M |x|`, `|ρ| = K |x|`. -/
def QDom (M K : ℕ → ℕ) : Type := {p : Qry // p.2.1.length = M p.1.length ∧ p.2.2.length = K p.1.length}

/-- The budget: linear in the input, plus `(log |x| + |ρ| + 1)^c`. -/
def budget (c : ℕ) (p : Qry) : ℕ :=
  p.1.length + p.2.1.length + p.2.2.length + (Nat.log 2 (p.1.length + 1) + p.2.2.length + 1) ^ c

/-- The binary length word of a list, in linear time. -/
def LenHyp : Prop := Computes (fun x : List Bool => x.length) (fun x : List Bool => Nat.bits x.length)

/-- The format numbers used by checks C11-C13 (as binary words, LSB first): number of final bases, arcs per final
base, slots, lanes, the offsets and widths of the sections `Ω`, `width` (final level), `chain`, the length of the
fixed part, `chainLen`. -/
def fmt (D : Dims) : List (List Bool) :=
  [finN D, finArcs D, (D.lv D.top).slots, (D.lv D.top).lanes, D.off D.secOmega, D.width D.secOmega,
    D.off (secLev D.top .width), D.width (secLev D.top .width), D.off D.secChain, D.width D.secChain,
    D.fixedLen, D.chainLen].map Nat.bits

/-- [P6 / P10] The format numbers are polynomial-time in the binary word of `n`. -/
def FmtHyp (dims : ℕ → Dims) : Prop := Poly (fun w : List Bool => fmt (dims (P1Batch.bval w)))

/- Family 11 (C12), program: the statement `P1ChkFinal.progC12` (text unchanged) moved to
`P1ChkFinal/ProgC12.lean` (lane P1-lean-checks, 2026-11-25T12:05Z); its proof is the Sol delivery
`P1ChkFinal.SolFinal.progC12` (folder P1SolFinal/, copied unchanged), which imports this file. -/

namespace SolFinal

/-- INTEGRATION SHIM (lane P1-lean-checks, 12:08Z). The Sol prover P1-sol-finalprog compiled its files against the
earlier text of `LenHyp`, with the skeleton's word `bin |x|` in place of Mathlib's `Nat.bits |x|`. Inside the namespace
`P1ChkFinal.SolFinal` the name `LenHyp` resolves to this definition, so the Sol files compile UNCHANGED; the
consumer `P1ChkFinal.progC12` (file ProgC12.lean) converts with `P1ChkFinal.lenHyp_bin` (`bin = Nat.bits`). -/
def LenHyp : Prop := Computes (fun x : List Bool => x.length) (fun x : List Bool => bin x.length)

end SolFinal

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- The coordinates of an element of `F` in the basis `b`, one bit per basis vector. -/
noncomputable def coords (b : Basis (Fin Dd) (ZMod 2) F) (w : F) : List Bool :=
  List.ofFn fun j : Fin Dd => decide (b.repr w j = 1)

end P1ChkFinal
