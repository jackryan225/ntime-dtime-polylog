import P1ChkDir.Stage
import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-!
# P1ChkDir.C4Wired: check C4 in the wired form of decision D5 / D8, and the STATEMENT of its program

Lane P1-lean-checks (2026-11-25). Form of lane chkfinal's `P1ChkFinal.Wired` / `Progs`: the family is a Prop
`C4w τ dims x u i` on the input `x`, the witness `u` and the index `i`; `dims n` is the fixed data at input length `n`
(`C4Dims`: the P6 format `D`, the lane bits `h`, the payload widths); the degree exponent `a` of the level-0 state
(`4 ≤ 2 ^ a`) and the tape numbering `τ` of the directory are FIXED (the same for every `n`, so that one program can
use them; in the genuine format `a = S.degreeExponent 0`).

* `dirAt D τ I N`: the directory layout of P6 (`P1ChkDir.dirP6`) with free sizes; `dirP6 D ρ = dirAt D ρ D.I D.N`
  (`dirP6_eq_dirAt`, by `rfl`), `dirTrue_dirAt` (stage 0 transfers when `D.N = N`).
* `C4w τ dims x u i`: `P1ChkDir.C4F` of `dims |x|` at index `i` (a level-0 base address); `C4w_out`, `C4w_stage`.
* `fmtBig`, `fmtSmall`, `FmtHyp4`: the format numbers that the program needs, as a hypothesis in the style of
  `P1ChkFinal.FmtHyp` (binary words for the large numbers; UNARY tallies for the numbers that bound the work:
  `2 ^ h`, `h` and the field widths).
* `ProgC4 τ dims`: the target statement (a Prop, no `sorry`): one OpenAI `Task` on the tree `send (x, u, ρ)`, for
  EVERY triple (no condition on the lengths: malformed and short witnesses included), with reply
  `send (decide (C4w τ dims x u (bval ρ)))`, within `budget c`. `P1Dispatch.ofTask` (with `q := id`) turns it into the
  program `Rc` of D8; `Task.on Subtype.val` restricts it to a domain such as `P1ChkFinal.QDom M K`.
-/

namespace P1ChkDir

open P1Net P1Wit OAI.Computability.VPVNP Compression
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

variable {K : Type}

/-! ## The directory layout with free sizes -/

/-- The directory layout of P6 (sections 0-3 of `P1Wit.Layout`) with the tape numbering `τ` and free sizes `I`, `N`.
`P1ChkDir.dirP6 D ρ` is the case `τ = ρ`, `I = D.I`, `N = D.N`. -/
def dirAt (D : Dims) (τ : K → ℕ) (I N : ℕ) : DirLayout K I N where
  cT := tritNum
  cT_ok := tritNum_ok
  tritOff i k := D.off secTrit + ((i : ℕ) * D.r + τ k) * D.width secTrit
  betaOff ι k := D.off secStart + ((ι : ℕ) * D.r + τ k) * D.width secStart
  nextOff ι k δ := D.off secNext + (((ι : ℕ) * D.r + τ k) * 3 + δ) * D.width secNext
  prevOff ι k δ := D.off secPrev + (((ι : ℕ) * D.r + τ k) * 3 + δ) * D.width secPrev
  cB := zigCode D.bigW
  cO := ownCode D.bigW I

theorem dirP6_eq_dirAt (D : Dims) (ρ : K ≃ Fin D.r) :
    dirP6 D ρ = dirAt D (fun k => (ρ k : ℕ)) D.I D.N := rfl

/-- Stage 0 for `dirAt`: if the tape numbering is `ρ` and `D.N = N`, a true directory of `dirP6 D ρ` is a true
directory of `dirAt D τ D.I N`. -/
theorem dirTrue_dirAt (D : Dims) (ρ : K ≃ Fin D.r) (τ : K → ℕ) (hτ : ∀ k, (ρ k : ℕ) = τ k) {N : ℕ}
    (hN : D.N = N) (u : List Bool) (h : DirTrue (dirP6 D ρ) u) : DirTrue (dirAt D τ D.I N) u := by
  subst hN
  have e : τ = fun k => (ρ k : ℕ) := funext fun k => (hτ k).symm
  subst e
  exact h

/-! ## The wired check -/

/-- The data of check C4 at one input length: the P6 format, the number `h` of lane bits of level 0
(`N = 2 ^ h` small intervals per big interval) and the payload widths (content, state, table tuple) of
`P1Net.stateNet`. -/
structure C4Dims where
  D : Dims
  h : ℕ
  Wc : ℕ
  Ws : ℕ
  Wt : ℕ

variable [Fintype K] [DecidableEq K] {a : ℕ}

/-- **Family 3 (C4), wired form.** At input `x`, witness `u`, index `i` (a level-0 base address): the stored
level-0 panel of base `i` equals the panel computed from the stored directory (`P1ChkDir.C4F`). -/
def C4w (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (x u : List Bool) (i : ℕ) : Prop :=
  C4F (K := K) ha (dims x.length).D
    (dirAt (dims x.length).D τ (dims x.length).D.I (2 ^ (dims x.length).h)) u
    (dims x.length).Wc (dims x.length).Ws (dims x.length).Wt i

/-- The number of indices of family 3: the level-0 bases. -/
def cnt4 (K : Type) [Fintype K] [DecidableEq K] (dims : ℕ → C4Dims) (n : ℕ) : ℕ :=
  2 * ((dims n).D.I * locCount K (dims n).h)

theorem C4w_out (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (x u : List Bool) {i : ℕ}
    (hi : cnt4 K dims x.length ≤ i) : C4w ha τ dims x u i :=
  C4F_out _ _ _ _ _ _ _ hi

/-- **Stage 2 (C4), wired form.** Once the directory is true, every index of family 3 passes iff every level-0
panel field holds the true panel of the network of the stored skeleton. -/
theorem C4w_stage (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) (x u : List Bool)
    [NeZero (dims x.length).D.I]
    (hDir : DirTrue (dirAt (K := K) (dims x.length).D τ (dims x.length).D.I (2 ^ (dims x.length).h)) u) :
    (∀ i, C4w ha τ dims x u i) ↔
      ∀ y, PanelStored (dims x.length).D u (addrL y)
        (P1P7.panel (stateNet (K := K) (dims x.length).D.I
          ((dirAt (dims x.length).D τ (dims x.length).D.I (2 ^ (dims x.length).h)).sigmaS u)
          ha (dims x.length).Wc (dims x.length).Ws (dims x.length).Wt) y) :=
  C4_stage _ _ _ _ _ _ _ hDir

/-! ## The format numbers of the program -/

/-- The large format numbers (given to the program as binary words, least significant bit first). Order:
`I`, `r`, slots and lanes of level 0, the offsets of the sections start, prev, next, the offsets of the seven
level-0 panel sections (outAddr, outDisp, outFar, inAddr, inDisp, inFar, width), and `Wc`, `Ws`, `Wt`. -/
def fmtBig (P : C4Dims) : List ℕ :=
  [P.D.I, P.D.r, (P.D.lv 0).slots, (P.D.lv 0).lanes,
    P.D.off secStart, P.D.off secPrev, P.D.off secNext,
    P.D.off (secLev 0 .outAddr), P.D.off (secLev 0 .outDisp), P.D.off (secLev 0 .outFar),
    P.D.off (secLev 0 .inAddr), P.D.off (secLev 0 .inDisp), P.D.off (secLev 0 .inFar),
    P.D.off (secLev 0 .width), P.Wc, P.Ws, P.Wt]

/-- The small format numbers (given to the program in UNARY, so that the work of the check is polynomial in the
size of the format): `2 ^ h` (lanes), `h`, and the field widths of the sections start, prev, next and of the seven
level-0 panel sections. -/
def fmtSmall (P : C4Dims) : List ℕ :=
  [2 ^ P.h, P.h,
    P.D.width secStart, P.D.width secPrev, P.D.width secNext,
    P.D.width (secLev 0 .outAddr), P.D.width (secLev 0 .outDisp), P.D.width (secLev 0 .outFar),
    P.D.width (secLev 0 .inAddr), P.D.width (secLev 0 .inDisp), P.D.width (secLev 0 .inFar),
    P.D.width (secLev 0 .width)]

/-- [P6 / P10 / integration] **The format hypothesis of the C4 program.** One polynomial-time function of the binary
word `w` of the input length `n = bval w` returns the large format numbers as binary words (any words with these
values) and the small ones as tallies. (So `2 ^ h` and the field widths are polynomial in `log n`.) -/
def FmtHyp4 (dims : ℕ → C4Dims) : Prop :=
  ∃ f : List Bool → List (List Bool) × List Tally, Poly f ∧ ∀ w : List Bool,
    (f w).1.map P1Batch.bval = fmtBig (dims (P1Batch.bval w)) ∧
      (f w).2.map List.length = fmtSmall (dims (P1Batch.bval w))

/-! ## The target statement -/

/-- A query `(x, u, ρ)`. -/
abbrev Qry := List Bool × List Bool × List Bool

/-- The budget (same text as `P1ChkFinal.budget`): linear in the input, plus `(log |x| + |ρ| + 1)^c`. -/
def budget (c : ℕ) (p : Qry) : ℕ :=
  p.1.length + p.2.1.length + p.2.2.length + (Nat.log 2 (p.1.length + 1) + p.2.2.length + 1) ^ c

open Classical in
/-- **The target: the check program of family 3 (C4), Task form of D8.** One program for EVERY triple `(x, u, ρ)`
(no condition on the lengths). -/
def ProgC4 (ha : 4 ≤ 2 ^ a) (τ : K → ℕ) (dims : ℕ → C4Dims) : Prop :=
  ∃ c : ℕ, Task (fun p : Qry => budget c p) (fun p => send p)
    (fun p => send (decide (C4w ha τ dims p.1 p.2.1 (P1Batch.bval p.2.2))))

end P1ChkDir
