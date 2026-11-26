import P1C10.Code
import P1ChkFinal.Progs

/-!
# P1, check C10: the PROGRAM statements (lane P1-lean-c10), targets for Sol provers

Form of decision D8 (as `P1ChkFinal.progC11`): an OpenAI `Task` over `Ltr` with query `send (x, u, ρ)` and reply
`send (decide (C10w fx dims x u (bval ρ)))`, on the domain `QDom M K`, budget `P1ChkFinal.budget c` (linear in
`|x| + |u| + |ρ|`, plus a polynomial in `log |x| + |ρ|`). `P1Dispatch.ofTask` turns it into the `Prog Rc`.

Why a multi-round skeleton: C10 walks the ball of radius 6 (shrink) or 1 (refresh) by STORED addresses, so the
addresses of round `r + 1` are known only after the fetch of round `r`. `P1ChkFinal.checkSkeleton` has ONE batched
look-up; `checkRounds` (target 1) has `R` of them (R = 7 for a shrink, 2 for a refresh, plus one for the new panel).

TARGETS (Sol items; the statements are the Props below, a prover proves `theorem <Lib>.<name> : P1C10.<Target>`):
1. `CheckRoundsTarget`: the generic `R`-round skeleton (routine; model `P1ChkFinal.checkSkeleton`, same proof per round).
2. `ProgC10Target`: the C10 program, with the interfaces below as hypotheses (uses 1).
3. `RcCasesTarget`: one shrink recomputation from the finitely many substeps of a block (routine).

Interfaces (explicit hypotheses):
* `BatchHyp` = `P1Batch.batch_lookup` (PROVED, `P1ChkFinal.BatchLink.batchHyp`); `LenHyp` (P1-sol-fmt);
* `FmtHyp10 dims`: the format numbers of substep `ℓ` (`fmt10`) are `Poly` in the binary words of `n` and `ℓ`;
* `hfb`: the bits of one base at any level and the table lengths of the codes are polylogarithmic in `n` (`c10Size`);
* `Poly (fun q => fx.rcS q.1.1 q.1.2 q.2)`, `Poly fx.rcR`: the recomputations on codes (targets `P1C10.ShrinkProgram`
  for each shrinking substep of the block, combined by a finite case split on the slot bits, and
  `P1C10.RefreshProgram`).
-/

namespace P1C10

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1ChkGreedy P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-! ## Format numbers and sizes -/

/-- The twelve field kinds of one level, in the order of `P1Wit.Mem`. -/
def memAll : List Mem :=
  [.layout, .outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar, .width, .colour, .offset, .energy, .terms]

/-- The format numbers that check C10 at substep `ℓ` needs (binary words, LSB first): `top`, `levBits`, the sizes of
levels `ℓ` and `ℓ + 1`, the kind bit of `ℓ`, and the offset and width of every field section of levels `ℓ`, `ℓ + 1`. -/
def fmt10 (D : Dims) (ℓ : ℕ) : List (List Bool) :=
  ([D.top, levBits D, D.fixedLen,
    (D.lv ℓ).bases, (D.lv ℓ).slots, (D.lv ℓ).lanes, (D.lv ℓ).laneW, if (D.lv ℓ).shrink then 1 else 0,
    (D.lv ℓ).termKeys, (D.lv ℓ).termArity,
    (D.lv (ℓ + 1)).bases, (D.lv (ℓ + 1)).slots, (D.lv (ℓ + 1)).lanes, (D.lv (ℓ + 1)).laneW] ++
   (memAll.flatMap fun k => [D.off (secLev ℓ k), D.width (secLev ℓ k)]) ++
   (memAll.flatMap fun k => [D.off (secLev (ℓ + 1) k), D.width (secLev (ℓ + 1) k)])).map Nat.bits

/-- [P6 / P10] The C10 format numbers are polynomial-time in the binary words of `n` and `ℓ`. -/
def FmtHyp10 (dims : ℕ → Dims) : Prop :=
  Poly (fun w : List Bool × List Bool => fmt10 (dims (P1Batch.bval w.1)) (P1Batch.bval w.2))

/-- The bits of the stored fields of ONE base of level `ℓ` (panel, widths, colour, offset, energy, terms) plus the
layout field of the level. -/
def baseBits (D : Dims) (ℓ : ℕ) : ℕ :=
  (D.lv ℓ).slots * ([Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar].map fun k =>
      D.width (secLev ℓ k)).sum +
    (D.lv ℓ).lanes * (D.lv ℓ).slots * D.width (secLev ℓ .width) +
    D.width (secLev ℓ .colour) + D.width (secLev ℓ .offset) + 2 * D.width (secLev ℓ .energy) +
    (D.lv ℓ).termKeys * ((D.lv ℓ).termArity + 1) * D.width (secLev ℓ .terms) + D.width (secLev ℓ .layout)

/-- The largest `baseBits` over the levels `0, ..., top`. -/
def maxBaseBits (D : Dims) : ℕ := ((List.range (D.top + 1)).map (baseBits D)).foldr max 0

/-- The table lengths that the codes of substep `ℓ` use: lanes of the old shrink datum (`packingLaneBits a g`), of the
old refresh datum (`a + g`, so also the `2^a` old slots), of the new panel (`g`) and its slots (`2^b`), with
`a = slotBits D ℓ`, `b = slotBits D (ℓ+1)`, `g = (D.lv (ℓ+1)).laneW`. (The ball has at most `(1 + 2 * 2^a)^6` entries.) -/
def lanesUsed (D : Dims) (ℓ : ℕ) : ℕ :=
  2 ^ packingLaneBits (slotBits D ℓ) (D.lv (ℓ + 1)).laneW + 2 ^ (slotBits D ℓ + (D.lv (ℓ + 1)).laneW) +
    2 ^ (D.lv (ℓ + 1)).laneW + 2 ^ slotBits D (ℓ + 1)

/-- The sum of the widths of the twelve field kinds of level `ℓ` (a read of ONE field of any kind costs at most this).
Needed because `Dims` allows `slots = lanes = 0` while the check still reads `2 ^ slotBits = 1` slot and one lane: then
`baseBits` is `0` but a width field of `wW` bits is read (counterexample of P1-sol-c10prog, board 12:54Z). -/
def fieldW (D : Dims) (ℓ : ℕ) : ℕ := (memAll.map fun k => D.width (secLev ℓ k)).sum

/-- The size measure that must be polylogarithmic in `n` (hypothesis `hfb` of `progC10`): the bits of a base, and at
every substep `ℓ < top` the table lengths of the codes and the field widths of levels `ℓ` and `ℓ + 1`. -/
def c10Size (D : Dims) : ℕ :=
  maxBaseBits D + ((List.range D.top).map fun ℓ => lanesUsed D ℓ + fieldW D ℓ + fieldW D (ℓ + 1)).foldr max 0

/-! ## Target 1: the generic multi-round skeleton -/

/-- The small state after `r` rounds: start `s0`, then `r` times: fetch the requests of the state, then `step`. -/
def roundState {S : Type*} (rq : S → List P1Batch.Req) (step : S × List (List Bool) → S) (w : List Bool)
    (s0 : S) : ℕ → S
  | 0 => s0
  | r + 1 => step (roundState rq step w s0 r, (rq (roundState rq step w s0 r)).map (P1Batch.fetch w))

/-- **TARGET 1 (Sol): the `R`-round check skeleton.** `R` batched look-ups, each with requests computed from the small
state of the round before; the budget is that of (A), `R + 1` times `|u|` (one more `|u|` to drop `u` before the
decision: with `R * |u|` the target is FALSE at `R = 0`, counterexample of P1-sol-c10prog, board 12:47Z), and a term
polynomial in `σ`. -/
def CheckRoundsTarget : Prop :=
  ∀ {X S : Type} [Codec S] (_hbatch : BatchHyp) (R : ℕ)
    (Q : X → Tree) (u : X → List Bool) (s0 : X → S) (rq : S → List P1Batch.Req)
    (step : S × List (List Bool) → S) (dec : S → Bool) (ck : X → Bool) (a σ : X → ℕ)
    (_hA : Code.Task a Q (fun p => send (u p, s0 p)))
    (_hrq : Poly (fun z : S => (rq z, z)))
    (_hstep : Poly step)
    (_hdec : Poly dec)
    (_hσ : ∀ r ≤ R, Dom σ (fun p => size (roundState rq step (u p) (s0 p) r)))
    (_htot : ∀ r < R, Dom σ (fun p => P1Batch.total (rq (roundState rq step (u p) (s0 p) r))))
    (_haddr : ∀ p, ∀ r < R, ∀ q ∈ rq (roundState rq step (u p) (s0 p) r), P1Batch.bval q.1 ≤ (u p).length)
    (_hck : ∀ p, ck p = dec (roundState rq step (u p) (s0 p) R)),
    ∃ t : X → ℕ, Dom σ t ∧ Code.Task (fun p => a p + (R + 1) * (u p).length + t p) Q (fun p => send (ck p))

/-! ## Target 2: the C10 program -/

/-- **TARGET 2 (Sol): family 9 (C10) as a program** (D8 form, as `P1ChkFinal.progC11`). -/
def ProgC10Target : Prop :=
  ∀ (fx : C10Fix) (dims : ℕ → Dims) (M K : ℕ → ℕ) (_hb : BatchHyp) (_hl : LenHyp)
    (_hM : ∀ n, (dims n).fixedLen ≤ M n)
    (_hf : FmtHyp10 dims)
    (_hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => c10Size (dims n)))
    (_hS : Poly (fun q : (ℕ × ℕ) × ShrinkIn => fx.rcS q.1.1 q.1.2 q.2)) (_hR : Poly fx.rcR),
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C10w fx dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))))

/-! ## Target 3: one shrink recomputation for the finitely many substeps of a block -/

/-- The shrink recomputation for slot bits `(a, b)`: the first entry of `L` with key `(a, b)`, else `none`. -/
def rcCases (L : List ((ℕ × ℕ) × (ShrinkIn → Option PanelCode))) (a b : ℕ) (z : ShrinkIn) : Option PanelCode :=
  match L.find? (fun e => e.1 == (a, b)) with
  | some e => e.2 z
  | none => none

/-- **TARGET 3 (Sol): a finite case split of polynomial-time recomputations is polynomial-time** (gives `hS` of
`progC10` from one `P1C10.ShrinkProgram` per shrinking substep of the block, keys `(degreeExponent i, degreeExponent
(i+1))`). -/
def RcCasesTarget : Prop :=
  ∀ (L : List ((ℕ × ℕ) × (ShrinkIn → Option PanelCode))) (_hL : ∀ e ∈ L, Poly e.2),
    Poly (fun q : (ℕ × ℕ) × ShrinkIn => rcCases L q.1.1 q.1.2 q.2)

theorem rcCases_of_mem (L : List ((ℕ × ℕ) × (ShrinkIn → Option PanelCode))) {a b : ℕ}
    {rc : ShrinkIn → Option PanelCode} (h : L.find? (fun e => e.1 == (a, b)) = some ((a, b), rc)) :
    rcCases L a b = rc := by
  funext z
  unfold rcCases
  rw [h]

end P1C10
