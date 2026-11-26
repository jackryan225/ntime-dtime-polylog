import P1ChkFinal.ProgC11
import P1SolFinal.C12

/-!
# P1ChkFinal.ProgC12: the program of family 11 (check C12), integrated from the Sol prover P1-sol-finalprog

Lane P1-lean-checks (2026-11-25). The statement below is the text of the old `sorry` statement of
`P1ChkFinal/Progs.lean` (moved here unchanged, with the same `open` lines). The proof is the delivered theorem
`P1ChkFinal.SolFinal.progC12` (file P1SolFinal/C12.lean, sha256
b71231e0a76765eca074b84fcfaba2e8b8cd6680aab3d2bd7790307e7129d2c7, copied unchanged). Its hypotheses are the
allowed interface facts of the old statement only: `BatchHyp`, `LenHyp`, `FmtHyp dims`. The Sol files were compiled
against the earlier `bin` form of `LenHyp`; the shim `P1ChkFinal.SolFinal.LenHyp` (in Progs.lean) keeps them unchanged,
and `lenHyp_bin` (ProgC11.lean) converts the current `Nat.bits` form.
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module

open scoped Classical

/-- **Family 11 (C12), program** (the zero test of S3 is one scan). -/
theorem progC12 (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C12w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  SolFinal.progC12 dims M K hb (lenHyp_bin hl) hf

/-- Statement check (owner rule of G3-chief, board 1800): the delivered theorem has exactly the needed type. -/
example (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C12w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  @SolFinal.progC12 dims M K hb (lenHyp_bin hl) hf

end P1ChkFinal

#print axioms P1ChkFinal.progC12
#print axioms P1ChkFinal.SolFinal.progC12
