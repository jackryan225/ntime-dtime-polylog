import P1ChkFinal.ProgC12
import P1ChkFinal.ProgC13
import P1SolFinal.C11Fmt
import P1SolFinal.Ends

/-!
# P1ChkFinal.ProgSolFmt: programs of C11 and C13ends with ONLY the format inputs (Sol P1-sol-finalprog)

Lane P1-lean-checks (2026-11-25). The delivered theorems `P1ChkFinal.SolFinal.progC11Fmt` (P1SolFinal/C11Fmt.lean,
sha256 7fe61e5a...4360d) and `P1ChkFinal.SolFinal.progC13ends` (P1SolFinal/Ends.lean, sha256 31c745b4...9761b), files
copied UNCHANGED. Their conclusions are the texts of `P1ChkFinal.progC11` (ProgC11.lean) and `P1ChkFinal.progC13ends`
(ProgC13.lean); their hypotheses are ONLY `BatchHyp`, `LenHyp`, `FmtHyp dims` (as `progC12`): the inputs `hM`, `hrq`,
`hdec`, `hfb` of chkfinal's forms are gone (the concrete requests and decisions are proved polynomial inside).
`LenHyp` is converted with `lenHyp_bin` (shim `SolFinal.LenHyp` in Progs.lean, see ProgC12.lean).
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module

open scoped Classical

/-- **Family 10 (C11), program, format inputs only.** Conclusion = that of `progC11`. -/
theorem progC11_fmt (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C11w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  SolFinal.progC11Fmt dims M K hb (lenHyp_bin hl) hf

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- **Family 13 (C13ends), program, format inputs only.** Conclusion = that of `progC13ends`. -/
theorem progC13ends_fmt (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims)
    (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw b l dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  SolFinal.progC13ends b l dims M K hb (lenHyp_bin hl) hf

/-- Check: the conclusion of `progC11_fmt` is the conclusion of chkfinal's `progC11` (same type, by `exact`). -/
example (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp)
    (hM : ∀ n, (dims n).fixedLen ≤ M n)
    (hrq : Poly (fun z : List Bool × List Bool => (rqC11 dims z, z)))
    (hdec : Poly (decC11 dims))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC11 (dims n))) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C11w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  (fun _ => progC11_fmt dims M K hb hl hf) (progC11 dims M K hb hl hM hrq hdec hfb)

/-- Check: the conclusion of `progC13ends_fmt` is the conclusion of chkfinal's `progC13ends`. -/
example (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hM : ∀ n, (dims n).fixedLen ≤ M n)
    (hrq : Poly (fun z : List Bool × List Bool => (rqC13ends dims z, z)))
    (hdec : Poly (decC13ends b l))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => totC13 (dims n))) (hf : FmtHyp dims) :
    (∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw b l dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))))) ∧
    (∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw b l dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))))) :=
  ⟨progC13ends b l dims M K hb hl hM hrq hdec hfb, progC13ends_fmt b l dims M K hb hl hf⟩

end P1ChkFinal

#print axioms P1ChkFinal.progC11_fmt
#print axioms P1ChkFinal.progC13ends_fmt
