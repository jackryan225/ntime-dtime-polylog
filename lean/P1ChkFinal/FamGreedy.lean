import P1SolGreedy.DemandWidth
import P1SolGreedy.ProgC5
import P1SolGreedy.ProgC6
import P1SolGreedy.ProgC78
import P1SolGreedy.ProgC9
import P1ProgDir.FamTask
import P1SolFmt.Length

/-!
# P1ChkFinal.FamGreedy: the programs of C5-C9 (Sol P1-sol-greedyprog2) in the form `P1Int.P11.FamProg`

Lane P1-lean-checks (2026-11-25). The 37 files P1SolGreedy/*.lean of P1-sol-greedyprog2 (round 3) are copied UNCHANGED to
research/p1/lean/ChkFinal/P1SolGreedy/. Their Task forms `P1SolGreedy.taskC5 .. taskC9` on `QDom M K` need `BatchHyp`,
`LenHyp` (both proved: `P1ChkFinal.batchHyp`, `P1SolFmt.SolLength.lenHyp`) and ONE format hypothesis each
(`FmtHypGreedy dims M` for C5, C9; `FmtHypTags dims M ag` for C6; `FmtHypMotif false/true dims M ag` for C7/C8: Poly
functions of the binary word of `n` that give format numbers). With `M := lpM2 s a b`, `K := fun n => lpK2 a b n - 4`
the converter `P1ProgDir.famProg_of_task` gives the family form. OPEN: the three format hypotheses at the genuine dims.
-/

namespace P1ChkFinal.FamGreedy

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1Int P1SolGreedy P1SolGreedy.SolDemand

open Classical

theorem famC5 (dims : ℕ → Dims) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (hf : FmtHypGreedy dims (lpM2 s a b)) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C5fam dims x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := taskC5 dims (lpM2 s a b) (fun n => lpK2 a b n - 4) batchHyp P1SolFmt.SolLength.lenHyp hf
  exact P1ProgDir.famProg_of_task hs hb _ c T

theorem famC6 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (hf : FmtHypTags dims (lpM2 s a b) ag) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C6fam dims ag x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := taskC6 dims ag (lpM2 s a b) (fun n => lpK2 a b n - 4) batchHyp P1SolFmt.SolLength.lenHyp hf
  exact P1ProgDir.famProg_of_task hs hb _ c T

theorem famC9 (dims : ℕ → Dims) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (hf : FmtHypGreedy dims (lpM2 s a b)) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C9fam dims x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := taskC9 dims (lpM2 s a b) (fun n => lpK2 a b n - 4) batchHyp P1SolFmt.SolLength.lenHyp hf
  exact P1ProgDir.famProg_of_task hs hb _ c T

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem famC7 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (hf : FmtHypMotif false dims (lpM2 s a b) ag) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C7fam B dims ag x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := taskC7 B dims ag (lpM2 s a b) (fun n => lpK2 a b n - 4) batchHyp P1SolFmt.SolLength.lenHyp hf
  exact P1ProgDir.famProg_of_task hs hb _ c T

theorem famC8 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (hf : FmtHypMotif true dims (lpM2 s a b) ag) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C8fam B dims ag x u i)) s a b cc n₂ := by
  obtain ⟨c, T⟩ := taskC8 B dims ag (lpM2 s a b) (fun n => lpK2 a b n - 4) batchHyp P1SolFmt.SolLength.lenHyp hf
  exact P1ProgDir.famProg_of_task hs hb _ c T

end P1ChkFinal.FamGreedy

#print axioms P1SolGreedy.dw_correct
#print axioms P1ChkFinal.FamGreedy.famC5
#print axioms P1ChkFinal.FamGreedy.famC6
#print axioms P1ChkFinal.FamGreedy.famC7
#print axioms P1ChkFinal.FamGreedy.famC8
#print axioms P1ChkFinal.FamGreedy.famC9
