import P1ChkFinal.FamGreedyGenuine
import P1ChkFinal.FmtAgTarget
import P1SolFmt.FmtAgTags
import P1SolFmt.FmtAgMotif

/-!
# P1ChkFinal.FamGreedyAg: C6, C7, C8 as `FamProg` at the genuine dims and the genuine `ag` (format inputs discharged)

Lane P1-lean-greedy (2026-11-25). `FamGreedy.famC6/famC7/famC8` need `FmtHypTags` / `FmtHypMotif false/true` at
`lpM2 s a b`; Sol P1-sol-fmtag proved them at the genuine dims, witness length `Params.m Kc (lpTime a b n)`, and the genuine
`ag` written inline (`P1SolFmt.fmtHypTags_genuine`, `fmtHypMotif_genuine`; files ChkFinal/P1SolFmt/FmtAg{Core,Tags,Motif}.lean
copied UNCHANGED, sha256 c50f0c3d.., f2ebdf96.., b125bba7..; runner LEAN CHECK passed, round 1). `agG dims` is that inline `ag`
(`rfl`), and `P1Int.P11.genuineAg dims = agG dims` by `rfl` (both are `fun n ℓ => (slotW, laneW - packingLaneBits slotW 0)`).
-/

namespace P1ChkFinal.FamGreedy

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1Int P1SolGreedy P1SolGreedy.SolDemand P1ChkFinal.FmtAgTarget

open Classical

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates) (Kc : P1Wrap.Consts)
  (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)

/-- The genuine dims function (as in `FamGreedyGenuine`). -/
noncomputable abbrev gDims : ℕ → Dims :=
  fun n => SolSpace.genuineDims A Kc V aM (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias

theorem m_eq_lpM2_fun :
    (fun n => P1Wrap.Params.m Kc (lpTime a b n)) = lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b :=
  funext fun n => P11.m_eq_lpM2 Kc a b n

theorem fmtHypTags_lpM2 :
    FmtHypTags (gDims A Kc V aM a b d bigBias termBias) (lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b)
      (agG (gDims A Kc V aM a b d bigBias termBias)) := by
  rw [← m_eq_lpM2_fun Kc a b]
  exact P1SolFmt.fmtHypTags_genuine A Kc V aM a b d bigBias termBias

theorem fmtHypMotif_lpM2 (all : Bool) :
    FmtHypMotif all (gDims A Kc V aM a b d bigBias termBias) (lpM2 ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b)
      (agG (gDims A Kc V aM a b d bigBias termBias)) := by
  rw [← m_eq_lpM2_fun Kc a b]
  exact P1SolFmt.fmtHypMotif_genuine all A Kc V aM a b d bigBias termBias

/-- **C6 (family 5) as `FamProg` at the genuine dims and `ag`**, `s = 2^-Kc.j`. -/
theorem famC6_genuine (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C6fam (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC6 _ _ hs hb (fmtHypTags_lpM2 A Kc V aM a b d bigBias termBias)

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

/-- **C7, shrinking part (family 6 before D15's refresh part) as `FamProg` at the genuine dims and `ag`.** -/
theorem famC7_genuine (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C7fam B (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC7 B _ _ hs hb (fmtHypMotif_lpM2 A Kc V aM a b d bigBias termBias false)

/-- **C8 (family 7) as `FamProg` at the genuine dims and `ag`.** -/
theorem famC8_genuine (hs : (2 : ℝ) ^ (-(Kc.j : ℤ)) ≤ 1) (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
      (fun x u i => decide (C8fam B (gDims A Kc V aM a b d bigBias termBias)
        (agG (gDims A Kc V aM a b d bigBias termBias)) x u i)) ((2 : ℝ) ^ (-(Kc.j : ℤ))) a b cc n₂ :=
  famC8 B _ _ hs hb (fmtHypMotif_lpM2 A Kc V aM a b d bigBias termBias true)

end P1ChkFinal.FamGreedy

#print axioms P1ChkFinal.FamGreedy.famC6_genuine
#print axioms P1ChkFinal.FamGreedy.famC7_genuine
#print axioms P1ChkFinal.FamGreedy.famC8_genuine
