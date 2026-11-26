import P1SolGreedy.MotifBudget
import P1SolGreedy.MotifFamilyEval
import P1ChkFinal.BatchLink
import P1Dispatch.TaskBridge

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

set_option maxHeartbeats 1600000 in
theorem motifTask (all : Bool) (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypMotif all dims M ag)
    (decision : MotifFields → Bool) (hd : Poly decision) (ck : QDom M K → Bool)
    (hc : ∀ p, evaluateMotif all decision (setupC78 all dims M ag (SetupIdx p)) p.val.2.1 = ck p) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val) (fun p => send (ck p)) := by
  let setup := setupC78 all dims M ag
  let q (p : QDom M K) := setup (SetupIdx p)
  let u (p : QDom M K) := p.val.2.1
  let R (p : QDom M K) := motifLevel (q p)
  let F (p : QDom M K) := send p.val
  let s₁ (p : QDom M K) := motFirstNext (q p, (motFirst (q p)).map (P1Batch.fetch (u p)))
  let s₂ (p : QDom M K) := motSecondNext (s₁ p, (motSecond (s₁ p)).map (P1Batch.fetch (u p)))
  have hp : Poly setup := setupC78_poly all dims M ag hf
  have hs : Dom smallSize (fun p : QDom M K => size (q p)) := (hp.length.map SetupIdx).sub index_size
  have hR : Dom smallSize (fun p : QDom M K => size (R p)) := (motifLevel_poly.length.map q).sub hs
  have hpublic (p : QDom M K) : q p =
      setupMotif all (motifFormat all (dims p.val.1.length) (M p.val.1.length) (ag p.val.1.length), p.val.2.2) := by
    simp only [q, setup, setupC78, SetupIdx, bval_bin]
  have hlen (p : QDom M K) : P1Batch.bval (q p).1.1 = (u p).length := by
    rw [hpublic, setupMotif_length]
    exact p.property.1.symm
  have hW (p : QDom M K) (rs : List P1Batch.Req) (h : RowWidths (R p) rs) :
      ∀ r ∈ rs, P1Batch.bval r.2 ≤ size (R p) := by
    unfold R at h ⊢
    rw [hpublic] at h ⊢
    exact setupMotif_widths_le all _ _ _ _ rs h
  have hTot₁ := total_of_boundedRequests smallSize q R motFirst motFirst_poly hs hR
    (fun p => hW p _ (rowWidths_clip _ _ _ (rowWidths_first (q p))))
  have hAddr₁ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ motFirst (q p)) : P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  obtain ⟨t₀, ht₀, T₀⟩ := prepareWitness (M := M) (K := K) hl setup hp
  obtain ⟨t₁, ht₁, hs₁, T₁⟩ := batchPhase hb u q smallSize motFirst motFirstNext
    motFirst_poly motFirstNext_poly hs hTot₁ hAddr₁
  have hq₁ (p : QDom M K) : (s₁ p).1 = q p := rfl
  have hTot₂ := total_of_boundedRequests smallSize s₁ R motSecond motSecond_poly hs₁ hR
    (fun p => hW p _ (rowWidths_clip (motifLevel (s₁ p).1) _ _ (rowWidths_second (s₁ p))))
  have hAddr₂ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ motSecond (s₁ p)) : P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  obtain ⟨t₂, ht₂, hs₂, T₂⟩ := batchPhase hb u s₁ smallSize motSecond motSecondNext
    motSecond_poly motSecondNext_poly hs₁ hTot₂ hAddr₂
  have hTot₃ := total_of_boundedRequests smallSize s₂ R (motThird all) (motThird_poly all) hs₂ hR
    (fun p => hW p _ (rowWidths_clip (motifLevel (nearContext (s₂ p))) _ _ (rowWidths_third all (s₂ p))))
  have hAddr₃ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ motThird all (s₂ p)) : P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  let d (s : MotifNear × List NumberWord) := decision (motThirdNext all s)
  have hdec : Poly d := (motThirdNext_poly all).compose hd
  let cost (p : QDom M K) := p.val.1.length + 3 * (u p).length + t₀ p +
    ((u p).length + t₁ p) + ((u p).length + t₂ p)
  have T : Code.Task cost F (fun p => send (u p, s₂ p)) := (T₀.compose T₁).compose T₂
  have hEval (p : QDom M K) : ck p = d (s₂ p, (motThird all (s₂ p)).map (P1Batch.fetch (u p))) := (hc p).symm
  obtain ⟨t₃, ht₃, T₃⟩ := checkSkeleton hb F u s₂ (motThird all) d ck cost smallSize T
    ((motThird_poly all).pair Poly.identity) hdec hs₂ hTot₃ hAddr₃ hEval
  apply pack_budget (E := 6) (((ht₀.add ht₁).add ht₂).add ht₃)
  exact T₃.bound 1 (fun p => by dsimp only [cost, u]; omega)

end P1SolGreedy.SolDemand

namespace P1SolGreedy

open SolDemand Classical

section Programs

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

theorem taskC7 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypMotif false dims M ag) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C7fam B dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  motifTask false dims ag M K hb hl hf _ (decideTermWords_poly B.scale B.radius.num.natAbs B.radius.den) _
    (fun p => evaluateC7_correct B dims M ag p.val.1 p.val.2.1 p.val.2.2 p.property.1)

theorem progC7 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hl : LenHyp) (hf : FmtHypMotif false dims M ag) :
    ∃ (Rc : Prog Ltr) (c C : ℕ), ∀ p : QDom M K,
      P1Int.ProgAnswers Rc P1Dispatch.answer (P1Int.inputRegs Ltr.bit p.val.1 p.val.2.1 p.val.2.2)
        (decide (C7fam B dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) (C * (budget c p.val + 1)) := by
  obtain ⟨c, h⟩ := taskC7 B dims ag M K batchHyp hl hf
  obtain ⟨Rc, C, hRc⟩ := P1Dispatch.ofTask_tight' (fun p : QDom M K => p.val)
    (fun p => budget c p.val) (fun x u i => decide (C7fam B dims ag x u i)) h
  exact ⟨Rc, c, C, hRc⟩

theorem taskC8 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypMotif true dims M ag) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C8fam B dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :=
  motifTask true dims ag M K hb hl hf _ (decideEnergyWords_poly B.scale B.selectorBits) _
    (fun p => evaluateC8_correct B dims M ag p.val.1 p.val.2.1 p.val.2.2 p.property.1)

theorem progC8 (dims : ℕ → Dims) (ag : ℕ → ℕ → ℕ × ℕ) (M K : ℕ → ℕ)
    (hl : LenHyp) (hf : FmtHypMotif true dims M ag) :
    ∃ (Rc : Prog Ltr) (c C : ℕ), ∀ p : QDom M K,
      P1Int.ProgAnswers Rc P1Dispatch.answer (P1Int.inputRegs Ltr.bit p.val.1 p.val.2.1 p.val.2.2)
        (decide (C8fam B dims ag p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) (C * (budget c p.val + 1)) := by
  obtain ⟨c, h⟩ := taskC8 B dims ag M K batchHyp hl hf
  obtain ⟨Rc, C, hRc⟩ := P1Dispatch.ofTask_tight' (fun p : QDom M K => p.val)
    (fun p => budget c p.val) (fun x u i => decide (C8fam B dims ag x u i)) h
  exact ⟨Rc, c, C, hRc⟩

end Programs

#print axioms taskC7
#print axioms progC7
#print axioms taskC8
#print axioms progC8

end P1SolGreedy
