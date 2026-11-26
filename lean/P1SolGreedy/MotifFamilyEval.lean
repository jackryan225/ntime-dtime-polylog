import P1SolGreedy.MotifEnergyCorrect

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

def evaluateMotif (all : Bool) (dec : MotifFields → Bool) (q : MotifContext) (u : List Bool) : Bool :=
  let first := motFirstNext (q, (motFirst q).map (P1Batch.fetch u))
  let second := motSecondNext (first, (motSecond first).map (P1Batch.fetch u))
  let third := motThirdNext all (second, (motThird all second).map (P1Batch.fetch u))
  dec third

theorem evaluateMotif_reads (all : Bool) (dec : MotifFields → Bool) (q : MotifContext) (u : List Bool)
    (hl : P1Batch.bval q.1.1 = u.length) :
    evaluateMotif all dec q u =
      dec (savedMotifFields all (savedMotifNear (savedMotifBases q u) u) u) := by
  unfold evaluateMotif
  rw [motFirstNext_reads _ _ hl]
  let a := savedMotifBases q u
  let b := motSecondNext (a, (motSecond a).map (P1Batch.fetch u))
  change dec (motThirdNext all (b, (motThird all b).map (P1Batch.fetch u))) = _
  have h₁ : P1Batch.bval a.1.1.1 = u.length := hl
  have h₂ : b = savedMotifNear a u := motSecondNext_reads a u h₁
  rw [h₂]
  have h₃ : P1Batch.bval (nearContext (savedMotifNear a u)).1.1 = u.length := hl
  rw [motThirdNext_reads _ _ _ h₃]

section Block

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

open Classical in
set_option maxHeartbeats 1000000 in
theorem evaluateC7_correct (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ)
    (x u i : List Bool) (hlen : u.length = M x.length) :
    evaluateMotif false (decideTermWords B.scale B.radius.num.natAbs B.radius.den)
      (setupC78 false dims M ag (bin x.length, i)) u = decide (C7fam B dims ag x u (P1Batch.bval i)) := by
  let D := dims x.length
  let A := ag x.length
  let m := M x.length
  let q := setupMotif false (motifFormat false D m A, i)
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let Y := q.1.2.2.1
  let key := q.2.2
  have hq : setupC78 false dims M ag (bin x.length, i) = q := by
    simp only [setupC78, bval_bin, D, A, m, q]
  have hl : P1Batch.bval q.1.1 = u.length := (setupMotif_length false D m A i).trans hlen.symm
  have hs := setupMotif_spec false D m A i
  rw [hq, evaluateMotif_reads _ _ _ _ hl, Bool.eq_iff_iff, decide_eq_true_eq]
  by_cases h : ShrinkIdx (termDims D A) (P1Batch.bval i)
  · have hq' : q = activeMotif false D ℓ (A ℓ).1 (A ℓ).2 (bin m) Y key :=
      setupMotif_active false D m A i h
    have hY : P1Batch.bval Y = P1Batch.bval i / 2 ^ levBits D / termStride A ℓ := (hs.2 h.1).2.2.1
    have hk : P1Batch.bval key = P1Batch.bval i / 2 ^ levBits D % termStride A ℓ := (hs.2 h.1).2.2.2
    conv_lhs => rw [hq']
    rw [decideTermWords_correct B, hY, hk]
    change _ ↔ ShrinkIdx (termDims D A) (P1Batch.bval i) → _
    exact ⟨fun hc _ => hc, fun hc => hc h⟩
  · have hb : q.1.2.1 = false := Bool.eq_false_iff.mpr fun ht => h (hs.1.mp ht)
    have hb' : (fieldContext (savedMotifFields false (savedMotifNear (savedMotifBases q u) u) u)).1.2.1 = false := hb
    simp only [decideTermWords, hb', Bool.cond_false]
    exact ⟨fun _ ht => (h ht).elim, fun _ => True.intro⟩

open Classical in
set_option maxHeartbeats 1000000 in
theorem evaluateC8_correct (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ)
    (x u i : List Bool) (hlen : u.length = M x.length) :
    evaluateMotif true (decideEnergyWords B.scale B.selectorBits)
      (setupC78 true dims M ag (bin x.length, i)) u = decide (C8fam B dims ag x u (P1Batch.bval i)) := by
  let D := dims x.length
  let A := ag x.length
  let m := M x.length
  let q := setupMotif true (motifFormat true D m A, i)
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let Y := q.1.2.2.1
  let key := q.2.2
  have hq : setupC78 true dims M ag (bin x.length, i) = q := by
    simp only [setupC78, bval_bin, D, A, m, q]
  have hl : P1Batch.bval q.1.1 = u.length := (setupMotif_length true D m A i).trans hlen.symm
  have hs := setupMotif_spec true D m A i
  rw [hq, evaluateMotif_reads _ _ _ _ hl, Bool.eq_iff_iff, decide_eq_true_eq]
  by_cases h : ShrinkIdx D (P1Batch.bval i)
  · have hq' : q = activeMotif true D ℓ (A ℓ).1 (A ℓ).2 (bin m) Y key :=
      setupMotif_active true D m A i h
    have hY : P1Batch.bval Y = P1Batch.bval i / 2 ^ levBits D := (hs.2 h.1).2.2.1
    conv_lhs => rw [hq']
    rw [decideEnergyWords_correct _ _ _ _ _ _ _ _ B, hY]
    change _ ↔ ShrinkIdx D (P1Batch.bval i) → _
    exact ⟨fun hc _ => hc, fun hc => hc h⟩
  · have hb : q.1.2.1 = false := Bool.eq_false_iff.mpr fun ht => h (hs.1.mp ht)
    have hb' : (fieldContext (savedMotifFields true (savedMotifNear (savedMotifBases q u) u) u)).1.2.1 = false := hb
    simp only [decideEnergyWords, hb', Bool.cond_false]
    exact ⟨fun _ ht => (h ht).elim, fun _ => True.intro⟩

end Block

#print axioms evaluateC7_correct
#print axioms evaluateC8_correct

end P1SolGreedy.SolDemand
