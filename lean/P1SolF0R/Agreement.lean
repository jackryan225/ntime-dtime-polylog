import P1SolF0R.Run
import P1SolF0R.StageCorrect

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Net P1Wit P1SolFactor P1SolFactor.Owner
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

def requestOf {a h : ℕ} (X : State a h)
    (z : Σ t : X.network.Site, X.network.Half t) : Request :=
  ((P1P7.addr X z.1.1, P1ChkFinal.bwNum z.1.2), P1P5.KW.halfCode X z.1 z.2)

def localClocks (B I h w g : ℕ) : PublicClocks :=
  ((I, 2 ^ h, B, h, w, g), tally (2 ^ h), tally B, tally h)

private theorem planOne_sound (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
      cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
        (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)
    (x u : List Bool) (B I : ℕ) [NeZero B] [NeZero I] {h a : ℕ} (D : Dims) (g : ℕ)
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)
    (hr : D.r = Fintype.card V.K) (hi : D.I = I) (hn : D.N = 2 ^ h)
    (hfields : ∀ i : Fin I, ChunkFacts σ i tape D.bigW (witnessChunk D u i.val))
    (z : Σ s : (rnState V B I σ ha).network.Site, (rnState V B I σ ha).network.Half s) :
    resolveHeader V x (planOne V tape cross (localClocks B I h D.bigW g) u
      (requestOf (rnState V B I σ ha) z)).1 =
      ruleCode V (siteRuleWith V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset z.1) := by
  rcases z with ⟨⟨⟨⟨i, l⟩, twin⟩, lane⟩, z⟩
  let req := requestOf (rnState V B I σ ha) ⟨(((i, l), twin), lane), z⟩
  let args := localClocks B I h D.bigW g
  have hs : reqSite V.K (args, req) = ((locCode l, i.val), twin) :=
    codedBase_eq V B I σ ha i l twin
  have hf : chunkAt ((reqInterval V.K (args, req)).map (P1Batch.fetch u), 0) =
      witnessChunk D u i.val := by
    unfold reqInterval witnessChunk
    rw [hs, hr, hi, hn]
    rfl
  change resolveHeader V x (headerPlan V tape cross
    ((args, reqSite V.K (args, req)),
      (P1ChkFinal.bwNum lane, chunkAt ((reqInterval V.K (args, req)).map (P1Batch.fetch u), 0)))) = _
  rw [hf, hs]
  exact headerPlan_sound V tape cross hc x B I D.bigW g σ ha i l twin lane
    (witnessChunk D u i.val) (hfields i)

set_option maxHeartbeats 900000 in
theorem batchAgreement {F : Type} [CommRing F] (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    (test : EntryCode → Bool) (cross : CrossIn → Bool)
    (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
      cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
        (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)
    (x u : List Bool) (B I : ℕ) [NeZero B] [NeZero I] {h a₀ : ℕ} (D : Dims) (g : ℕ)
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a₀)
    (hr : D.r = Fintype.card V.K) (hi : D.I = I) (hn : D.N = 2 ^ h)
    (hfields : ∀ i : Fin I, ChunkFacts σ i tape D.bigW (witnessChunk D u i.val))
    (htest : ∀ (s : (rnState V B I σ ha).network.Site) (z : (rnState V B I σ ha).network.Half s),
      test (ruleCode V (siteRuleWith V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset s),
        halfCode0 (rnState V B I σ ha) s z) =
      decide (rnSiteOK V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset s z))
    (c : F) (entries : List (Σ s : (rnState V B I σ ha).network.Site, (rnState V B I σ ha).network.Half s)) :
    let args := localClocks B I h D.bigW g
    let qs := entries.map (requestOf (rnState V B I σ ha))
    let ps := batchAdvance (witnessRequests V.K) (planHeaders V tape cross) u (⟨c⟩, qs) args
    finish test (batchAdvance pinRequests (resolveEntries V) x ps args) =
      entries.map fun z =>
        let ok := rnSiteOK V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset z.1 z.2
        ⟨c * @ite F ok (Classical.propDecidable ok) 1 0⟩ := by
  let args := localClocks B I h D.bigW g
  let qs := entries.map (requestOf (rnState V B I σ ha))
  let plan := planOne V tape cross args u
  let headers (p : Request) := resolveHeader V x (plan p).1
  change finish test (batchAdvance pinRequests (resolveEntries V) x
    (batchAdvance (witnessRequests V.K) (planHeaders V tape cross) u (⟨c⟩, qs) args) args) = _
  rw [planHeaders_eq, resolveEntries_eq]
  · rw [List.map_map]
    exact finish_eq V B (withGuessLayout (M := V) x g) I σ ha P1Benes.NetBridge.bset test
      htest c entries headers (fun z _ => planOne_sound V tape cross hc x u B I D g σ ha hr hi hn hfields z)
  · intro p hp
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
    exact headerPlan_pin_bound V tape cross _
  · intro p hp q hq
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
    exact headerPlan_code_bound V tape cross _ q _ hq

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.batchAgreement
