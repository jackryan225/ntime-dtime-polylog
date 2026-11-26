import P1SolCone.TerminalReplay
import P1SolCone.BatchKeep

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

private theorem cachedTerminalSpans_bounds (h : TerminalHeader) (ic wc : FieldCache)
    (s : Span) (hs : s ∈ (cachedTerminalSpans h ic wc).2.1 ++ (cachedTerminalSpans h ic wc).2.2) :
    spanValid h.2.1 s = true ∧ s.2 ≤ h.2.2.1 := by
  let arcs := cachedTerminalArcs h ic
  let spans := (arcs.1.map (cachedArcSpan h wc), arcs.2.map (cachedArcSpan h wc))
  let yes := ((terminalHeaderOK h && cachedDispOK h ic) && (arcs.1 ++ arcs.2).all (terminalArcOK h)) &&
    (spans.1 ++ spans.2).all (terminalSpanOK h)
  let out : Bool × List Span × List Span := bif yes then (true,spans) else (false,[],[])
  change s ∈ out.2.1 ++ out.2.2 at hs
  dsimp only [out] at hs
  by_cases good : yes = true
  · rw [good] at hs
    dsimp only [yes] at good
    simp only [Bool.and_eq_true] at good
    have hall := good.2
    have b := List.all_eq_true.mp hall s hs
    simpa only [terminalSpanOK, Bool.and_eq_true, decide_eq_true_eq] using b
  · simp [Bool.eq_false_iff.mpr good] at hs

private theorem terminalMetadata_task {X A : Type*} [Codec A]
    (head : A → TerminalHeader) (keys : A → List FieldKey) (hh : Poly head) (hk : Poly keys)
    (u : X → List Bool) (a : X → A) (σ B : X → ℕ)
    (hs : Dom σ (fun x => size (a x))) (hB : Dom σ B)
    (hlen : ∀ x, (head (a x)).2.1 = (u x).length)
    (hwidth : ∀ x k, k ∈ keys (a x) → P1Batch.bval (terminalFieldReq (head (a x)) k).2 ≤ B x) :
    (∃ cost : X → ℕ, Dom σ cost ∧ Task (fun x => (u x).length + cost x)
      (fun x => send (u x, a x))
      (fun x => send (u x, (a x, readTerminalFields (head (a x)) (keys (a x)) (u x))))) ∧
    Dom σ (fun x => size (readTerminalFields (head (a x)) (keys (a x)) (u x))) := by
  let rq (p : A) := terminalFieldRequests (head p) (keys p)
  let merge (p : A × List (List Bool)) := fieldCache (keys p.1) p.2
  have hrq : Poly rq := (hh.pair hk).compose terminalFieldRequests_poly
  have hmerge : Poly merge := ((Easy.fst.poly.compose hk).pair Easy.snd.poly).compose fieldCache_poly
  have total : Dom σ (fun x => P1Batch.total (rq (a x))) := by
    apply batchTotal_dom hrq hs hB
    intro x q hq
    obtain ⟨k,hk',rfl⟩ := List.mem_map.mp hq
    exact hwidth x k hk'
  refine ⟨?_, batchReply_dom rq merge hrq hmerge u a σ hs total⟩
  exact batchKeep_task rq merge [] hrq hmerge u a σ hs total (fun x q hq =>
    (terminalFieldRequests_offsets (head (a x)) (keys (a x)) q hq).trans
      (le_of_eq (hlen x)))

/-- Execute the incidence, width and payload reads with three batched scans. -/
theorem terminalReplay_task {X : Type*} (h : X → TerminalHeader) (u : X → List Bool)
    (σ B : X → ℕ) (hs : Dom σ (fun x => size (h x))) (hB : Dom σ B)
    (hcap : Dom σ (fun x => (h x).2.2.1)) (hlen : ∀ x, (h x).2.1 = (u x).length)
    (hwidth : ∀ x k, k.1 < 13 → P1Batch.bval (terminalFieldReq (h x) k).2 ≤ B x) :
    (∃ cost : X → ℕ, Dom σ cost ∧ Task (fun x => 4 * (u x).length + cost x)
      (fun x => send (u x, h x))
      (fun x => send (u x, replayTerminalPayload (h x) (u x)))) ∧
      Dom σ (fun x => size (replayTerminalPayload (h x) (u x))) := by
  let inc (x : X) := readTerminalFields (h x) (terminalIncidenceKeys (h x)) (u x)
  let st (x : X) := (h x, inc x)
  obtain ⟨⟨t₁, ht₁, go₁⟩, hInc⟩ := terminalMetadata_task id terminalIncidenceKeys Code.Poly.identity
    terminalIncidenceKeys_poly u h σ B hs hB hlen
    (fun x k hk => hwidth x k (terminalIncidenceKeys_kinds _ _ hk))
  have hSt : Dom σ (fun x => size (st x)) :=
    ((hs.add hInc).add (Dom.const σ 1)).mono fun x => by
      change size (h x, inc x) ≤ _
      rw [size_prod]
      rfl
  let k₂ (p : TerminalHeader × FieldCache) := terminalArcWidths p.1 p.2
  let wc (x : X) := readTerminalFields (h x) (k₂ (st x)) (u x)
  obtain ⟨⟨t₂, ht₂, go₂⟩, hWc⟩ := terminalMetadata_task Prod.fst k₂ Easy.fst.poly
    terminalArcWidths_poly u st σ B hSt hB hlen
    (fun x k hk => hwidth x k (terminalArcWidths_kinds _ _ _ hk))
  let state (x : X) := (st x, wc x)
  let spans (x : X) := cachedTerminalSpans (h x) (inc x) (wc x)
  have hstate : Dom σ (fun x => size (state x)) :=
    ((hSt.add hWc).add (Dom.const σ 1)).mono fun x => by
      change size (st x, wc x) ≤ _
      rw [size_prod]
  have z : Easy (fun p : (TerminalHeader × FieldCache) × FieldCache => (p.1.1,p.1.2,p.2)) := by fun_prop
  have hcalc := z.poly.compose cachedTerminalSpans_poly
  have hSpan : Dom σ (fun x => size (spans x)) := (hcalc.length.map state).sub hstate
  obtain ⟨t₃, ht₃, go₃⟩ := hcalc.on hstate
  let rq (p : Bool × List Span × List Span) := payloadRequests p.2
  let merge (p : (Bool × List Span × List Span) × List (List Bool)) := splitPayload p.1.2 p.2
  have hrq : Poly rq := Easy.snd.poly.compose payloadRequests_poly
  have hmerge : Poly merge := by
    exact (show Poly (fun p : (Bool × List Span × List Span) × List (List Bool) => (p.1.2,p.2))
      from by fun_prop).compose splitPayload_poly
  have hper (x : X) (q : P1Batch.Req) (hq : q ∈ rq (spans x)) : P1Batch.bval q.2 ≤ (h x).2.2.1 := by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    rw [spanRequest, bval_bin]
    exact (cachedTerminalSpans_bounds (h x) (inc x) (wc x) s hs).2
  have addr (x : X) (q : P1Batch.Req) (hq : q ∈ rq (spans x)) : P1Batch.bval q.1 ≤ (u x).length :=
    (payloadRequests_offsets (spans x).2 (h x).2.1
      (fun s hs => (cachedTerminalSpans_bounds (h x) (inc x) (wc x) s hs).1) q hq).trans
      (le_of_eq (hlen x))
  obtain ⟨t₄, ht₄, go₄⟩ := batchKeep_task rq merge ([],[]) hrq hmerge u spans σ hSpan
    (batchTotal_dom hrq hSpan hcap hper) addr
  have hhalf := batchReply_dom rq merge hrq hmerge u spans σ hSpan (batchTotal_dom hrq hSpan hcap hper)
  let half (x : X) := (replayTerminalPayload (h x) (u x)).2
  let finish (p : (Bool × List Span × List Span) × HalfCode) := (p.1.1,p.2)
  have hf : Easy finish := by unfold finish; fun_prop
  have go₅ := (hf.on (fun x => (spans x,half x))).right (fun x => send (u x))
  have hfin : Dom σ (fun x => size (spans x,half x)) :=
    ((hSpan.add hhalf).add (Dom.const σ 1)).mono fun x => by rw [size_prod]; rfl
  have hresult : Dom σ (fun x => size (replayTerminalPayload (h x) (u x))) :=
    (hf.poly.length.map (fun x => (spans x,half x))).sub hfin
  refine ⟨⟨fun x => t₁ x + t₂ x + t₃ x + t₄ x + size (spans x, half x),
    (((ht₁.add ht₂).add ht₃).add ht₄).add hfin, ?_⟩, hresult⟩
  have run := (((go₁.compose go₂).compose (go₃.right (fun x => send (u x)))).compose go₄).compose go₅
  apply run.bound 4
  intro x
  have hcount : (send (u x)).count = size (u x) := rfl
  simp only [hcount, P1ChkFinal.size_listBool]
  omega

end P1SolCone.SolCone
