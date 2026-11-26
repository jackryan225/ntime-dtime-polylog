import P1ChkFinal.Skeleton
import P1Batch.Statement
import P1Batch.Moves
import P1SolC10P.Primitives
import P1SolFmt.Length
import P1ChkFinal.ProgC11

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- One round of local requests, keeping the witness for the next round. -/
def batchAdvance {S A T : Type*} (rq : A × S → List P1Batch.Req)
    (merge : (A × S) × List (List Bool) → T) (w : List Bool) (s : S) (a : A) : T :=
  merge ((a, s), (rq (a, s)).map (P1Batch.fetch w))

/-- A batch round charges a linear scan of the original witness and polynomial work in
the small data and the total lengths of the returned fields. -/
theorem batchAdvance_task {X S A T : Type*} [Codec S] [Codec A] [Codec T]
    (rq : A × S → List P1Batch.Req) (merge : (A × S) × List (List Bool) → T)
    (hrq : Poly (fun p => (rq p, p))) (hmerge : Poly merge)
    (w : X → List Bool) (s : X → S) (a : X → A) (σ : X → ℕ)
    (hsmall : Dom σ (fun p => size (a p, s p)))
    (hsize : Dom σ (fun p => P1Batch.total (rq (a p, s p))))
    (haddr : ∀ p, ∀ q ∈ rq (a p, s p), P1Batch.bval q.1 ≤ (w p).length) :
    ∃ localCost : X → ℕ, Dom σ localCost ∧
      Task (fun p => (w p).length + localCost p) (fun p => send (a p, (w p, s p)))
        (fun p => send (w p, batchAdvance rq merge (w p) (s p) (a p))) := by
  let small (p : X) := (a p, s p)
  let qs (p : X) := rq (small p)
  let fs (p : X) := (qs p).map (P1Batch.fetch (w p))
  have hqs : Dom σ (fun p => size (qs p)) := by
    have hs := hrq.length.mono (fun p => by simp only [size_prod]; omega :
      ∀ p : A × S, size (rq p) ≤ size (rq p, p))
    exact (hs.map small).sub hsmall
  have hfs : Dom σ (fun p => size (fs p)) :=
    ((((Dom.const σ 2).mul hsize).add ((Dom.const σ 2).mul hqs)).add (Dom.const σ 1)).mono
      (fun p => P1ChkFinal.size_fields (w p) (qs p))
  obtain ⟨cb, hb⟩ := P1Batch.batch_lookup
  obtain ⟨reqCost, hReqCost, hreq⟩ := hrq
  obtain ⟨mergeCost, hMergeCost, hm⟩ := hmerge
  have rearrange₁ : Easy (fun z : A × (List Bool × S) => (z.2.1, (z.1, z.2.2))) := by
    fun_prop
  have prepare := rearrange₁.on (fun p => (a p, (w p, s p)))
  have copy := ((Easy.clone (X := List Bool)).on w).left (fun p => send (small p))
  have request := (hreq.on small).right (fun p => send (w p, w p))
  have rearrange₂ : Easy (fun z : (List Bool × List Bool) × (List P1Batch.Req × (A × S)) =>
      ((z.1.1, z.2.1), (z.1.2, z.2.2))) := by
    fun_prop
  have route := rearrange₂.on (fun p => ((w p, w p), (qs p, small p)))
  let input (p : X) : P1Batch.BatchIn := ⟨(w p, qs p), haddr p⟩
  have read := (hb.on input).left (fun p => send (w p, small p))
  have rearrange₃ : Easy (fun z : List (List Bool) × (List Bool × (A × S)) =>
      (z.2.1, (z.2.2, z.1))) := by
    fun_prop
  have unpack := rearrange₃.on (fun p => (fs p, (w p, small p)))
  have mergeTask := (hm.on (fun p => (small p, fs p))).right (fun p => send (w p))
  have program := (((((prepare.compose copy).compose request).compose route).compose read).compose unpack).compose
    mergeTask
  let cost (p : X) := size (small p) + size (qs p) + size (fs p) + reqCost (small p) +
    (size (qs p) + P1Batch.total (qs p) + 1) ^ cb + mergeCost (small p, fs p) + 1
  have hc1 := (hReqCost.map small).sub hsmall
  have hc2 := ((hqs.add hsize).add (Dom.const σ 1)).pow cb
  have hinput : Dom σ (fun p => size (small p, fs p)) :=
    ((hsmall.add hfs).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  have hc3 := (hMergeCost.map (fun p => (small p, fs p))).sub hinput
  refine ⟨cost, (((((hsmall.add hqs).add hfs).add hc1).add hc2).add hc3).add (Dom.const σ 1), ?_⟩
  refine program.bound 20 (fun p => ?_)
  have h1 : (send (w p)).count = size (w p) := rfl
  have h2 : (send (w p, w p)).count = size (w p, w p) := rfl
  simp only [h1, h2, size_prod, P1ChkFinal.size_listBool, cost, small, fs, qs, input]
  omega


open P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

/-- Requests past the end return an empty field. Clamping makes their addresses admissible. -/
def clamp (p : ℕ × P1Batch.Req) : P1Batch.Req :=
  bif decide (p.1 < P1Batch.bval p.2.1) then (binary p.1, p.2.2) else p.2

theorem clamp_poly : Poly clamp := by
  unfold clamp
  have ht := P1SolC10P.SolC10prog.poly_lt
    (show Poly (fun p : ℕ × P1Batch.Req => p.1) from by fun_prop)
    (show Poly (fun p : ℕ × P1Batch.Req => P1Batch.bval p.2.1) from by fun_prop)
  exact ht.choose (by fun_prop) (by fun_prop)

theorem clamp_length (m : ℕ) (q : P1Batch.Req) : (clamp (m, q)).2 = q.2 := by
  unfold clamp
  cases decide (m < P1Batch.bval q.1) <;> rfl

theorem clamp_address (m : ℕ) (q : P1Batch.Req) :
    P1Batch.bval (clamp (m, q)).1 ≤ m := by
  by_cases hq : m < P1Batch.bval q.1
  · simp only [clamp, hq, decide_true, Bool.cond_true, bval_binary, le_refl]
  · simpa only [clamp, hq, decide_false, Bool.cond_false] using Nat.le_of_not_gt hq

theorem fetch_clamp (w : List Bool) (q : P1Batch.Req) :
    P1Batch.fetch w (clamp (w.length, q)) = P1Batch.fetch w q := by
  by_cases hq : w.length < P1Batch.bval q.1
  · simp only [clamp, hq, decide_true, Bool.cond_true, P1Batch.fetch, bval_binary,
      List.drop_length, List.drop_eq_nil_of_le hq.le]
  · simp only [clamp, hq, decide_false, Bool.cond_false]

theorem total_clamp (m : ℕ) (qs : List P1Batch.Req) :
    P1Batch.total (qs.map fun q => clamp (m, q)) = P1Batch.total qs := by
  simp only [P1Batch.total, List.map_map, Function.comp_def, clamp_length]

theorem length_task : Computes (fun w : List Bool => w.length) (fun w => w.length) := by
  refine (P1ChkFinal.lenHyp_bin P1SolFmt.SolLength.lenHyp).conform
    (fun _ => rfl) (fun _ => rfl) (fun w => ?_)
  change send (P1ChkFinal.bin w.length) = send (binary w.length)
  rw [P1SolC10P.SolC10prog.binary_eq_bin]

/-- A total batch stage. The supplied length word makes every clipped query admissible. -/
theorem batchClamped_task {X S A T : Type*} [Codec S] [Codec A] [Codec T]
    (rq : A × S → List P1Batch.Req)
    (merge : (A × S) × List (List Bool) → T)
    (hrq : Poly rq) (hmerge : Poly merge)
    (w : X → List Bool) (s : X → S) (a : X → A) (σ : X → ℕ)
    (hsmall : Dom σ (fun p => size ((w p).length, a p, s p)))
    (hsize : Dom σ (fun p => P1Batch.total (rq (a p, s p)))) :
    ∃ localCost : X → ℕ, Dom σ localCost ∧
      Task (fun p => (w p).length + localCost p)
        (fun p => send (((w p).length, a p), (w p, s p)))
        (fun p => send (w p, batchAdvance rq merge (w p) (s p) (a p))) := by
  let rq' (p : (ℕ × A) × S) := (rq (p.1.2, p.2)).map fun q => clamp (p.1.1, q)
  let merge' (p : ((ℕ × A) × S) × List (List Bool)) := merge ((p.1.1.2, p.1.2), p.2)
  have hrq' : Poly (fun p => (rq' p, p)) := by
    have hp : Poly (fun p : (ℕ × A) × S => (p.1.2, p.2)) := by fun_prop
    have hlen : Poly (fun p : (ℕ × A) × S => p.1.1) := by fun_prop
    exact ((hlen.pair (hp.compose hrq)).compose
      (Poly.push (0 : ℕ) (([], []) : P1Batch.Req) clamp_poly)).pair Poly.identity
  have hmerge' : Poly merge' :=
    (show Poly (fun p : ((ℕ × A) × S) × List (List Bool) => ((p.1.1.2, p.1.2), p.2)) from
      by fun_prop).compose hmerge
  have hs : Dom σ (fun p => size (((w p).length, a p), s p)) := by
    apply hsmall.mono
    intro p
    simp only [size_prod]
    omega
  have ht : Dom σ (fun p => P1Batch.total (rq' (((w p).length, a p), s p))) := by
    simpa only [rq', total_clamp] using hsize
  obtain ⟨c, hc, hrun⟩ := batchAdvance_task rq' merge' hrq' hmerge' w s
    (fun p => ((w p).length, a p)) σ hs ht (fun p q hq => by
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
      exact clamp_address (w p).length r)
  refine ⟨c, hc, hrun.conform (fun _ => rfl) (fun _ => rfl) (fun p => ?_)⟩
  simp only [batchAdvance, merge', rq', List.map_map, Function.comp_def, fetch_clamp]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.batchAdvance_task
