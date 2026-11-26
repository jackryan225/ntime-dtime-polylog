import P1ChkFinal.Skeleton
import P1Batch.Statement
import P1Batch.Moves

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- One round of local requests, keeping the witness for the next round. -/
def batchAdvance {S A : Type*} (rq : A × S → List P1Batch.Req)
    (merge : (A × S) × List (List Bool) → S) (w : List Bool) (s : S) (a : A) : S :=
  merge ((a, s), (rq (a, s)).map (P1Batch.fetch w))

/-- A batch round charges a linear scan of the original witness and polynomial work in
the small data and the total lengths of the returned fields. -/
theorem batchAdvance_task {X S A : Type*} [Codec S] [Codec A]
    (rq : A × S → List P1Batch.Req) (merge : (A × S) × List (List Bool) → S)
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

/-- State before reading the first entry of the given suffix of the schedule. -/
def beforeSuffix {S A : Type*} (rq : A × S → List P1Batch.Req)
    (merge : (A × S) × List (List Bool) → S) (w : List Bool) (s : S) (schedule suffix : List A) : S :=
  (schedule.take (schedule.length - suffix.length)).foldl (batchAdvance rq merge w) s

private theorem beforeSuffix_step {S A : Type*} (rq : A × S → List P1Batch.Req)
    (merge : (A × S) × List (List Bool) → S) (w : List Bool) (s : S)
    {schedule : List A} {a : A} {tail : List A} (h : a :: tail <:+ schedule) :
    batchAdvance rq merge w (beforeSuffix rq merge w s schedule (a :: tail)) a =
      beforeSuffix rq merge w s schedule tail := by
  obtain ⟨pre, rfl⟩ := h
  simp only [beforeSuffix, List.length_append, List.length_cons]
  rw [show pre.length + (tail.length + 1) - tail.length = pre.length + 1 by omega,
    Nat.add_sub_cancel]
  have hp : (pre ++ a :: tail).take (pre.length + 1) = pre ++ [a] := by
    rw [List.take_append]
    simp
  rw [hp, List.take_left, List.foldl_append]
  rfl

private theorem foldCost_le_uniform {A : Type*} (weight : A → List A → ℕ) (xs : List A) (B : ℕ)
    (h : ∀ a tail, a :: tail <:+ xs → weight a tail ≤ B) :
    Task.foldCost weight xs ≤ xs.length * (B + 1) + 1 := by
  induction xs with
  | nil => simp only [Task.foldCost, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons a xs ih =>
    have h1 := h a xs List.suffix_rfl
    have h2 := ih (fun q tail ht => h q tail (ht.trans (List.suffix_cons a xs)))
    simp only [Task.foldCost, List.length_cons, Nat.succ_mul]
    omega

/-- Run a variable number of batch rounds with one fixed command. Address and size
conditions are checked on reachable states of the fold. -/
theorem batchStages_task {X S A : Type*} [Codec S] [Codec A]
    (rq : A × S → List P1Batch.Req) (merge : (A × S) × List (List Bool) → S)
    (hrq : Poly (fun p => (rq p, p))) (hmerge : Poly merge)
    (w : X → List Bool) (s : X → S) (schedule : X → List A) (σ : X → ℕ)
    (hschedule : Dom σ (fun p => (schedule p).length))
    (smallCap : X → ℕ) (hCap : Dom σ smallCap)
    (hStep : ∀ p a tail, a :: tail <:+ schedule p →
      let v := beforeSuffix rq merge (w p) (s p) (schedule p) (a :: tail)
      size (a, v) ≤ smallCap p ∧ P1Batch.total (rq (a, v)) ≤ smallCap p ∧
        ∀ q ∈ rq (a, v), P1Batch.bval q.1 ≤ (w p).length) :
    ∃ localCost : X → ℕ, Dom σ localCost ∧
      Task (fun p => (schedule p).length * (w p).length + localCost p)
        (fun p => send (schedule p, (w p, s p)))
        (fun p => send (w p, (schedule p).foldl (batchAdvance rq merge (w p)) (s p))) := by
  let D (tail : List A) (p : X) := tail <:+ schedule p
  let Reach := {i : A × List A × X // D (i.1 :: i.2.1) i.2.2}
  let v (tail : List A) (p : X) := beforeSuffix rq merge (w p) (s p) (schedule p) tail
  let state (i : Reach) := v (i.val.1 :: i.val.2.1) i.val.2.2
  let base (i : Reach) := i.val.2.2
  have hs (i : Reach) := hStep (base i) i.val.1 i.val.2.1 i.property
  obtain ⟨cost, hcost, go⟩ := batchAdvance_task rq merge hrq hmerge (w ∘ base) state
    (fun i => i.val.1) (σ ∘ base) ((hCap.map base).mono fun i => (hs i).1)
    ((hCap.map base).mono fun i => (hs i).2.1) (fun i => (hs i).2.2)
  obtain ⟨e, c, hc⟩ := hcost
  let enc (_ : X) (a : A) := send a
  let out (tail : List A) (p : X) := send (w p, v tail p)
  let up (p : X) := c * (σ p + 1) ^ e + smallCap p
  have hup : Dom σ up := (show Dom σ (fun p => c * (σ p + 1) ^ e) from ⟨e, c, fun _ => le_rfl⟩).add hCap
  have run := Task.sweep (p := enc) (w := out) (D := D)
    (a := fun _ _ p => (w p).length + c * (σ p + 1) ^ e)
    (fun a tail p ht => (List.suffix_cons a tail).trans ht) ?_
  · let localCost (p : X) := (schedule p).length * (up p + 1) + 1
    refine ⟨localCost, (hschedule.mul (hup.add (Dom.const σ 1))).add (Dom.const σ 1), ?_⟩
    have final := run.on (fun p : X => (⟨(schedule p, p), List.suffix_rfl⟩ : {i : List A × X // D i.1 i.2}))
    refine (final.mono (fun p => ?_)).conform (fun _ => rfl) (fun p => ?_) (fun p => ?_)
    · apply (foldCost_le_uniform _ _ ((w p).length + up p) (fun a tail ht => ?_)).trans
      · dsimp only [localCost]
        rw [show (w p).length + up p + 1 = (w p).length + (up p + 1) by omega, Nat.mul_add, Nat.add_assoc]
      · have ha := (hStep p a tail ht).1
        simp only [enc, ← Nat.add_assoc, up, size_prod] at *
        change (w p).length + c * (σ p + 1) ^ e + size a ≤ _
        omega
    · simp only [out, enc, beforeSuffix, v, Nat.sub_self, List.take_zero, List.foldl_nil,
        Task.forest_send, send_prod]
    · simp only [out, v, beforeSuffix, List.length_nil, Nat.sub_zero, List.take_length]
  · refine (go.mono (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
    · exact Nat.add_le_add_left (hc i) _
    · change send (w (base i), batchAdvance rq merge (w (base i)) (state i) i.val.1) = _
      rw [show batchAdvance rq merge (w (base i)) (state i) i.val.1 = v i.val.2.1 (base i) from
        beforeSuffix_step rq merge _ _ i.property]

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.batchAdvance_task
#print axioms P1SolCone.SolCone.batchStages_task
