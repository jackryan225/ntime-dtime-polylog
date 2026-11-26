import P1SolF0R.BatchReader

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-- The local output of a batch is polynomial in its local inputs and requested field lengths. -/
theorem batch_output_dom {X A S T : Type} [Codec A] [Codec S] [Codec T]
    (rq : A × S → List P1Batch.Req) (merge : (A × S) × List (List Bool) → T)
    (hr : Poly rq) (hm : Poly merge) (w : X → List Bool) (a : X → A) (s : X → S)
    (σ : X → ℕ) (hs : Dom σ (fun p => size (a p, s p)))
    (ht : Dom σ (fun p => P1Batch.total (rq (a p, s p)))) :
    Dom σ (fun p => size (batchAdvance rq merge (w p) (s p) (a p))) := by
  let small (p : X) := (a p, s p)
  let qs (p : X) := rq (small p)
  let fields (p : X) := (qs p).map (P1Batch.fetch (w p))
  have hq : Dom σ (fun p => size (qs p)) := (hr.length.map small).sub hs
  have hf : Dom σ (fun p => size (fields p)) :=
    ((((Dom.const σ 2).mul ht).add ((Dom.const σ 2).mul hq)).add (Dom.const σ 1)).mono
      (fun p => P1ChkFinal.size_fields (w p) (qs p))
  have hmerge : Dom σ (fun p => size (small p, fields p)) :=
    ((hs.add hf).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  exact (hm.length.map (fun p => (small p, fields p))).sub hmerge

/-- Run the witness batch and then the input batch, using the measured tape lengths for clipping. -/
theorem twoBatches_task {X A S T R : Type} [Codec A] [Codec S] [Codec T] [Codec R]
    (rq₁ : A × S → List P1Batch.Req) (merge₁ : (A × S) × List (List Bool) → T)
    (rq₂ : A × T → List P1Batch.Req) (merge₂ : (A × T) × List (List Bool) → R)
    (hr₁ : Poly rq₁) (hm₁ : Poly merge₁) (hr₂ : Poly rq₂) (hm₂ : Poly merge₂)
    (x u : X → List Bool) (a : X → A) (s : X → S) (σ : X → ℕ)
    (hin : Dom σ (fun p => size (((x p).length, (u p).length), (a p, s p))))
    (ht₁ : Dom σ (fun p => P1Batch.total (rq₁ (a p, s p))))
    (ht₂ : Dom σ (fun p => P1Batch.total (rq₂ (a p, batchAdvance rq₁ merge₁ (u p) (s p) (a p))))) :
    ∃ c : X → ℕ, Dom σ c ∧
      Task (fun p => (x p).length + (u p).length + c p)
        (fun p => send ((x p, u p), (((x p).length, (u p).length), (a p, s p))))
        (fun p => send (batchAdvance rq₂ merge₂ (x p) (batchAdvance rq₁ merge₁ (u p) (s p) (a p)) (a p))) := by
  let t (p : X) := batchAdvance rq₁ merge₁ (u p) (s p) (a p)
  let r (p : X) := batchAdvance rq₂ merge₂ (x p) (t p) (a p)
  let inSmall (p : X) := (((x p).length, (u p).length), (a p, s p))
  let between (p : X) := ((x p).length, a p, t p)
  have hs₁ : Dom σ (fun p => size ((u p).length, a p, s p)) :=
    hin.mono (fun p => by simp only [size_prod]; omega)
  have hs : Dom σ (fun p => size (a p, s p)) :=
    hin.mono (fun p => by simp only [size_prod]; omega)
  have hmid : Dom σ (fun p => size ((x p).length, a p)) :=
    hin.mono (fun p => by simp only [size_prod]; omega)
  have ht := batch_output_dom rq₁ merge₁ hr₁ hm₁ u a s σ hs ht₁
  have hbetween : Dom σ (fun p => size (between p)) :=
    ((hmid.add ht).add (Dom.const σ 1)).mono (fun p => by simp only [between, t, size_prod]; omega)
  obtain ⟨c₁, hc₁, h₁⟩ := batchClamped_task rq₁ merge₁ hr₁ hm₁ u s a σ hs₁ ht₁
  obtain ⟨c₂, hc₂, h₂⟩ := batchClamped_task rq₂ merge₂ hr₂ hm₂ x t a σ hbetween ht₂
  have e₁ : Easy (fun q : (List Bool × List Bool) × ((ℕ × ℕ) × (A × S)) =>
    (((q.2.1.2, q.2.2.1), (q.1.2, q.2.2.2)), (q.1.1, (q.2.1.1, q.2.2.1)))) := by
    fun_prop
  have e₂ : Easy (fun q : (List Bool × T) × (List Bool × (ℕ × A)) =>
    (q.2.2, (q.2.1, q.1.2))) := by fun_prop
  have first := h₁.left (fun p => send (x p, ((x p).length, a p)))
  have omitWitness := e₂.on (fun p => ((u p, t p), (x p, ((x p).length, a p))))
  have after := Task.dropLeft (fun p => send (x p)) (fun p => send (r p))
  have task := (((e₁.on (fun p => ((x p, u p), inSmall p))).compose first).compose
    omitWitness).compose (h₂.compose after)
  let cost (p : X) := size (inSmall p) + size (between p) + c₁ p + c₂ p + 1
  refine ⟨cost, (((hin.add hbetween).add hc₁).add hc₂).add (Dom.const σ 1), ?_⟩
  refine task.bound 12 (fun p => ?_)
  change
    size ((x p, u p), inSmall p) + ((u p).length + c₁ p) +
      size ((u p, t p), (x p, ((x p).length, a p))) + ((x p).length + c₂ p + size (x p)) + 1 ≤ _
  simp only [cost, between, size_prod, P1ChkFinal.size_listBool]
  omega

/-- Read one field from a concatenation of equal-width groups. -/
theorem readAt_flatMap_groups {A E : Type} (defaultValue : E) (f : A → List E) (w : ℕ)
    (xs : List A) (h : ∀ a ∈ xs, (f a).length = w)
    (i j : ℕ) (hi : i < xs.length) (hj : j < w) :
    readAt defaultValue (xs.flatMap f) (w * i + j) =
      readAt defaultValue (f xs[i]) j := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hi
  | cons a xs ih =>
    have hw := h a List.mem_cons_self
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero, readAt]
      rw [List.getElem?_append_left (by rwa [hw])]
    | succ i =>
      have hi' : i < xs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hlow : (f a).length ≤ w * (i + 1) + j := by rw [hw, Nat.mul_succ]; omega
      have hoff : w * (i + 1) + j - (f a).length = w * i + j := by rw [hw, Nat.mul_succ]; omega
      simp only [List.flatMap_cons, List.getElem_cons_succ, readAt]
      rw [List.getElem?_append_right hlow, hoff]
      exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) i hi'

theorem total_flatMap_le {A : Type} (xs : List A) (f : A → List P1Batch.Req) (w : ℕ)
    (h : ∀ a ∈ xs, P1Batch.total (f a) ≤ w) :
    P1Batch.total (xs.flatMap f) ≤ xs.length * w := by
  induction xs with
  | nil => simp only [List.flatMap_nil, P1Batch.total, List.map_nil, List.sum_nil, List.length_nil,
      Nat.zero_mul, le_refl]
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have hs := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.flatMap_cons, P1Batch.total, List.map_append, List.sum_append, List.length_cons,
      Nat.succ_mul]
    exact Nat.add_le_add ha hs |>.trans (Nat.add_comm _ _).le

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.twoBatches_task
