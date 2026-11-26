import P1SolCone.BatchStage

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- The returned small state depends polynomially on the encoded request data and total requested width. -/
theorem batchReply_dom {X A R : Type*} [Codec A] [Codec R]
    (rq : A → List P1Batch.Req) (merge : A × List (List Bool) → R)
    (hrq : Poly rq) (hmerge : Poly merge)
    (u : X → List Bool) (a : X → A) (σ : X → ℕ)
    (hsize : Dom σ (fun x => size (a x))) (htotal : Dom σ (fun x => P1Batch.total (rq (a x)))) :
    Dom σ (fun x => size (merge (a x, (rq (a x)).map (P1Batch.fetch (u x))))) := by
  have rqSize := (hrq.length.map a).sub hsize
  have wordSize : Dom σ (fun x => size ((rq (a x)).map (P1Batch.fetch (u x)))) :=
    ((((Dom.const σ 2).mul htotal).add ((Dom.const σ 2).mul rqSize)).add (Dom.const σ 1)).mono
      (fun x => P1ChkFinal.size_fields (u x) (rq (a x)))
  have args : Dom σ (fun x => size (a x, (rq (a x)).map (P1Batch.fetch (u x)))) :=
    ((hsize.add wordSize).add (Dom.const σ 1)).mono (fun x => by rw [size_prod])
  exact (hmerge.length.map _).sub args

theorem batchTotal_bound (qs : List P1Batch.Req) (B : ℕ)
    (h : ∀ q ∈ qs, P1Batch.bval q.2 ≤ B) : P1Batch.total qs ≤ qs.length * B := by
  induction qs with
  | nil => simp [P1Batch.total]
  | cons q qs ih =>
    have hq := h q List.mem_cons_self
    have hs := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [P1Batch.total, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at hs ⊢
    omega

theorem batchTotal_dom {X A : Type*} [Codec A] {σ B : X → ℕ} {a : X → A} {rq : A → List P1Batch.Req}
    (hrq : Poly rq) (ha : Dom σ (fun x => size (a x))) (hB : Dom σ B)
    (h : ∀ x q, q ∈ rq (a x) → P1Batch.bval q.2 ≤ B x) :
    Dom σ (fun x => P1Batch.total (rq (a x))) := by
  have hn : Dom σ (fun x => (rq (a x)).length) :=
    ((hrq.length.map a).sub ha).mono (fun x => (duration (rq (a x))).le)
  exact (hn.mul hB).mono (fun x => batchTotal_bound _ _ (h x))

/-- A batch that retains the small input used to construct its requests. -/
theorem batchKeep_task {X A R : Type*} [Codec A] [Codec R]
    (rq : A → List P1Batch.Req) (merge : A × List (List Bool) → R) (empty : R)
    (hrq : Poly rq) (hmerge : Poly merge)
    (u : X → List Bool) (a : X → A) (σ : X → ℕ)
    (hsize : Dom σ (fun x => size (a x)))
    (htotal : Dom σ (fun x => P1Batch.total (rq (a x))))
    (haddr : ∀ x q, q ∈ rq (a x) → P1Batch.bval q.1 ≤ (u x).length) :
    ∃ cost : X → ℕ, Dom σ cost ∧ Task (fun x => (u x).length + cost x)
      (fun x => send (u x, a x))
      (fun x => send (u x, (a x, merge (a x, (rq (a x)).map (P1Batch.fetch (u x)))))) := by
  let req : Bool × (A × R) → List P1Batch.Req := fun p => rq p.2.1
  let run : (Bool × (A × R)) × List (List Bool) → A × R := fun p =>
    (p.1.2.1, merge (p.1.2.1, p.2))
  have f : Poly (fun p : Bool × (A × R) => p.2.1) := by fun_prop
  have f' : Poly (fun p : (Bool × (A × R)) × List (List Bool) => p.1.2.1) := by fun_prop
  have runPoly : Poly run := f'.pair ((f'.pair Easy.snd.poly).compose hmerge)
  have hsmall : Dom σ (fun x => size (false, (a x, empty))) := by
    refine (hsize.add (Dom.const σ (size false + size empty + 2))).mono fun x => ?_
    simp only [size_prod]
    omega
  obtain ⟨cost, hcost, task⟩ := batchAdvance_task req run ((f.compose hrq).pair Code.Poly.identity)
    runPoly u (fun x => (a x, empty)) (fun _ => false) σ hsmall htotal haddr
  have prep : Easy (fun p : List Bool × A => (false, (p.1, p.2, empty))) := by
    exact (Easy.const false).pair (Easy.fst.pair (Easy.snd.pair (Easy.const empty)))
  refine ⟨fun x => size (a x) + cost x + 1, (hsize.add hcost).add (Dom.const σ 1), ?_⟩
  have go := (prep.on (fun x => (u x, a x))).compose task
  exact go.bound 4 (fun x => by
    simp only [size_prod, P1ChkFinal.size_listBool]
    omega)

end P1SolCone.SolCone
