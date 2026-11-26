import P1SolCone.PhaseWalk

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

theorem rawRoundKeys_bounds (extra : PhaseHeader × ℕ → List FieldKey)
    {h : PhaseHeader} {ys : List ℕ} {q : FieldKey}
    (hex : ∀ y k, k ∈ extra (h,y) → k.1 ≤ h.2.1 ∧ k.2 ≤ h.1.length)
    (hq : q ∈ rawRoundKeys extra h ys) : q.1 ≤ h.2.1 ∧ q.2 ≤ h.1.length := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact phaseFieldKey_bounds _ _ _ _
  obtain ⟨y,_,hy⟩ := List.mem_flatMap.mp hq
  rcases List.mem_append.mp hy with hq | hx
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact phaseFieldKey_bounds _ _ _ _
    rcases List.mem_cons.mp hq with rfl | hq
    · exact phaseFieldKey_bounds _ _ _ _
    obtain ⟨slot,_,hj⟩ := List.mem_flatMap.mp hq
    simp only [rawSlotFields, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact phaseFieldKey_bounds _ _ _ _
  · exact hex _ _ hx

theorem phaseBatch_task {X A : Type*} [Codec A] (h : A → PhaseHeader) (keys : A → List FieldKey)
    (hh : Poly h) (hk : Poly keys) (u : X → List Bool) (a : X → A) (σ : X → ℕ)
    (hs : Dom σ (fun x => size (a x))) (hlen : ∀ x, (h (a x)).2.1 = (u x).length)
    (hc : ∀ x k, k ∈ keys (a x) → k.1 ≤ (h (a x)).2.1 ∧ k.2 ≤ (h (a x)).1.length) :
    (∃ cost : X → ℕ, Dom σ cost ∧ Task (fun x => (u x).length + cost x)
      (fun x => send (u x, a x))
      (fun x => send (u x, (a x, fetchPhaseFields (u x) (keys (a x)))))) ∧
    Dom σ (fun x => size (a x, fetchPhaseFields (u x) (keys (a x)))) := by
  let rq (p : A) := (keys p).map phaseRequest
  let merge (p : A × List (List Bool)) := fieldCache (keys p.1) p.2
  have hrq : Poly rq := hk.compose (Code.Poly.maps _ phaseRequest_poly)
  have hmerge : Poly merge := ((Easy.fst.poly.compose hk).pair Easy.snd.poly).compose fieldCache_poly
  have hclock : Dom σ (fun x => (h (a x)).1.length) :=
    ((hh.fstCompose.length.map a).sub hs).mono (fun x => (duration (h (a x)).1).le)
  have ht : Dom σ (fun x => P1Batch.total (rq (a x))) := by
    apply batchTotal_dom hrq hs hclock
    intro x q hq
    obtain ⟨k,hk',rfl⟩ := List.mem_map.mp hq
    simpa only [phaseRequest, bval_bin] using (hc x k hk').2
  have output := batchReply_dom rq merge hrq hmerge u a σ hs ht
  refine ⟨?_, ((hs.add output).add (Dom.const σ 1)).mono (fun x => by rw [size_prod]; rfl)⟩
  apply batchKeep_task rq merge [] hrq hmerge u a σ hs ht
  intro x q hq
  obtain ⟨k,hk',rfl⟩ := List.mem_map.mp hq
  simpa only [phaseRequest, bval_bin, hlen] using (hc x k hk').1

/-- Grow the raw radius a fixed number of times and fetch the last frontier.
The theorem charges one linear scan per fetch and per local rearrangement. -/
theorem rawWalk_task {X : Type*}
    (extra : PhaseHeader × ℕ → List FieldKey) (he : Poly extra)
    (u : X → List Bool) (head : X → PhaseHeader) (roots : X → List ℕ) (σ : X → ℕ)
    (hs : Dom σ (fun x => size (head x,roots x)))
    (hlen : ∀ x, (head x).2.1 = (u x).length)
    (hex : ∀ x y k, k ∈ extra (head x,y) → k.1 ≤ (head x).2.1 ∧ k.2 ≤ (head x).1.length)
    (r : ℕ) :
    let visited := fun x => rawWalk extra (u x) (head x) (roots x) r
    let result := fun x => ((head x, visited x), rawRoundCache extra (u x) (head x) (visited x))
    (∃ cost : X → ℕ, Dom σ cost ∧ Task (fun x => (3 * r + 1) * (u x).length + cost x)
      (fun x => send (u x,head x,roots x)) (fun x => send (u x,result x))) ∧
      Dom σ (fun x => size (result x)) := by
  let rq (p : PhaseHeader × List ℕ) := rawRoundKeys extra p.1 p.2
  have hq : Poly rq := rawRoundKeys_poly he
  have batch {v : X → List ℕ} (hv : Dom σ (fun x => size (head x,v x))) :=
    phaseBatch_task Prod.fst rq Easy.fst.poly hq u (fun x => (head x,v x)) σ hv hlen
      (fun x _ hk => rawRoundKeys_bounds extra (hex x) hk)
  induction r with
  | zero =>
    dsimp only [rawWalk]
    obtain ⟨⟨c,hc,hc'⟩,ho⟩ := batch hs
    exact ⟨⟨c,hc,by simpa only [Nat.mul_zero, Nat.zero_add, Nat.one_mul, rq, rawRoundCache] using hc'⟩,ho⟩
  | succ r ih =>
    let v (x : X) := rawWalk extra (u x) (head x) (roots x) r
    let state (x : X) := ((head x,v x),rawRoundCache extra (u x) (head x) (v x))
    obtain ⟨⟨cost,hcost,go⟩,hState⟩ := ih
    let step (p : (PhaseHeader × List ℕ) × FieldCache) := (p.1.1, extendRaw p.1.1 p.2 p.1.2)
    have stepPoly : Poly step := by
      have cr : Poly (fun p : (PhaseHeader × List ℕ) × FieldCache => ((p.1.1,p.2),p.1.2)) := by fun_prop
      exact Easy.fst.poly.fstCompose.pair (cr.compose extendRaw_poly)
    have hnext : Dom σ (fun x => size (step (state x))) := (stepPoly.length.map state).sub hState
    obtain ⟨c,hc,cgo⟩ := stepPoly.on hState
    let next : X → List ℕ := fun x => (step (state x)).2
    obtain ⟨⟨dt,hdt,go'⟩,hres⟩ := batch (v := next) hnext
    refine ⟨⟨fun x => cost x + c x + dt x + 1, (((hcost.add hc).add hdt).add (Dom.const σ 1)), ?_⟩, hres⟩
    apply ((go.compose (cgo.right (fun x => send (u x)))).compose go').mono
    intro x
    have hcount : (send (u x)).count = size (u x) := rfl
    simp only [hcount,P1ChkFinal.size_listBool, Nat.mul_succ, Nat.add_mul, Nat.one_mul]
    omega

end P1SolCone.SolCone
