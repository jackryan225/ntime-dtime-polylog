import P1SolCone.BatchStage

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code

def coneBefore {A S X : Type*} (step : X → S → A → S) (initial : X → S) (order : X → List A)
    (x : X) (tail : List A) : S :=
  ((order x).take ((order x).length - tail.length)).foldl (step x) (initial x)

abbrev ConeReach {A X : Type*} (order : X → List A) :=
  {p : A × List A × X // p.1 :: p.2.1 <:+ order p.2.2}

theorem coneBefore_step {A S X : Type*} (step : X → S → A → S) (initial : X → S) (order : X → List A)
    (p : ConeReach order) :
    step p.val.2.2 (coneBefore step initial order p.val.2.2 (p.val.1 :: p.val.2.1)) p.val.1 =
      coneBefore step initial order p.val.2.2 p.val.2.1 := by
  rcases p with ⟨⟨a,tail,x⟩, h⟩
  rcases h with ⟨pre,h⟩
  have e : pre ++ a :: tail = order x := h
  unfold coneBefore
  dsimp only
  rw [← e]
  simp only [List.length_append, List.length_cons]
  rw [show pre.length + (tail.length + 1) - tail.length = pre.length + 1 by omega, Nat.add_sub_cancel]
  have he : (pre ++ a :: tail).take (pre.length + 1) = pre ++ [a] := by rw [List.take_append]; simp
  rw [he, List.take_left, List.foldl_append]
  rfl

private theorem foldCost_uniform {A : Type*} (f : A → List A → ℕ) (xs : List A) (M : ℕ)
    (h : ∀ a tail, a :: tail <:+ xs → f a tail ≤ M) : Task.foldCost f xs ≤ xs.length * (M+1) + 1 := by
  induction xs with
  | nil => simp only [Task.foldCost, List.length_nil, Nat.zero_mul, Nat.zero_add, le_refl]
  | cons a xs ih =>
    have b := h a xs List.suffix_rfl
    have h' := ih (fun z tail ht => h z tail (ht.trans (List.suffix_cons a xs)))
    simp only [Task.foldCost, List.length_cons, Nat.succ_mul]
    omega

/-- Iterate a fixed phase command whose local work is bounded on reachable states. -/
theorem phaseSweep_task {A S X : Type*} [Codec A] [Codec S]
    (u : X → List Bool) (step : X → S → A → S) (initial : X → S) (order : X → List A) (σ : X → ℕ)
    (c : ℕ) (cost : ConeReach order → ℕ)
    (hcost : Dom (fun p : ConeReach order => σ p.val.2.2) cost)
    (hlen : Dom σ (fun x => (order x).length))
    (henc : Dom (fun p : ConeReach order => σ p.val.2.2) (fun p => size p.val.1))
    (exec : Task (fun p : ConeReach order => c * (u p.val.2.2).length + cost p)
      (fun p => send (p.val.1,(u p.val.2.2,coneBefore step initial order p.val.2.2 (p.val.1 :: p.val.2.1))))
      (fun p => send (u p.val.2.2,step p.val.2.2
        (coneBefore step initial order p.val.2.2 (p.val.1 :: p.val.2.1)) p.val.1))) :
    ∃ tailCost : X → ℕ, Dom σ tailCost ∧
      Task (fun x => c * (order x).length * (u x).length + tailCost x)
        (fun x => send (order x,(u x,initial x)))
        (fun x => send (u x,(order x).foldl (step x) (initial x))) := by
  obtain ⟨e,b,hb⟩ := hcost
  obtain ⟨e',b',hb'⟩ := henc
  let B (x : X) := b * (σ x + 1)^e
  let B' (x : X) := b' * (σ x + 1)^e'
  have hB : Dom σ B := ⟨e,b,fun _ => le_rfl⟩
  have hB' : Dom σ B' := ⟨e',b',fun _ => le_rfl⟩
  let enc (_ : X) (a : A) := send a
  let out (tail : List A) (x : X) := send (u x,coneBefore step initial order x tail)
  let domain (tail : List A) (x : X) := tail <:+ order x
  have stepTask := Task.sweep (p := enc) (w := out) (D := domain)
    (a := fun _ _ x => c * (u x).length + B x)
    (fun a tail x h => (List.suffix_cons a tail).trans h) ?_
  · let tailCost (x : X) := (order x).length * (B x + B' x + 1) + 1
    refine ⟨tailCost, (hlen.mul ((hB.add hB').add (Dom.const σ 1))).add (Dom.const σ 1), ?_⟩
    have run := stepTask.on (fun x : X => (⟨(order x, x), List.suffix_rfl⟩ : {i : List A × X // domain i.1 i.2}))
    refine (run.mono (fun x => ?_)).conform (fun _ => rfl) (fun x => ?_) (fun x => ?_)
    · apply (foldCost_uniform _ _ (c * (u x).length + (B x + B' x))
        (fun a tail h => ?_)).trans
      · unfold tailCost
        rw [Nat.mul_comm c (order x).length, Nat.mul_assoc]
        change (order x).length * (c * (u x).length + (B x + B' x) + 1) + 1 ≤ _
        rw [Nat.add_assoc (c * (u x).length), Nat.mul_add]
        omega
      · have hsmall := hb' (⟨(a,tail,x),h⟩ : ConeReach order)
        have he : (enc x a).count = size a := rfl
        simp only [he]
        change size a ≤ B' x at hsmall
        omega
    · simp only [out, enc, coneBefore, Nat.sub_self, List.take_zero, List.foldl_nil,
        Task.forest_send, send_prod]
    · simp only [out, coneBefore, List.length_nil, Nat.sub_zero, List.take_length]
  · refine (exec.mono (fun p => Nat.add_le_add_left (hb p) _)).conform
      (fun _ => rfl) (fun _ => rfl) (fun p => ?_)
    change send (u p.val.2.2, step p.val.2.2 _ p.val.1) = send (u p.val.2.2, _)
    rw [coneBefore_step step initial order p]

end P1SolCone.SolCone
