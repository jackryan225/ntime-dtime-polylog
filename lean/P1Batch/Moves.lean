import OAI.Computability.IntegerMultiplication.Code.Slice

/-!
# P1Batch.Moves: tree regrouping tasks and a left fold whose step budget may depend on the state

* `assocL`, `assocR`: regroup `a (b c) ↔ (a b) c`; cost linear in `a` only (the third component, e.g. a long data
  suffix, is never visited).
* `swap12`: `a (b c) → b (a c)`; cost linear in `a` and `b`.
* `foldLeftS`: OpenAI's `Task.foldLeft` (Code/FoldLeft.lean), generalized so that the step budget `a y z x`
  may depend on the current state `z`; the total budget is `walkCost` along the fold. Proof adapted from OpenAI's.
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

variable {X Y Z : Type*}

theorem assocL (f g h : X → Tree) :
    Task (fun x => (f x).count) (fun x => .fork (f x) (.fork (g x) (h x)))
      (fun x => .fork (.fork (f x) (g x)) (h x)) := by
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (splitRoot 0 (fun _ => .pass)
    ((move 1 0 2).join ((pack 0).join (pack 0))))), 100, fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (f x) env
    (pile 0 (.fork (g x) (h x)) r)
  rw [pile_comm 1 _ _ 0 _ (by decide)] at h₁
  have h₂ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (f x) env
    (pile 0 (g x) (pile 0 (h x) r))
  rw [pile_comm 1 _ _ 0 _ (by decide), pile_comm 1 _ _ 0 _ (by decide)] at h₂
  have h₃ := fits_pack (f x) (g x) (pile 0 (h x) r) 0 env
  have h₄ := fits_pack (.fork (f x) (g x)) (h x) r 0 env
  refine (fits_pair (h₁.join (fits_pair (h₂.join (h₃.join h₄))))).mono ?_
  have := (f x).count_pos
  beta_reduce
  omega

theorem assocR (f g h : X → Tree) :
    Task (fun x => (f x).count) (fun x => .fork (.fork (f x) (g x)) (h x))
      (fun x => .fork (f x) (.fork (g x) (h x))) := by
  refine ⟨splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((pack 0).join ((move 1 0 2).join (pack 0))))), 100, fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (f x) env
    (pile 0 (g x) (pile 0 (h x) r))
  rw [pile_comm 1 _ _ 0 _ (by decide), pile_comm 1 _ _ 0 _ (by decide)] at h₁
  have h₂ := fits_pack (g x) (h x) (pile 1 (f x) r) 0 env
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (f x) env
    (pile 0 (.fork (g x) (h x)) r)
  rw [pile_comm 1 _ _ 0 _ (by decide)] at h₃
  have h₄ := fits_pack (f x) (.fork (g x) (h x)) r 0 env
  refine (fits_pair (fits_pair (h₁.join (h₂.join (h₃.join h₄))))).mono ?_
  have := (f x).count_pos
  beta_reduce
  omega

theorem swap12 (f g h : X → Tree) :
    Task (fun x => (f x).count + (g x).count) (fun x => .fork (f x) (.fork (g x) (h x)))
      (fun x => .fork (g x) (.fork (f x) (h x))) :=
  (((assocL f g h).compose ((Task.exchange f g).left h)).compose (assocR g f h)).bound 3
    (fun x => by omega)

/-! ## Left fold with a state-dependent step budget -/

/-- Budget along a fold: the step budget at each visited state. -/
def walkCost (a : Z → X → ℕ) (next : Z → X → Z) : Z → List X → ℕ
  | _, [] => 0
  | z, x :: l => a z x + walkCost a next (next z x) l

theorem foldCost_walk (a : Z → X → ℕ) (next : Z → X → Z) (c : X → ℕ) (z0 : Z) (L : List X) :
    ∀ (l pre : List X), pre ++ l = L →
      Task.foldCost (fun x l' => a ((L.take (L.length - (x::l').length)).foldl next z0) x + c x) l
        = walkCost a next (pre.foldl next z0) l + costSum c l + l.length + 1 := by
  intro l
  induction l with
  | nil => intro pre _; simp [Task.foldCost, walkCost]
  | cons x l ih =>
    intro pre hpre
    have h1 : L.take (L.length - (x::l).length) = pre := by
      subst hpre
      rw [show (pre ++ x :: l).length - (x :: l).length = pre.length by simp]
      exact List.take_left' rfl
    have h2 := ih (pre ++ [x]) (by subst hpre; simp)
    have hl : (x::l).length = l.length + 1 := rfl
    simp only [Task.foldCost, h1, h2, walkCost, List.foldl_append, List.foldl_cons, List.foldl_nil,
      costSum_cons]
    omega

theorem foldLeftS (p : Y → X → Tree) (u : Y → Z → Tree)
    (next : Y → Z → X → Z) (a : Y → Z → X → ℕ)
    (h : Task (fun i : X × Z × Y => a i.2.2 i.2.1 i.1)
      (fun i => .fork (p i.2.2 i.1) (u i.2.2 i.2.1))
      (fun i => u i.2.2 (next i.2.2 i.2.1 i.1))) :
    Task (fun s : List X × Z × Y =>
        walkCost (a s.2.2) (next s.2.2) s.2.1 s.1 + (Task.forest (p s.2.2) s.1).count)
      (fun s => .fork (Task.forest (p s.2.2) s.1) (u s.2.2 s.2.1))
      (fun s => u s.2.2 (s.1.foldl (next s.2.2) s.2.1)) := by
  let z (s : List X) (i : List X × Z × Y) :=
    (i.1.take (i.1.length - s.length)).foldl (next i.2.2) i.2.1
  let w (s : List X) (i : List X × Z × Y) := u i.2.2 (z s i)
  let f (i : List X × Z × Y) := p i.2.2
  let D' (s : List X) (i : List X × Z × Y) := s <:+ i.1
  have step : Task (fun i : {s : X × List X × (List X × Z × Y) // D' (s.1::s.2.1) s.2.2} =>
        a i.val.2.2.2.2 (z (i.val.1::i.val.2.1) i.val.2.2) i.val.1)
      (fun i => .fork (f i.val.2.2 i.val.1) (w (i.val.1::i.val.2.1) i.val.2.2))
      (fun i => w i.val.2.1 i.val.2.2) := by
    refine (h.on (fun i : {s : X × List X × (List X × Z × Y) // D' (s.1::s.2.1) s.2.2} =>
      (i.val.1, z (i.val.1::i.val.2.1) i.val.2.2, i.val.2.2.2.2))).conform
      (fun _ => rfl) (fun _ => rfl) ?_
    intro ⟨⟨x,l,i⟩,hee⟩
    change u _ (next _ (z (x::l) i) x) = u _ (z l i)
    congr 1
    obtain ⟨head,hq⟩ := hee
    dsimp at hq
    simp only [z, ← hq, List.length_append, List.length_cons, Nat.add_sub_cancel]
    rw [show head.length+(l.length+1)-l.length=head.length+1 by omega]
    have hh : (head ++ x::l).take (head.length+1) = head ++ [x] := by
      rw [List.take_append]
      simp
    simp [hh, List.foldl_append]
  have hm := Task.sweep (p := f) (w := w) (a := fun x l i => a i.2.2 (z (x::l) i) x) (D := D')
    (fun x l y ⟨q,hq⟩ => ⟨q++[x], by simpa using hq⟩) step
  refine (hm.on (fun i : List X × Z × Y => ⟨(i.1,i), List.suffix_rfl⟩)).conform (fun i => ?_)
    (fun i => by simp [w,z,f]) (fun i => by simp [w,z])
  refine (foldCost_walk (a i.2.2) (next i.2.2) (fun x => (p i.2.2 x).count) i.2.1 i.1 i.1 []
    (by simp)).trans ?_
  simp only [Task.forest_count, List.foldl_nil]
  omega

end P1Batch
