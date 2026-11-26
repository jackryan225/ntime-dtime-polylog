import P1Hier.UTCore

/-!
# P1Hier.UTDiv (copy B of lane hier): unary division in linear time

`easy_div : Easy (fun i : ℕ × ℕ => i.1 / (i.2 + 1))`.

Method: OpenAI's `Task.foldRight` over the units of the dividend; the divisor tally `y`
(length `d ≥ 1`) is the seed parameter. After `k` units the state is
`cnt k y = (tally (d - 1 - k % d), y, tally (k / d))`. A normal step removes one unit of the
first counter (constant cost, `dec_task`); when the counter is empty (`k % d = d - 1`) the step
reloads it from a copy of `y` and adds one unit to the quotient (cost `O(d)`, `roll_task`).
The branch is `leftCase` (atom or fork at the root-left). Amortized:
`foldCost + 3 (k mod d) ≤ 5 k + 1` (`foldCost_div`).
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

theorem dmod_roll {k d : ℕ} (hd : 1 ≤ d) (h : k % d = d - 1) :
    (k + 1) / d = k / d + 1 ∧ (k + 1) % d = 0 := by
  have h1 := Nat.div_add_mod k d
  refine (Nat.div_mod_unique (by omega)).mpr ⟨?_, by omega⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem dmod_step {k d : ℕ} (h : k % d < d - 1) :
    (k + 1) / d = k / d ∧ (k + 1) % d = k % d + 1 := by
  have h1 := Nat.div_add_mod k d
  refine (Nat.div_mod_unique (by omega)).mpr ⟨?_, by omega⟩
  omega

theorem send_cons_tail (y : Tally) (h : 1 ≤ y.length) :
    send y = Tree.fork (Tree.atom false) (send y.tail) := by
  cases y with
  | nil => simp at h
  | cons u t => rfl

/-! ## The two kinds of step, for any index type -/

/-- Rollover: `(y, m) ↦ (y.tail, y, m + 1)` at cost `O(|y|)`. -/
theorem roll_task {I : Type*} (y : I → Tally) (m : I → ℕ) (hy : ∀ i, 1 ≤ (y i).length) :
    Task (fun i => size (y i)) (fun i => send (y i, tally (m i)))
      (fun i => send ((y i).tail, y i, tally (m i + 1))) := by
  have R1 := Task.right (Task.supply (Tree.atom false) (fun i => send (tally (m i))))
    (fun i => send (y i))
  have R2 := Task.left (Task.copy (fun i => send (y i)))
    (fun i => Tree.fork (Tree.atom false) (send (tally (m i))))
  have R3 := regroup (fun i => send (y i)) (fun i => send (y i))
    (fun i => Tree.fork (Tree.atom false) (send (tally (m i))))
  have R4 := (Task.left (Task.dropLeft (fun _ => Tree.atom false) (fun i => send (y i).tail))
    (fun i => Tree.fork (send (y i)) (Tree.fork (Tree.atom false) (send (tally (m i)))))).conform
    (p' := fun i => Tree.fork (send (y i))
      (Tree.fork (send (y i)) (Tree.fork (Tree.atom false) (send (tally (m i))))))
    (fun _ => rfl) (fun i => by
      show Tree.fork (Tree.fork (Tree.atom false) (send (y i).tail))
          (Tree.fork (send (y i)) (Tree.fork (Tree.atom false) (send (tally (m i))))) =
        Tree.fork (send (y i)) (Tree.fork (send (y i)) (Tree.fork (Tree.atom false) (send (tally (m i)))))
      rw [send_cons_tail (y i) (hy i)]) (fun _ => rfl)
  refine (Task.bound (b' := fun i => size (y i)) (((R1.compose R2).compose R3).compose R4) 4
    (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  show (send (y i)).count + 0 + (send (y i)).count + (send (y i)).count +
      (Tree.atom false).count + 1 ≤ 4 * ((send (y i)).count + 1)
  simp only [Tree.count]
  omega

/-- Normal step: drop one unit of the counter at the root-left. -/
theorem dec_task {I : Type*} (c : I → ℕ) (R : I → Tree) :
    Task (fun _ => 1) (fun i => Tree.fork (send (tally (c i + 1))) (R i))
      (fun i => Tree.fork (send (tally (c i))) (R i)) :=
  Task.left (Task.dropLeft (fun _ => Tree.atom false) (fun i => send (tally (c i)))) R

/-! ## The fold -/

/-- State after `k` units, divisor tally `y`. -/
def cnt (k : ℕ) (y : Tally) : Tally × Tally × Tally :=
  (tally (y.length - 1 - k % y.length), y, tally (k / y.length))

/-- Step budget: `size y` at a rollover, else `0`. -/
def dA (_x : Unit) (l : List Unit) (y : Tally) : ℕ :=
  if l.length % y.length = y.length - 1 then size y else 0

def dF (l : List Unit) (y : Tally) : Tree := send (cnt l.length y)

abbrev DI := {s : Unit × List Unit × Tally // 1 ≤ s.2.2.length}

def dIsA (i : DI) : Bool :=
  decide (i.val.2.1.length % i.val.2.2.length = i.val.2.2.length - 1)

theorem div_step : Task (fun i : DI => dA i.val.1 i.val.2.1 i.val.2.2)
    (fun i => Tree.fork (send i.val.1) (dF i.val.2.1 i.val.2.2))
    (fun i => dF (i.val.1 :: i.val.2.1) i.val.2.2) := by
  have T2 : Task (fun i : DI => dA i.val.1 i.val.2.1 i.val.2.2) (fun i => dF i.val.2.1 i.val.2.2)
      (fun i => dF (i.val.1 :: i.val.2.1) i.val.2.2) := by
    refine leftCase dIsA
      (fun i => send (tally (i.val.2.2.length - 1 - i.val.2.1.length % i.val.2.2.length)))
      (fun i => send (i.val.2.2, tally (i.val.2.1.length / i.val.2.2.length))) _ ?_ ?_ ?_ ?_
    · intro i h
      have h' : i.val.2.1.length % i.val.2.2.length = i.val.2.2.length - 1 := of_decide_eq_true h
      refine ⟨false, ?_⟩
      show send (tally (i.val.2.2.length - 1 - i.val.2.1.length % i.val.2.2.length)) = _
      rw [h', Nat.sub_self]
      rfl
    · intro i h
      have h' : ¬ (i.val.2.1.length % i.val.2.2.length = i.val.2.2.length - 1) :=
        of_decide_eq_false h
      have hlt := Nat.mod_lt i.val.2.1.length (by have := i.property; omega :
        i.val.2.2.length > 0)
      obtain ⟨m, hm⟩ : ∃ m, i.val.2.2.length - 1 - i.val.2.1.length % i.val.2.2.length = m + 1 :=
        ⟨i.val.2.2.length - 1 - i.val.2.1.length % i.val.2.2.length - 1, by omega⟩
      refine ⟨Tree.atom false, send (tally m), ?_⟩
      show send (tally (i.val.2.2.length - 1 - i.val.2.1.length % i.val.2.2.length)) = _
      rw [hm]
      rfl
    · have hr := roll_task (I := {x : DI // dIsA x = true}) (fun x => x.val.val.2.2)
        (fun x => x.val.val.2.1.length / x.val.val.2.2.length) (fun x => x.val.property)
      refine (Task.bound (b' := fun x : {x : DI // dIsA x = true} =>
        dA x.val.val.1 x.val.val.2.1 x.val.val.2.2) hr 1 (fun x => ?_)).conform
        (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      · have h : x.val.val.2.1.length % x.val.val.2.2.length = x.val.val.2.2.length - 1 :=
          of_decide_eq_true x.property
        show size x.val.val.2.2 + 1 ≤ 1 * (dA x.val.val.1 x.val.val.2.1 x.val.val.2.2 + 1)
        rw [dA, if_pos h]
        omega
      · have h : x.val.val.2.1.length % x.val.val.2.2.length = x.val.val.2.2.length - 1 :=
          of_decide_eq_true x.property
        obtain ⟨h1, h2⟩ := dmod_roll x.val.property h
        show send (x.val.val.2.2.tail, x.val.val.2.2,
            tally (x.val.val.2.1.length / x.val.val.2.2.length + 1)) =
          send (tally (x.val.val.2.2.length - 1 - (x.val.val.2.1.length + 1) % x.val.val.2.2.length),
            x.val.val.2.2, tally ((x.val.val.2.1.length + 1) / x.val.val.2.2.length))
        rw [h1, h2, Nat.sub_zero, ← List.length_tail, ← tally_eq]
    · have hd := dec_task (I := {x : DI // dIsA x = false})
        (fun x => x.val.val.2.2.length - 1 - (x.val.val.2.1.length + 1) % x.val.val.2.2.length)
        (fun x => send (x.val.val.2.2, tally (x.val.val.2.1.length / x.val.val.2.2.length)))
      have key : ∀ x : {x : DI // dIsA x = false},
          x.val.val.2.1.length % x.val.val.2.2.length < x.val.val.2.2.length - 1 := by
        intro x
        have h' : ¬ (x.val.val.2.1.length % x.val.val.2.2.length = x.val.val.2.2.length - 1) :=
          of_decide_eq_false x.property
        have hlt := Nat.mod_lt x.val.val.2.1.length (by have := x.val.property; omega :
          x.val.val.2.2.length > 0)
        omega
      refine (Task.bound (b' := fun x : {x : DI // dIsA x = false} =>
        dA x.val.val.1 x.val.val.2.1 x.val.val.2.2) hd 2 (fun x => ?_)).conform
        (fun _ => rfl) (fun x => ?_) (fun x => ?_)
      · show 1 + 1 ≤ 2 * (dA x.val.val.1 x.val.val.2.1 x.val.val.2.2 + 1)
        omega
      · obtain ⟨-, h2⟩ := dmod_step (key x)
        have hc : x.val.val.2.2.length - 1 - (x.val.val.2.1.length + 1) % x.val.val.2.2.length + 1 =
            x.val.val.2.2.length - 1 - x.val.val.2.1.length % x.val.val.2.2.length := by
          have := key x
          omega
        show Tree.fork (send (tally (x.val.val.2.2.length - 1 -
            (x.val.val.2.1.length + 1) % x.val.val.2.2.length + 1))) _ =
          Tree.fork (send (tally (x.val.val.2.2.length - 1 -
            x.val.val.2.1.length % x.val.val.2.2.length))) _
        rw [hc]
      · obtain ⟨h1, -⟩ := dmod_step (key x)
        show send (tally (x.val.val.2.2.length - 1 -
            (x.val.val.2.1.length + 1) % x.val.val.2.2.length),
            x.val.val.2.2, tally (x.val.val.2.1.length / x.val.val.2.2.length)) =
          send (tally (x.val.val.2.2.length - 1 - (x.val.val.2.1.length + 1) % x.val.val.2.2.length),
            x.val.val.2.2, tally ((x.val.val.2.1.length + 1) / x.val.val.2.2.length))
        rw [h1]
  have T1 := Task.dropLeft (fun i : DI => send i.val.1) (fun i => dF i.val.2.1 i.val.2.2)
  refine Task.bound (T1.compose T2) 2 (fun i => ?_)
  show (send i.val.1).count + dA i.val.1 i.val.2.1 i.val.2.2 + 1 ≤
    2 * (dA i.val.1 i.val.2.1 i.val.2.2 + 1)
  have h : (send i.val.1).count = 1 := rfl
  omega

/-- Amortized cost of the fold. -/
theorem foldCost_div (y : Tally) (hy : 1 ≤ y.length) : ∀ l : List Unit,
    Task.foldCost (fun x l => dA x l y + (send x).count) l + 3 * (l.length % y.length) ≤
      5 * l.length + 1
  | [] => by simp [Task.foldCost]
  | x :: l => by
    have ih := foldCost_div y hy l
    have hx : (send x).count = 1 := rfl
    have hs : size y = 2 * y.length + 1 := size_tally y
    simp only [Task.foldCost, List.length_cons]
    rw [dA]
    split_ifs with h
    · obtain ⟨-, h2⟩ := dmod_roll hy h
      rw [h2]
      rw [h] at ih
      omega
    · have hlt := Nat.mod_lt l.length (by omega : y.length > 0)
      obtain ⟨-, h2⟩ := dmod_step (by omega : l.length % y.length < y.length - 1)
      rw [h2]
      omega

/-- **Unary division** `a / (e + 1)` in linear time. -/
theorem easy_div : Easy (fun i : ℕ × ℕ => i.1 / (i.2 + 1)) := by
  have hf := Task.foldRight (X := Unit) (Y := Tally) (p := fun (_ : Tally) (x : Unit) => send x)
    (f := dF) (seed := fun y => dF [] y) (b := fun _ => 0) (a := dA)
    (D := fun _ y => 1 ≤ y.length) (fun _ _ _ h => h) Task.self div_step
  have P2 := (hf.on (fun i : ℕ × ℕ =>
      (⟨(tally i.1, tally (i.2 + 1)), by simp⟩ : {s : List Unit × Tally // 1 ≤ s.2.length}))).conform
    (p' := fun i : ℕ × ℕ => Tree.fork (send (tally i.1))
      (send (tally i.2, tally (i.2 + 1), (tally 0 : Tally))))
    (fun _ => rfl) (fun i => by
      show Tree.fork (Task.forest send (tally i.1)) (dF [] (tally (i.2 + 1))) = _
      rw [Task.forest_send]
      simp only [dF, cnt, tally_length, List.length_nil, Nat.zero_mod, Nat.zero_div, Nat.sub_zero,
        Nat.add_sub_cancel])
    (fun _ => rfl)
  have hseed : Easy (fun e : ℕ => (tally e, tally (e + 1), (tally 0 : Tally))) := by
    have h2 : Easy (fun e : ℕ => tally (e + 1)) := ((Easy.const ()).pair easy_tally).compose Easy.cons
    exact easy_tally.pair (h2.pair (Easy.const (tally 0)))
  have P1 := Task.right (hseed.on (fun i : ℕ × ℕ => i.2)) (fun i : ℕ × ℕ => send (tally i.1))
  have hx : Easy (fun s : Tally × Tally × Tally => s.2.2) := Easy.sndCompose Easy.snd
  have P3 := hx.on (fun i : ℕ × ℕ => cnt (tally i.1).length (tally (i.2 + 1)))
  refine (Task.bound (b' := fun i : ℕ × ℕ => size i) ((P1.compose P2).compose P3) 12
    (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  · have hF := foldCost_div (tally (i.2 + 1)) (by simp) (tally i.1)
    simp only [tally_length] at hF
    have hq : i.1 / (i.2 + 1) ≤ i.1 := Nat.div_le_self _ _
    show size (tally i.1) + size i.2 +
        (0 + Task.foldCost (fun x l => dA x l (tally (i.2 + 1)) + (send x).count) (tally i.1)) +
        size (cnt (tally i.1).length (tally (i.2 + 1))) + 1 ≤ 12 * (size i + 1)
    simp only [cnt, size_prod, size_tally, tally_length, size_nat']
    omega
  · show send (tally ((tally i.1).length / (tally (i.2 + 1)).length)) =
      send (tally (i.1 / (i.2 + 1)))
    simp only [tally_length]

end P1Hier.UM
