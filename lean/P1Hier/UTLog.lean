import P1Hier.UTDiv

/-!
# P1Hier.UTLog (copy B of lane hier): `Nat.log 2` on unary numbers in linear time

`easy_log2 : Easy (fun n : ℕ => Nat.log 2 n)`.

Method: the fold of `UTDiv` again. After `j` units the state is
`lg j = (tally (lc j), tally (lP j), tally (log₂ j))` with `lP j = 2 ^ (log₂ j + 1)` and
`lc j = lP j - 1 - j` (units left before the next power of two). A normal step drops one unit
of the counter; at a rollover (`lc j = 0`, so `j + 1 = lP j`) the state becomes
`(tally (P - 1), tally (2P), tally (log₂ j + 1))` at cost `O(P)` (`roll2_task`).
Amortized: `foldCost ≤ 5 j + 2 lc j + 1` (`foldCost_log`).
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

def lP (j : ℕ) : ℕ := 2 ^ (Nat.log 2 j + 1)

def lc (j : ℕ) : ℕ := lP j - 1 - j

def lg (j : ℕ) : Tally × Tally × Tally := (tally (lc j), tally (lP j), tally (Nat.log 2 j))

theorem lt_lP (j : ℕ) : j < lP j := Nat.lt_pow_succ_log_self (by norm_num) j

theorem pow_log_le_succ (j : ℕ) : 2 ^ Nat.log 2 j ≤ j + 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp
  · exact (Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ j)

theorem lP_le (j : ℕ) : lP j ≤ 2 * j + 2 := by
  unfold lP
  rw [pow_succ]
  have := pow_log_le_succ j
  omega

theorem lc_le (j : ℕ) : lc j ≤ j + 1 := by
  unfold lc
  have := lP_le j
  omega

theorem lc_zero : lc 0 = 1 := by
  simp [lc, lP]

theorem lg_normal {j : ℕ} (h : lc j ≠ 0) :
    Nat.log 2 (j + 1) = Nat.log 2 j ∧ lP (j + 1) = lP j ∧ lc (j + 1) + 1 = lc j := by
  have hlt := lt_lP j
  have hj : j + 1 < lP j := by
    unfold lc at h
    omega
  have hlog : Nat.log 2 (j + 1) = Nat.log 2 j :=
    Nat.log_eq_of_pow_le_of_lt_pow (pow_log_le_succ j) hj
  have hP : lP (j + 1) = lP j := by
    unfold lP
    rw [hlog]
  refine ⟨hlog, hP, ?_⟩
  unfold lc at h ⊢
  rw [hP]
  omega

theorem lg_roll {j : ℕ} (h : lc j = 0) :
    Nat.log 2 (j + 1) = Nat.log 2 j + 1 ∧ lP (j + 1) = lP j + lP j ∧ lc (j + 1) = lP j - 1 := by
  have hlt := lt_lP j
  have hj : j + 1 = lP j := by
    unfold lc at h
    omega
  have hlog : Nat.log 2 (j + 1) = Nat.log 2 j + 1 := by
    rw [hj, lP, Nat.log_pow (by norm_num)]
  have hP : lP (j + 1) = lP j + lP j := by
    unfold lP
    rw [hlog]
    ring
  refine ⟨hlog, hP, ?_⟩
  unfold lc
  rw [hP]
  omega

theorem easy_tailU : Easy (fun l : Tally => l.tail) := by
  have h := Easy.listCase (X := Unit) (f := fun i : Unit × Tally => i.2) ([] : Tally) Easy.snd
  exact Task.conform h (fun _ => rfl) (fun _ => rfl) (fun l => by cases l <;> rfl)

/-- Rollover of the log fold: `(P, L) ↦ (P - 1, 2P, L + 1)` at cost `O(P)`. -/
theorem roll2_task {I : Type*} (P L : I → ℕ) :
    Task (fun i => size (tally (P i))) (fun i => send (tally (P i), tally (L i)))
      (fun i => send (tally (P i - 1), tally (P i + P i), tally (L i + 1))) := by
  have R1 := Task.right (Task.supply (Tree.atom false) (fun i => send (tally (L i))))
    (fun i => send (tally (P i)))
  have hg : Easy (fun t : Tally => (t.tail, t ++ t)) := easy_tailU.pair (easy_append easy_id easy_id)
  have R2 := Task.left (hg.on (fun i => tally (P i)))
    (fun i => Tree.fork (Tree.atom false) (send (tally (L i))))
  have R3 := regroup (fun i => send (tally (P i)).tail) (fun i => send (tally (P i) ++ tally (P i)))
    (fun i => Tree.fork (Tree.atom false) (send (tally (L i))))
  refine (Task.bound (b' := fun i => size (tally (P i))) ((R1.compose R2).compose R3) 4
    (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  · have e1 := size_tally (tally (P i))
    have e2 := size_tally (tally (P i)).tail
    have e3 : (tally (P i)).tail.length ≤ (tally (P i)).length := by simp
    show size (tally (P i)) + 0 + size (tally (P i)) + size (tally (P i)).tail + 1 ≤
      4 * (size (tally (P i)) + 1)
    omega
  · show send ((tally (P i)).tail, tally (P i) ++ tally (P i), tally (L i + 1)) =
      send (tally (P i - 1), tally (P i + P i), tally (L i + 1))
    simp only [tally, List.tail_replicate, List.replicate_add]

/-! ## The fold -/

def gA (_x : Unit) (l : List Unit) (_y : Unit) : ℕ :=
  if lc l.length = 0 then size (tally (lP l.length)) else 0

def gF (l : List Unit) (_y : Unit) : Tree := send (lg l.length)

abbrev GI := {s : Unit × List Unit × Unit // True}

def gIsA (i : GI) : Bool := decide (lc i.val.2.1.length = 0)

theorem log_step : Task (fun i : GI => gA i.val.1 i.val.2.1 i.val.2.2)
    (fun i => Tree.fork (send i.val.1) (gF i.val.2.1 i.val.2.2))
    (fun i => gF (i.val.1 :: i.val.2.1) i.val.2.2) := by
  have T2 : Task (fun i : GI => gA i.val.1 i.val.2.1 i.val.2.2) (fun i => gF i.val.2.1 i.val.2.2)
      (fun i => gF (i.val.1 :: i.val.2.1) i.val.2.2) := by
    refine leftCase gIsA (fun i => send (tally (lc i.val.2.1.length)))
      (fun i => send (tally (lP i.val.2.1.length), tally (Nat.log 2 i.val.2.1.length))) _
      ?_ ?_ ?_ ?_
    · intro i h
      have h' : lc i.val.2.1.length = 0 := of_decide_eq_true h
      refine ⟨false, ?_⟩
      show send (tally (lc i.val.2.1.length)) = _
      rw [h']
      rfl
    · intro i h
      have h' : lc i.val.2.1.length ≠ 0 := of_decide_eq_false h
      obtain ⟨m, hm⟩ : ∃ m, lc i.val.2.1.length = m + 1 :=
        ⟨lc i.val.2.1.length - 1, by omega⟩
      refine ⟨Tree.atom false, send (tally m), ?_⟩
      show send (tally (lc i.val.2.1.length)) = _
      rw [hm]
      rfl
    · have hr := roll2_task (I := {x : GI // gIsA x = true})
        (fun x => lP x.val.val.2.1.length) (fun x => Nat.log 2 x.val.val.2.1.length)
      refine (Task.bound (b' := fun x : {x : GI // gIsA x = true} =>
        gA x.val.val.1 x.val.val.2.1 x.val.val.2.2) hr 1 (fun x => ?_)).conform
        (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      · have h : lc x.val.val.2.1.length = 0 := of_decide_eq_true x.property
        show size (tally (lP x.val.val.2.1.length)) + 1 ≤
          1 * (gA x.val.val.1 x.val.val.2.1 x.val.val.2.2 + 1)
        rw [gA, if_pos h]
        omega
      · have h : lc x.val.val.2.1.length = 0 := of_decide_eq_true x.property
        obtain ⟨h1, h2, h3⟩ := lg_roll h
        show send (tally (lP x.val.val.2.1.length - 1),
            tally (lP x.val.val.2.1.length + lP x.val.val.2.1.length),
            tally (Nat.log 2 x.val.val.2.1.length + 1)) =
          send (tally (lc (x.val.val.2.1.length + 1)), tally (lP (x.val.val.2.1.length + 1)),
            tally (Nat.log 2 (x.val.val.2.1.length + 1)))
        rw [h1, h2, h3]
    · have hd := dec_task (I := {x : GI // gIsA x = false})
        (fun x => lc (x.val.val.2.1.length + 1))
        (fun x => send (tally (lP x.val.val.2.1.length), tally (Nat.log 2 x.val.val.2.1.length)))
      refine (Task.bound (b' := fun x : {x : GI // gIsA x = false} =>
        gA x.val.val.1 x.val.val.2.1 x.val.val.2.2) hd 2 (fun x => ?_)).conform
        (fun _ => rfl) (fun x => ?_) (fun x => ?_)
      · show 1 + 1 ≤ 2 * (gA x.val.val.1 x.val.val.2.1 x.val.val.2.2 + 1)
        omega
      · have h : lc x.val.val.2.1.length ≠ 0 := of_decide_eq_false x.property
        obtain ⟨-, -, h3⟩ := lg_normal h
        show Tree.fork (send (tally (lc (x.val.val.2.1.length + 1) + 1))) _ =
          Tree.fork (send (tally (lc x.val.val.2.1.length))) _
        rw [h3]
      · have h : lc x.val.val.2.1.length ≠ 0 := of_decide_eq_false x.property
        obtain ⟨h1, h2, -⟩ := lg_normal h
        show send (tally (lc (x.val.val.2.1.length + 1)), tally (lP x.val.val.2.1.length),
            tally (Nat.log 2 x.val.val.2.1.length)) =
          send (tally (lc (x.val.val.2.1.length + 1)), tally (lP (x.val.val.2.1.length + 1)),
            tally (Nat.log 2 (x.val.val.2.1.length + 1)))
        rw [h1, h2]
  have T1 := Task.dropLeft (fun i : GI => send i.val.1) (fun i => gF i.val.2.1 i.val.2.2)
  refine Task.bound (T1.compose T2) 2 (fun i => ?_)
  show (send i.val.1).count + gA i.val.1 i.val.2.1 i.val.2.2 + 1 ≤
    2 * (gA i.val.1 i.val.2.1 i.val.2.2 + 1)
  have h : (send i.val.1).count = 1 := rfl
  omega

theorem foldCost_log : ∀ l : List Unit,
    Task.foldCost (fun x l => gA x l () + (send x).count) l ≤ 5 * l.length + 2 * lc l.length + 1
  | [] => by simp [Task.foldCost, lc_zero]
  | x :: l => by
    have ih := foldCost_log l
    have hx : (send x).count = 1 := rfl
    simp only [Task.foldCost, List.length_cons]
    rw [gA]
    split_ifs with h
    · obtain ⟨-, -, h3⟩ := lg_roll h
      have hs := size_tally (tally (lP l.length))
      rw [tally_length] at hs
      rw [h3]
      rw [h] at ih
      have := lt_lP l.length
      omega
    · obtain ⟨-, -, h3⟩ := lg_normal h
      omega

/-- **`log₂` on unary numbers** in linear time. -/
theorem easy_log2 : Easy (fun n : ℕ => Nat.log 2 n) := by
  have hf := Task.foldRight (X := Unit) (Y := Unit) (p := fun (_ : Unit) (x : Unit) => send x)
    (f := gF) (seed := fun y => gF [] y) (b := fun _ => 0) (a := gA)
    (D := fun _ _ => True) (fun _ _ _ _ => trivial) Task.self log_step
  have P2 := (hf.on (fun n : ℕ =>
      (⟨(tally n, ()), trivial⟩ : {s : List Unit × Unit // True}))).conform
    (p' := fun n : ℕ => Tree.fork (send (tally n)) (send (lg 0)))
    (fun _ => rfl) (fun n => by
      show Tree.fork (Task.forest send (tally n)) (gF [] ()) = _
      exact congrArg (fun t => Tree.fork t (gF [] ())) (Task.forest_send (tally n)))
    (fun _ => rfl)
  have P1 : Easy (fun n : ℕ => (tally n, lg 0)) := easy_tally.pair (Easy.const (lg 0))
  have hx : Easy (fun s : Tally × Tally × Tally => s.2.2) := Easy.sndCompose Easy.snd
  have P3 := hx.on (fun n : ℕ => lg (tally n).length)
  refine (Task.bound (b' := fun n : ℕ => size n) ((Task.compose P1 P2).compose P3) 10
    (fun n => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun n => ?_)
  · have hF := foldCost_log (tally n)
    simp only [tally_length] at hF
    have h1 := lc_le n
    have h2 := lP_le n
    have h3 : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
    show size n + (0 + Task.foldCost (fun x l => gA x l () + (send x).count) (tally n)) +
        size (lg (tally n).length) + 1 ≤ 10 * (size n + 1)
    simp only [lg, size_prod, size_tally, tally_length, size_nat']
    omega
  · show send (tally (Nat.log 2 (tally n).length)) = send (tally (Nat.log 2 n))
    simp only [tally_length]

end P1Hier.UM
