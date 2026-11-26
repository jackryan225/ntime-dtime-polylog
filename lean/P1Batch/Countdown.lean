import P1Batch.Defs

/-!
# P1Batch.Countdown: a binary counter counted down into a unary tally (paper lem:countdown)

Method: `Task.foldRight` over the bits (most significant bit is processed first, since the fold works from
the end of the list). The seed is the empty tally; one step turns the tally of `g` and the bit `b` into the
tally of `b + 2 g` (`dstep`, an `Easy` function: cost linear in `g`). Summed over the bits the cost is
`O(bval l + |l|)`, since the values of the proper suffixes sum to at most `bval l` (`foldCost_dstep`).
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- One countdown step: from the bit `b` and the tally of `g`, the tally of `b + 2 g`. -/
def dstep (i : Bool × Tally) : Tally := bif i.1 then () :: (i.2 ++ i.2) else i.2 ++ i.2

theorem dstep_tally (b : Bool) (g : ℕ) : dstep (b, tally g) = tally (b.toNat + 2 * g) := by
  cases b
  · show tally g ++ tally g = tally (0 + 2 * g)
    rw [show 0 + 2 * g = g + g by omega]
    simp only [tally, List.replicate_add]
  · show () :: (tally g ++ tally g) = tally (1 + 2 * g)
    rw [show 1 + 2 * g = (g + g) + 1 by omega]
    simp only [tally, List.replicate_succ, List.replicate_add]

theorem easy_double : Easy (fun t : Tally => t ++ t) := by fun_prop

theorem easy_dstep : Easy dstep :=
  Easy.ifst (f := fun t : Tally => t ++ t) (g := fun t : Tally => () :: (t ++ t)) easy_double
    ((Easy.pair (Easy.const ()) easy_double).compose Easy.cons)

theorem count_send_bits (l : List Bool) : (send l).count = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    show (send b).count + (send l).count + 1 = 2 * (l.length + 1) + 1
    have hb : (send b).count = 1 := rfl
    omega

theorem count_send_tally (g : ℕ) : (send (tally g)).count = 2 * g + 1 := by
  have h := size_tally (tally g)
  simp only [tally_length] at h
  exact h

theorem foldCost_dstep (l : List Bool) :
    Task.foldCost (fun x l => (send (x, tally (bval l))).count + (send x).count) l
      ≤ 2 * bval l + 5 * l.length + 1 := by
  induction l with
  | nil => simp [Task.foldCost]
  | cons x l ih =>
    have hx : (send x).count = 1 := rfl
    have hp : (send (x, tally (bval l))).count = (send x).count + (send (tally (bval l))).count + 1 := rfl
    have ht := count_send_tally (bval l)
    have hv : bval (x :: l) = x.toNat + 2 * bval l := rfl
    simp only [Task.foldCost, List.length_cons]
    omega

/-- **Countdown** (proof of `P1Batch.countdown`). -/
theorem countdown_proof :
    Task (fun l : List Bool => bval l + l.length) send (fun l => send (tally (bval l))) := by
  have hstep : Task (fun i : {s : Bool × List Bool × Unit // True} =>
        (send (i.val.1, tally (bval i.val.2.1))).count)
      (fun i => .fork ((fun (_ : Unit) => (send : Bool → Tree)) i.val.2.2 i.val.1)
        ((fun (l : List Bool) (_ : Unit) => send (tally (bval l))) i.val.2.1 i.val.2.2))
      (fun i => (fun (l : List Bool) (_ : Unit) => send (tally (bval l))) (i.val.1 :: i.val.2.1) i.val.2.2) :=
    (easy_dstep.on (fun i : {s : Bool × List Bool × Unit // True} =>
      (i.val.1, tally (bval i.val.2.1)))).conform (fun _ => rfl) (fun _ => rfl) (fun i => by
        show send (dstep (i.val.1, tally (bval i.val.2.1))) = send (tally (bval (i.val.1 :: i.val.2.1)))
        rw [dstep_tally]; rfl)
  have hf := Task.foldRight (X := Bool) (Y := Unit) (p := fun (_ : Unit) => (send : Bool → Tree))
    (f := fun (l : List Bool) (_ : Unit) => send (tally (bval l)))
    (seed := fun _ => Tree.atom false) (b := fun _ => 0)
    (a := fun x l _ => (send (x, tally (bval l))).count) (D := fun _ _ => True)
    (fun _ _ _ _ => trivial) (show Task _ _ _ from Task.self) hstep
  have hf' := (hf.on (fun l : List Bool => (⟨(l, ()), trivial⟩ : {s : List Bool × Unit // True}))).conform
    (b' := fun l : List Bool => 0 + Task.foldCost
      (fun x l => (send (x, tally (bval l))).count + (send x).count) l)
    (p' := fun l : List Bool => Tree.fork (send l) (Tree.atom false))
    (q' := fun l : List Bool => send (tally (bval l)))
    (fun _ => rfl) (fun l => by simp only [Task.forest_send]) (fun _ => rfl)
  have hs := (Task.supply (.atom false) (send (X := List Bool))).compose
    (Task.exchange (fun _ => .atom false) (send (X := List Bool)))
  refine (hs.compose hf').bound 8 ?_
  intro l
  have h1 := foldCost_dstep l
  have h2 := count_send_bits l
  have h3 : (Tree.atom false).count = 1 := rfl
  simp only [h3, h2]
  omega

end P1Batch
