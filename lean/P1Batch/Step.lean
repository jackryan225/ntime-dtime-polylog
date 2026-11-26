import P1Batch.Plan
import P1Batch.Countdown

/-!
# P1Batch.Step: one step of the scan as a stack task, budget `O(size outs + size item + gap + ℓ + 1)`

Input tree `fork (send item) (send (outs, suffix))`, output `send (scanStep (outs, suffix) item)`.
The data suffix is never visited: it is only ever the RIGHT-most component, and every move used here
(`assocL`, `assocR`, `swap12`, `Task.right`, `Computes.cut`) charges the left parts only.
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Parameter of one scan step: (item, state, unit). -/
abbrev SP := TReq × St × Unit

section Parts
variable (i : SP)
/-- The item. -/ def sIt : TReq := i.1
/-- Its tag. -/ def sTg : Tally := i.1.1
/-- Its gap word. -/ def sGW : List Bool := i.1.2.1
/-- Its length word. -/ def sLW : List Bool := i.1.2.2
/-- Records so far. -/ def sOuts : List Rec := i.2.1.1
/-- The data suffix. -/ def sSuf : List Bool := i.2.1.2
/-- Gap tally. -/ def sGT : Tally := tally (bval (sGW i))
/-- Length tally. -/ def sLT : Tally := tally (bval (sLW i))
/-- Discarded prefix. -/ def sPre : List Bool := (cutLists (sGT i, sSuf i)).1
/-- Data from the address on. -/ def sRest : List Bool := (cutLists (sGT i, sSuf i)).2
/-- The field. -/ def sFld : List Bool := (cutLists (sLT i, sRest i)).1
/-- Data after the field. -/ def sRest2 : List Bool := (cutLists (sLT i, sRest i)).2
end Parts

theorem count_send_take (l : List Bool) (k : ℕ) : (send (l.take k)).count ≤ 2 * k + 1 := by
  rw [count_send_bits]
  have := List.length_take_le k l
  omega

/-- Phase 1: count down the gap and the length of the item (in place, left of the state). -/
theorem ph1 : Task (fun i : SP => size (sIt i) + ((bval (sGW i) + (sGW i).length) +
      ((send (sGT i)).count + (bval (sLW i) + (sLW i).length))))
    (fun i => .fork (send (sIt i)) (send i.2.1))
    (fun i => .fork (.fork (send (sGT i)) (.fork (send (sLT i)) (send (sTg i)))) (send i.2.1)) := by
  have e1 : Easy (fun x : TReq => (x.2.1, (x.2.2, x.1))) := by fun_prop
  have h1a : Task (fun i : SP => size (sIt i)) (fun i => send (sIt i))
      (fun i => .fork (send (sGW i)) (.fork (send (sLW i)) (send (sTg i)))) := e1.on sIt
  have h1b : Task (fun i : SP => bval (sGW i) + (sGW i).length)
      (fun i => .fork (send (sGW i)) (.fork (send (sLW i)) (send (sTg i))))
      (fun i => .fork (send (sGT i)) (.fork (send (sLW i)) (send (sTg i)))) :=
    (countdown_proof.on sGW).left (fun i => .fork (send (sLW i)) (send (sTg i)))
  have h1c : Task (fun i : SP => (send (sGT i)).count + (bval (sLW i) + (sLW i).length))
      (fun i => .fork (send (sGT i)) (.fork (send (sLW i)) (send (sTg i))))
      (fun i => .fork (send (sGT i)) (.fork (send (sLT i)) (send (sTg i)))) :=
    ((countdown_proof.on sLW).left (fun i => send (sTg i))).right (fun i => send (sGT i))
  exact (h1a.compose (h1b.compose h1c)).left (fun i => send i.2.1)

/-- Phase 3 (inner part): on `fork item' suffix`, fetch the field; output `fork (tag, field) suffix'`. -/
theorem ph3 : Task (fun i : SP =>
      (send (sGT i)).count
      + ((send (sGT i)).count + (send (sLT i, sTg i)).count)
      + ((send (sLT i, sTg i)).count + (size (sGT i, sSuf i).1 + size (cutLists (sGT i, sSuf i)).1))
      + ((send (sLT i, sTg i)).count + (send (sPre i)).count)
      + (send (sLT i)).count
      + ((send (sLT i)).count + (send (sTg i)).count)
      + ((send (sTg i)).count + (size (sLT i, sRest i).1 + size (cutLists (sLT i, sRest i)).1))
      + ((send (sTg i)).count + (send (sFld i)).count)
      + ((send (sTg i)).count + (send (sFld i)).count)
      + ((send (sTg i)).count + ((send (sFld i)).count + size (sFld i, sRest2 i).1))
      + (send (sTg i)).count)
    (fun i => .fork (.fork (send (sGT i)) (.fork (send (sLT i)) (send (sTg i)))) (send (sSuf i)))
    (fun i => .fork (.fork (send (sTg i)) (send (sFld i))) (send (sFld i ++ sRest2 i))) := by
  have h3a := assocR (fun i : SP => send (sGT i)) (fun i => send (sLT i, sTg i)) (fun i => send (sSuf i))
  have h3b := swap12 (fun i : SP => send (sGT i)) (fun i => send (sLT i, sTg i)) (fun i => send (sSuf i))
  have h3c := ((Computes.cut (X := Bool)).on (fun i : SP => (sGT i, sSuf i))).right
    (fun i => send (sLT i, sTg i))
  have h3d := (Task.dropLeft (fun i : SP => send (sPre i)) (fun i => send (sRest i))).right
    (fun i => send (sLT i, sTg i))
  have h3e := assocR (fun i : SP => send (sLT i)) (fun i => send (sTg i)) (fun i => send (sRest i))
  have h3f := swap12 (fun i : SP => send (sLT i)) (fun i => send (sTg i)) (fun i => send (sRest i))
  have h3g := ((Computes.cut (X := Bool)).on (fun i : SP => (sLT i, sRest i))).right
    (fun i => send (sTg i))
  have h3h := ((Task.copy (fun i : SP => send (sFld i))).left (fun i => send (sRest2 i))).right
    (fun i => send (sTg i))
  have h3i := (assocR (fun i : SP => send (sFld i)) (fun i => send (sFld i))
    (fun i => send (sRest2 i))).right (fun i => send (sTg i))
  have h3j := (((Computes.append (X := Bool)).on (fun i : SP => (sFld i, sRest2 i))).right
    (fun i => send (sFld i))).right (fun i => send (sTg i))
  have h3k := assocL (fun i : SP => send (sTg i)) (fun i => send (sFld i))
    (fun i => send (sFld i ++ sRest2 i))
  exact (((((((((h3a.compose h3b).compose h3c).compose h3d).compose h3e).compose h3f).compose
    h3g).compose h3h).compose h3i).compose h3j).compose h3k

/-- **One scan step** as a stack task. -/
theorem stepTask : Task (fun i : SP => stepCost i.2.1 i.1)
    (fun i => .fork (send i.1) (send i.2.1)) (fun i => send (scanStep i.2.1 i.1)) := by
  have h2 := swap12 (fun i : SP => send (sGT i, (sLT i, sTg i))) (fun i => send (sOuts i))
    (fun i => send (sSuf i))
  have h3 := ph3.right (fun i : SP => send (sOuts i))
  have h4 := assocL (fun i : SP => send (sOuts i)) (fun i => send (sTg i, sFld i))
    (fun i => send (sFld i ++ sRest2 i))
  have h5 := (Task.exchange (fun i : SP => send (sOuts i)) (fun i => send (sTg i, sFld i))).left
    (fun i => send (sFld i ++ sRest2 i))
  refine (ph1.compose (h2.compose (h3.compose (h4.compose h5)))).bound 100 (fun i => ?_)
  have f1 : (send i.1).count
      = (send (sTg i)).count + ((send (sGW i)).count + (send (sLW i)).count + 1) + 1 := rfl
  have f2 : (send (sGW i)).count = 2 * (sGW i).length + 1 := count_send_bits _
  have f3 : (send (sLW i)).count = 2 * (sLW i).length + 1 := count_send_bits _
  have f4 : (send (sGT i)).count = 2 * bval (sGW i) + 1 := count_send_tally _
  have f5 : (send (sLT i)).count = 2 * bval (sLW i) + 1 := count_send_tally _
  have f6 : (send (sGT i, (sLT i, sTg i))).count
      = (send (sGT i)).count + ((send (sLT i)).count + (send (sTg i)).count + 1) + 1 := rfl
  have f7 : (send (sLT i, sTg i)).count = (send (sLT i)).count + (send (sTg i)).count + 1 := rfl
  have f9 : (send (cutLists (sGT i, sSuf i)).1).count ≤ 2 * (sGT i).length + 1 := count_send_take _ _
  have f9' : (sGT i).length = bval (sGW i) := tally_length _
  have f10 : (send (sPre i)).count ≤ 2 * (sGT i).length + 1 := count_send_take _ _
  have f12 : (send (cutLists (sLT i, sRest i)).1).count ≤ 2 * (sLT i).length + 1 := count_send_take _ _
  have f12' : (sLT i).length = bval (sLW i) := tally_length _
  have f13 : (send (sFld i)).count ≤ 2 * (sLT i).length + 1 := count_send_take _ _
  have f15 : (send (sTg i, sFld i)).count = (send (sTg i)).count + (send (sFld i)).count + 1 := rfl
  have f16 : (send (sOuts i)).count = (send i.2.1.1).count := rfl
  have f17 : bval (sGW i) = bval i.1.2.1 := rfl
  have f18 : bval (sLW i) = bval i.1.2.2 := rfl
  have f19 : (send (sIt i)).count = (send i.1).count := rfl
  simp only [size, stepCost] at *
  omega

end P1Batch
