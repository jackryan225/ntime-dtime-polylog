import P1Batch.Statement
import P1Batch.Sort

namespace P1ProgDir.SolScanSlice

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits

/-- A large contiguous slice needs no polynomial-time batched planning. -/
def slice (p : (Tally × Tally) × List Bool) : List Bool :=
  (cutLists (p.1.2, (cutLists (p.1.1, p.2)).2)).1

theorem easy_slice : Easy slice := by
  have ha : Easy (fun p : (Tally × Tally) × List Bool => p.1.1) :=
    Easy.fst.compose Easy.fst
  have hb : Easy (fun p : (Tally × Tally) × List Bool => p.1.2) :=
    Easy.fst.compose Easy.snd
  exact (easy_cut (hb.pair (easy_cut (ha.pair Easy.snd)).sndCompose)).fstCompose

theorem slice_of_slice (w : Word) (a l j k : ℕ) (h : j + k ≤ l) :
    ((((w.drop a).take l).drop j).take k) = (w.drop (a + j)).take k := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (show k ≤ l - j by omega), List.drop_drop]

def binarySlice (p : P1Batch.Req × List Bool) : List Bool := P1Batch.fetch p.2 p.1

theorem binarySlice_task : Computes
    (fun p : P1Batch.Req × List Bool => p.2.length + size p.1 + P1Batch.bval p.1.1 + P1Batch.bval p.1.2)
    binarySlice := by
  let P := P1Batch.Req × List Bool
  let t₁ (p : P) := tally (P1Batch.bval p.1.1)
  let t₂ (p : P) := tally (P1Batch.bval p.1.2)
  have h1 := (P1Batch.countdown.on (fun p : P => p.1.1)).left (fun p => send p.1.2)
  have h2 := (P1Batch.countdown.on (fun p : P => p.1.2)).right (fun p => send (t₁ p))
  have h3 : Task (fun p : P => size p.1.1 + size p.1.2 + 3 * P1Batch.bval p.1.1 + P1Batch.bval p.1.2 + 1)
      (fun p => send p.1) (fun p => send (t₁ p, t₂ p)) := by
    refine (h1.compose h2).mono ?_
    intro p
    change P1Batch.bval p.1.1 + p.1.1.length + (size (t₁ p) +
      (P1Batch.bval p.1.2 + p.1.2.length)) ≤ _
    simp only [t₁, size_tally, tally_length, size_word]
    omega
  have h4 := (h3.left (fun p : P => send p.2)).compose
    (easy_slice.on (fun p : P => ((t₁ p, t₂ p), p.2)))
  refine (h4.conform (fun _ => rfl) (fun _ => rfl) (fun p => ?_)).bound 6 ?_
  · simp only [binarySlice, slice, cutLists, P1Batch.fetch, t₁, t₂, tally_length]
  · intro p
    simp only [size_prod, t₁, t₂, size_tally, tally_length, size_word]
    omega

/-- Use a large slice only with validated endpoints, so the two countdowns
are bounded by the witness length. -/
theorem boundedSlice {X : Type*} (q : X → P1Batch.Req) (w : X → List Bool)
    (h : ∀ x, P1Batch.bval (q x).1 + P1Batch.bval (q x).2 ≤ (w x).length) :
    Task (fun x => (w x).length + size (q x))
      (fun x => send (q x, w x))
      (fun x => send (P1Batch.fetch (w x) (q x))) := by
  refine (binarySlice_task.on (fun x => (q x, w x))).bound 2 ?_
  intro x
  have hx := h x
  change (w x).length + size (q x) + P1Batch.bval (q x).1 + P1Batch.bval (q x).2 + 1 ≤ _
  omega

#print axioms binarySlice_task
#print axioms boundedSlice

end P1ProgDir.SolScanSlice
