import OAI.Computability.IntegerMultiplication.Code.Dup

import Mathlib.Tactic.Ring

namespace P1ProgDir.SolRows

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Split a data segment into a number of rows fixed by the input geometry. -/
def rows (p : (Tally × Tally) × List Bool) : List (List Bool) :=
  (Piecework.segment (List.replicate p.1.1.length p.1.2) p.2).1

theorem size_rulers (n : ℕ) (r : Tally) :
    size (List.replicate n r) = n * (size r + 1) + 1 := by
  induction n with
  | zero => simp only [List.replicate_zero, size_nil, Nat.zero_mul, Nat.zero_add]
  | succ n hn =>
    simp only [List.replicate_succ, size_cons, hn, Nat.succ_mul]
    omega

theorem rows_task :
    Computes (fun p : (Tally × Tally) × List Bool =>
      (p.1.1.length + 1) * (p.1.2.length + 1) + size p.2) rows := by
  let P := (Tally × Tally) × List Bool
  have h1 := (generate (X := Tally)).on (Prod.fst : P → Tally × Tally)
  have h2 := (Piecework.easy (X := Bool)).fstCompose.on
    (fun p : P => (List.replicate p.1.1.length p.1.2, p.2))
  refine ((h1.left (fun p : P => send p.2)).compose h2).bound 4 ?_
  intro p
  rw [size_prod, size_rulers, size_tally]
  -- Linear in row count times row width, plus the input traversal.
  ring_nf
  omega

theorem rows_eq {A : Type} (r : Tally) (n : ℕ) (w : List A) :
    (Piecework.segment (List.replicate n r) w).1 =
      (List.range n).map (fun j => (w.drop (j * r.length)).take r.length) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, Piecework.segment, cutLists, ih, List.range_succ_eq_map,
      List.map_cons, Nat.zero_mul, List.drop_zero, List.map_map, Function.comp_def, List.drop_drop,
      Nat.succ_mul]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [Nat.add_comm]

end P1ProgDir.SolRows
