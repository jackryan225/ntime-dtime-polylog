import P1ProgDir.BatchCore
import P1ProgDir.FieldRead

namespace P1ProgDir.SolC1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Wit P1ProgDir.SolBatchCore P1ProgDir.SolFieldRead

abbrev Packed := (Word × Word) × Word

def requests (p : Packed) : List P1Batch.Req := c1Requests p.1

def fetched (p : Packed) : List Word := (requests p).map (P1Batch.fetch p.2)

def reply (p : Packed) : Bool := c1Reply (fetched p)

theorem reply_iff (p : Packed) :
    reply p = true ↔
      value p.1.1 ≤ value p.1.2 ∨ bitsVal ((p.2.drop (2 * value p.1.2)).take 2) < 3 := by
  have hm (q : Word × Word) : more q = true ↔ value q.2 < value q.1 := by
    rcases q with ⟨cap, i⟩
    exact more_lt cap i
  by_cases hp : value p.1.2 < value p.1.1
  · have hp' : more p.1 = true := (hm p.1).mpr hp
    unfold reply fetched requests c1Requests
    rw [ite_eq_left hp', or_iff_right (Nat.not_le.mpr hp)]
    simp only [c1Reply, List.map_cons, List.map_nil, List.headD_cons, more_lt]
    have hoff : P1Batch.bval (false :: p.1.2) = 2 * value p.1.2 := by
      rw [P1Batch.bval_eq_value, value_cons, d0, zero_add]
    have hw : P1Batch.bval [false, true] = 2 := rfl
    rw [P1Batch.fetch, hoff, hw, bitsVal_eq_value]
    rfl
  · have hp' : more p.1 ≠ true := fun h => hp ((hm p.1).mp h)
    unfold reply fetched requests c1Requests
    rw [ite_eq_right hp']
    exact iff_of_true rfl (Or.inl (Nat.le_of_not_gt hp))

abbrev ValidInput := {p : Packed // 2 * value p.1.1 ≤ p.2.length}

theorem total_le (p : Packed) : P1Batch.total (requests p) ≤ 2 := by
  unfold requests c1Requests
  split_ifs
  · exact Nat.le_refl 2
  · exact Nat.zero_le 2

theorem size_fetched (p : Packed) : size (fetched p) ≤ 7 := by
  unfold fetched requests c1Requests
  split_ifs
  · simp only [List.map_cons, List.map_nil, size_cons, size_nil, size_word]
    have h : (P1Batch.fetch p.2 (false :: p.1.2, [false, true])).length ≤ 2 := by
      rw [P1Batch.fetch, List.length_take]
      exact Nat.min_le_left _ _
    omega
  · simp only [List.map_nil, size_nil]
    decide

theorem task :
    ∃ t : Word × Word → ℕ, Dom size t ∧
      Task (fun p : ValidInput => p.val.2.length + t p.val.1)
        (fun p => send p.val) (fun p => send (reply p.val)) := by
  let batchIn (p : ValidInput) : P1Batch.BatchIn :=
    ⟨(p.val.2, requests p.val), fun q hq =>
      (Nat.le_add_right _ _).trans (c1Requests_fits p.val.2 p.val.1 p.property q hq)⟩
  obtain ⟨c, hc⟩ := P1Batch.batch_lookup
  let t (p : Word × Word) := size p + size (c1Requests p) + (size (c1Requests p) + 3)^c + 9
  have hq := (Poly.length easy_c1Requests.poly)
  have ht : Dom size t :=
    (((Dom.base _).add hq).add ((hq.add (Dom.const _ 3)).pow c)).add (Dom.const _ 9)
  refine ⟨t, ht, ?_⟩
  have h1 := (easy_c1Requests.on (fun p : ValidInput => p.val.1)).left (fun p => send p.val.2)
  have h2 := Task.exchange (fun p : ValidInput => send (requests p.val)) (fun p => send p.val.2)
  have h3 := hc.on batchIn
  have h4 := easy_c1Reply.on (fun p : ValidInput => fetched p.val)
  refine (((h1.compose h2).compose h3).compose h4).bound 3 ?_
  intro p
  have htot := total_le p.val
  have hget := size_fetched p.val
  have hp := Nat.pow_le_pow_left (show size (requests p.val) + P1Batch.total (requests p.val) + 1 ≤
      size (requests p.val) + 3 by omega) c
  change size p.val.1 + (size (requests p.val) + size p.val.2) +
      (p.val.2.length + (size (requests p.val) + P1Batch.total (requests p.val) + 1)^c) +
      size (fetched p.val) + 1 ≤
    3 * (p.val.2.length + (size p.val.1 + size (requests p.val) +
      (size (requests p.val) + 3)^c + 9) + 1)
  rw [size_word]
  omega

end P1ProgDir.SolC1Batch
