import P1SolCone.TerminalReads
import P1SolCone.FieldPrograms
import P1SolCone.BatchStage

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1ProgEng.SolKWR
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def payloadRequests (s : List Span × List Span) : List P1Batch.Req :=
  (s.1 ++ s.2).map spanRequest

def splitPayload (s : List Span × List Span) (words : List (List Bool)) : HalfCode :=
  (words.take s.1.length, words.drop s.1.length)

theorem payloadRequests_poly : Poly payloadRequests := by
  have mk : Poly spanRequest := by unfold spanRequest; fun_prop
  exact Easy.append.poly.compose (Poly.maps spanRequest mk)

theorem splitPayload_poly :
    Poly (fun p : (List Span × List Span) × List (List Bool) => splitPayload p.1 p.2) := by
  have n := poly_lengthNat (show Poly (fun p : (List Span × List Span) × List (List Bool) => p.1.1) from by fun_prop)
  exact (poly_take n Easy.snd.poly).pair (poly_drop n Easy.snd.poly)

theorem splitPayload_eq (s : List Span × List Span) (u : List Bool) :
    splitPayload s ((payloadRequests s).map (P1Batch.fetch u)) =
      (s.1.map (P1Batch.fetch u ∘ spanRequest), s.2.map (P1Batch.fetch u ∘ spanRequest)) := by
  simp only [payloadRequests, splitPayload, List.map_map, List.map_append]
  rw [← List.length_map (f := P1Batch.fetch u ∘ spanRequest) (as := s.1),
    List.take_left, List.drop_left]

theorem payloadRequests_total (s : List Span × List Span) (cap : ℕ)
    (h : ∀ z ∈ s.1 ++ s.2, z.2 ≤ cap) :
    P1Batch.total (payloadRequests s) ≤ (s.1.length + s.2.length) * cap := by
  have bound (xs : List Span) (hx : ∀ z ∈ xs, z.2 ≤ cap) :
      (xs.map Prod.snd).sum ≤ xs.length * cap := by
    induction xs with
    | nil => simp
    | cons a as ih =>
      have ht := ih (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      have ha := hx a List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  simpa only [P1Batch.total, payloadRequests, List.map_map, Function.comp_def, spanRequest, bval_bin,
    List.length_append] using bound (s.1 ++ s.2) h

theorem payloadRequests_offsets (s : List Span × List Span) (m : ℕ)
    (h : ∀ z ∈ s.1 ++ s.2, spanValid m z = true) :
    ∀ q ∈ payloadRequests s, P1Batch.bval q.1 ≤ m := by
  intro q hq
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
  have hle : z.1 + z.2 ≤ m := of_decide_eq_true (h z hz)
  simpa only [spanRequest, bval_bin] using (Nat.le_add_right z.1 z.2).trans hle

end P1SolCone.SolCone
