import P1Batch.Statement
import P1Batch.Sort
import OAI.Computability.IntegerMultiplication.Bits.Small

namespace P1ProgDir.SolBatchCore

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits

variable {X : Type*} {H Y : Type*} [Codec H] [Codec Y]

/-- Assemble a fixed batch call with independently computed requests and state.
The caller verifies the whole request interval before supplying it to the call. -/
theorem batchWith (w : X → List Bool) (qs : X → List P1Batch.Req) (state : X → H)
    (fits : ∀ x q, q ∈ qs x → P1Batch.bval q.1 + P1Batch.bval q.2 ≤ (w x).length) :
    ∃ c : ℕ, Task
      (fun x => (w x).length + (size (qs x) + P1Batch.total (qs x) + 1) ^ c)
      (fun x => send ((w x, qs x), state x))
      (fun x => send ((qs x).map (P1Batch.fetch (w x)), state x)) := by
  obtain ⟨c, hc⟩ := P1Batch.batch_lookup
  let pack (x : X) : P1Batch.BatchIn :=
    ⟨(w x, qs x), fun q hq => (Nat.le_add_right _ _).trans (fits x q hq)⟩
  exact ⟨c, (hc.on pack).left (fun x => send (state x))⟩

def c1Requests (p : Word × Word) : List P1Batch.Req :=
  if more p then [(false :: p.2, [false, true])] else []

theorem easy_c1Requests : Easy c1Requests := by
  have hc : Easy (fun p : Word × Word => [(false :: p.2, [false, true])] : Word × Word → List P1Batch.Req) := by
    have hoff : Easy (fun p : Word × Word => false :: p.2) :=
      ((Easy.const false).pair Easy.snd).compose Easy.cons
    exact ((hoff.pair (Easy.const ([false, true] : Word))).pair
      (Easy.const ([] : List P1Batch.Req))).compose Easy.cons
  have ht : Easy (fun p : Word × Word => (more p, p)) :=
    (easy_more Easy.identity).pair Easy.identity
  have h := ht.compose (Easy.ifst (Easy.const ([] : List P1Batch.Req)) hc)
  unfold c1Requests
  simpa only [Bool.cond_eq_ite] using h

theorem easy_firstWord : Easy (fun ws : List Word => ws.headD []) := by
  exact Iter.leader ([] : Word)

def atWord (n : ℕ) (l : List Word) : Word := Iter.pick [] (l, tally n)

theorem easy_atWord (n : ℕ) : Easy (atWord n) :=
  (Easy.identity.pair (Easy.const (tally n))).compose (Iter.facile [])

def c1Reply (ws : List Word) : Bool := more ([true, true], ws.headD [])

theorem easy_c1Reply : Easy c1Reply :=
  easy_more ((Easy.const ([true, true] : Word)).pair easy_firstWord)

theorem c1Requests_fits (w : List Bool) (p : Word × Word)
    (h : 2 * value p.1 ≤ w.length) :
    ∀ q ∈ c1Requests p, P1Batch.bval q.1 + P1Batch.bval q.2 ≤ w.length := by
  intro q hq
  unfold c1Requests at hq
  split_ifs at hq with hp
  · simp only [List.mem_singleton] at hq
    subst q
    have hp' := (more_lt _ _).mp hp
    simp only [P1Batch.bval_eq_value, value_cons, d0, d1, zero_add, value_nil]
    omega
  · simp only [List.not_mem_nil] at hq

end P1ProgDir.SolBatchCore
