import OAI.Computability.IntegerMultiplication.Code.Slice

/-!
# P1Batch.Defs: the definitions of the batch interface (moved out of `P1Batch.Statement`, unchanged)

Owner: P1-lean-W2-batch. Text identical to the definitions of `Statement.lean` as compiled in job batch-1.
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Value of a binary word, least significant bit first: `bval [b₀, b₁, …] = b₀ + 2 b₁ + 4 b₂ + …`. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bval l

/-- A request: (address, length), both binary words (least significant bit first). -/
abbrev Req := List Bool × List Bool

/-- The field fetched by request `q` from the data `w`: the bits `w[a, a + ℓ)` (cut at the end of `w`). -/
def fetch (w : List Bool) (q : Req) : List Bool := (w.drop (bval q.1)).take (bval q.2)

/-- Total length `Σ ℓ_i` of the requested fields. -/
def total (qs : List Req) : ℕ := (qs.map fun q => bval q.2).sum

/-- Inputs of one batch: the data `w` (length `m`) and the requests, every address at most `m`. -/
abbrev BatchIn : Type := {i : List Bool × List Req // ∀ q ∈ i.2, bval q.1 ≤ i.1.length}

end P1Batch
