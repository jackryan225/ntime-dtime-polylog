import P1Batch.Defs
import P1Batch.Countdown
import P1Batch.Lookup

/-!
# P1Batch.Statement: countdown and batched look-up (paper lem:countdown, lem:batch) as OpenAI programs

Owner: P1-lean-W2-batch. Paper: research/papers/ntime-dtime-polylog.tex, Lemma countdown (l.264) and
Lemma batch (l.273). Interface for the checker lanes (ChkDir, ChkGreedy, ChkFinal) and the dispatcher (Count).

**Model.** OpenAI's Task framework (OAI/Computability/IntegerMultiplication/Code/Task.lean). A
`Task budget query reply` is ONE fixed program `c : Prog Ltr` (OpenAI's `Prog` of TMProgram.lean, the form of
`P1Int.LemmaP` with alphabet `Ltr` and `letter = Ltr.bit`) with a constant `C` such that for every parameter `x`,
every scope `env` and EVERY content `r` of all registers, `c` turns the tree `query x` on top of register 0 into
`reply x` within `C * (budget x + 1)` steps (`Prog.Run`, OpenAI's cost) and leaves all other register contents
as they were. So tasks compose (`Task.compose`, `Task.left`, `Task.right`, `Task.foldLeft`, `Easy`, `Poly`, ...).
`batch_lookup_prog` below is the same statement unfolded to `Prog.Run`.

**Numbers** are binary words, least significant bit first (`bval`); high zeros are allowed.
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

-- Definitions `bval`, `Req`, `fetch`, `total`, `BatchIn`: `P1Batch.Defs` (text unchanged since batch-1).

/-- **Countdown** (paper lem:countdown). A binary counter `g` (any binary word `l` with `bval l = g`) is counted
down into the unary tally of `g` (OpenAI's `tally`, the ruler that `Computes.cut` uses to move along a scan) in
`O(g + |l|)` steps, i.e. `O(g + log g)` for a canonical word. -/
theorem countdown :
    Task (fun l : List Bool => bval l + l.length) send (fun l => send (tally (bval l))) :=
  countdown_proof

/-- **Batched look-up** (paper lem:batch). One fixed program takes the data `w` (length `m`) and requests
`q_1, …, q_r` (`q_i = (a_i, ℓ_i)` in binary, `a_i ≤ m`), as the tree `send (w, [q_1, …, q_r])` on top of
register 0, and returns the fields `[w[a_1, a_1+ℓ_1), …, w[a_r, a_r+ℓ_r)]` IN THE REQUEST ORDER (as the tree
`send [field_1, …, field_r]`), within `C * (m + (size qs + Σ ℓ_i + 1)^c + 1)` steps. Here `size qs` is the length
of the encoded request list: `O(r log m + Σ log ℓ_i)` for canonical words. Method: tag, sort by address (radix),
form the gaps, count each gap down (`countdown`), one scan of `w` with `Computes.cut`, return to request order. -/
theorem batch_lookup : ∃ c : ℕ,
    Task (fun i : BatchIn => i.val.1.length + (size i.val.2 + total i.val.2 + 1) ^ c)
      (fun i => send i.val) (fun i => send (i.val.2.map (fetch i.val.1))) :=
  batch_lookup_proof

/-- `batch_lookup` unfolded to OpenAI's `Prog.Run`: one program `P`, every scope, every register content `r`. -/
theorem batch_lookup_prog : ∃ (P : Prog Ltr) (c : ℕ), ∀ (w : List Bool) (qs : List Req),
    (∀ q ∈ qs, bval q.1 ≤ w.length) → ∀ (env : Scope Ltr) (r : Reg Tree),
      ∃ t ≤ c * (w.length + (size qs + total qs + 1) ^ c),
        Prog.Run env P (letters (pile 0 (send (w, qs)) r)) t
          (letters (pile 0 (send (qs.map (fetch w))) r)) :=
  batch_lookup_prog_proof

end P1Batch
