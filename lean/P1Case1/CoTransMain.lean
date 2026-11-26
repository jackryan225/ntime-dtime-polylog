import P1Case1.CoTransBridge
import OAI.Computability.MultitapeWeakETH.ProgramDecision

/-!
# P1, Case 1, task C1: from a register program to `NTIMELinLog` (lane case1b)

`ntime_of_prog`: if a fixed OpenAI register program `p : Prog Bool` (registers are stacks; register `0`
starts with the verifier input `withGuess w x`, all other registers empty) runs on every input with a
guess of the right length in cost `≤ K (|withGuess w x| + 1)` and leaves a verdict on top of register
`0`, then the language described by the verdicts is in `NTIMELinLog`.

Machine: OpenAI's `compile_program` (`MultitapeWeakETH/ProgramDecision.lean`, a run of cost `n` gives
`MultiTapeHaltsIn M bits answer (2n+1)`), then `fromOAI` (`CoTransBridge.lean`).
-/

namespace P1Case1.CoTransV

open C1Challenge OAI.Computability.IntegerMultiplication

/-- The initial registers of a program run on the input `bits`. -/
def initReg (bits : List Bool) : Reg Bool := fun i => if i = 0 then bits else []

/-- **Assembly.** A register program with linear cost and verdict on register `0` decides an
`NTIMELinLog` language. -/
theorem ntime_of_prog (L : List Bool → Bool) (p : Prog Bool)
    (verdict : List Bool → List Bool → Bool) (K : ℕ)
    (hrun : ∀ x w : List Bool, w.length = guessLen x.length →
      ∃ n r, Prog.Run [] p (initReg (withGuess w x)) n r ∧
        n ≤ K * ((withGuess w x).length + 1) ∧ (r 0).head? = some (verdict w x))
    (hspec : ∀ x : List Bool,
      L x = true ↔ ∃ w : List Bool, w.length = guessLen x.length ∧ verdict w x = true) :
    NTIMELinLog L := by
  obtain ⟨M, hM⟩ := OAI.Computability.MultitapeWeakETH.DecisionTapes.compile_program p id
    Function.injective_id (fun o => o.getD false)
  -- every guess of the right length: the compiled machine halts with the verdict
  have halts : ∀ x w : List Bool, w.length = guessLen x.length →
      HaltsWithin (fromOAI M) (withGuess w x) (verdict w x)
        ((2 * K + 1) * ((withGuess w x).length + 1)) := by
    intro x w hw
    obtain ⟨n, r, hr, hn, hv⟩ := hrun x w hw
    have hr' : Prog.Run [] p
        (fun i => if i = 0 then (withGuess w x).map id else []) n r := by
      rw [List.map_id]; exact hr
    have h := hM (withGuess w x) n r hr'
    rw [hv] at h
    have h2 := (haltsWithin_fromOAI M).mpr h
    exact haltsWithin_mono h2 (by nlinarith)
  refine ⟨fromOAI M, 2 * K + 1, fun x => ⟨fun w hw => ⟨_, halts x w hw⟩, ?_⟩⟩
  rw [hspec x]
  constructor
  · rintro ⟨w, hw, hv⟩
    refine ⟨w, hw, ?_⟩
    have := halts x w hw
    rwa [hv] at this
  · rintro ⟨w, hw, hh⟩
    exact ⟨w, hw, (haltsWithin_unique (halts x w hw) hh)⟩

end P1Case1.CoTransV
