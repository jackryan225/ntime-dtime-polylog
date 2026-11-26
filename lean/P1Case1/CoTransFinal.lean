import P1Case1.CoTransMain
import P1Case1.CoTransSpec
import P1Case1.CoTransProg

/-!
# P1, Case 1, task C1: `NTIMELinLog coTRANS` from a verifier program (lane case1b, copy A)

`ntime_coTRANS_of_run`: the target `NTIMELinLog coTRANS` follows from ONE run lemma for a register
program `p` that computes `verdict` (`CoTransSpec.lean`) in linear cost. The compiler
(`compile_program`), the bridge to the Challenge machine model, the time bound and the guess code are
done here (`CoTransMain.lean`, `CoTransSpec.lean`).
-/

namespace P1Case1.CoTransV

open C1Challenge OAI.Computability.IntegerMultiplication

/-- **C1, reduced to the run lemma of the verifier program.** -/
theorem ntime_coTRANS_of_run (p : Prog Bool) (K : ℕ)
    (hrun : ∀ x w : List Bool, w.length = guessLen x.length →
      ∃ n r, Prog.Run [] p (initReg (withGuess w x)) n r ∧
        n ≤ K * ((withGuess w x).length + 1) ∧ (r 0).head? = some (verdict w x)) :
    NTIMELinLog coTRANS :=
  ntime_of_prog coTRANS p verdict K hrun coTRANS_iff_verdict

/-- **Assembly in the `Runs` form of `CoTransProg.lean`**, for any language `L` and any verdict that is
sound and complete for `L`. -/
theorem ntime_of_runs (L : List Bool → Bool) (p : Prog Bool)
    (verdict' : List Bool → List Bool → Bool) (K : ℕ)
    (hrun : ∀ x w : List Bool, w.length = guessLen x.length →
      ∃ r', P1Case1.CoTrans.Runs [] p (initReg (withGuess w x)) r'
        (K * ((withGuess w x).length + 1)) ∧ (r' 0).head? = some (verdict' w x))
    (hsound : ∀ x w : List Bool, w.length = guessLen x.length → verdict' w x = true → L x = true)
    (hcomplete : ∀ x : List Bool, L x = true →
      ∃ w : List Bool, w.length = guessLen x.length ∧ verdict' w x = true) :
    NTIMELinLog L := by
  refine ntime_of_prog L p verdict' K (fun x w hw => ?_) (fun x => ⟨hcomplete x, ?_⟩)
  · obtain ⟨r', ⟨n, hn, hle⟩, hv⟩ := hrun x w hw
    exact ⟨n, r', hn, hle, hv⟩
  · rintro ⟨w, hw, hv⟩
    exact hsound x w hw hv

/-- **C1 in the `Runs` form**, with the verdict of `CoTransSpec.lean`. -/
theorem ntime_coTRANS_of_runs (p : Prog Bool) (K : ℕ)
    (hrun : ∀ x w : List Bool, w.length = guessLen x.length →
      ∃ r', P1Case1.CoTrans.Runs [] p (initReg (withGuess w x)) r'
        (K * ((withGuess w x).length + 1)) ∧ (r' 0).head? = some (verdict w x)) :
    NTIMELinLog coTRANS :=
  ntime_of_runs coTRANS p verdict K hrun
    (fun x w hw hv => (coTRANS_iff_verdict x).mpr ⟨w, hw, hv⟩)
    (fun x hx => (coTRANS_iff_verdict x).mp hx)

end P1Case1.CoTransV
