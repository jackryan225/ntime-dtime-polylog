import P1NTime.Preparation
import P1NTime.Simulation
import P1NTime.Length

namespace P1NTime.AstraNTime

open C1Challenge Composite

def AcceptingGuess (V : Machine) (c : ℕ) (x w : List Bool) : Prop :=
  w.length = guessLen x.length ∧
    HaltsWithin V (withGuess w x) true (c * ((withGuess w x).length + 1))

theorem stopped_outcome (D V : Machine) (K c : ℕ) (x w : List Bool) (src : Turing.Tape (Sym D V))
    (checkRun : HaltsWithin D (withGuess w x) (decide (w.length = guessLen x.length))
      (K * ((withGuess w x).length + 1)))
    (verifier : w.length = guessLen x.length →
      ∃ b, HaltsWithin V (withGuess w x) b (c * ((withGuess w x).length + 1))) :
    Outcome (machine D V) (stopped D V src (withGuess w x))
      ((c + K) * ((withGuess w x).length + 1) + 1) (AcceptingGuess V c x w) := by
  let z := withGuess w x
  have pass (test : decide (w.length = guessLen x.length) = true) (d : Tapes D) :
      Outcome (machine D V) (inVerify D V src d (V.init z)) (c * (z.length + 1))
        (HaltsWithin V z true (c * (z.length + 1))) := by
    obtain ⟨b, hv⟩ := verifier (decide_eq_true_iff.mp test)
    apply (verify_outcome D V src d hv).congr
    constructor
    · intro hb
      exact hb ▸ hv
    · intro ht
      exact halts_unique V hv ht
  have h := check_outcome D V src (V.init z).tapes checkRun pass
  refine (h.mono ?_).congr (and_congr decide_eq_true_iff Iff.rfl)
  change c * (z.length + 1) + 1 + K * (z.length + 1) ≤ (c + K) * (z.length + 1) + 1
  rw [Nat.add_mul]
  omega

end P1NTime.AstraNTime

open C1Challenge P1NTime.AstraNTime P1NTime.AstraNTime.Composite

theorem P1NTime.ntime_of_ntimeLinLog {L : List Bool → Bool} (h : C1Challenge.NTIMELinLog L) :
    C1Challenge.NTIMEIn L (fun n => (n : ℝ)) := by
  obtain ⟨V, c, hV⟩ := h
  obtain ⟨D, K, hD⟩ := lengthMachine
  apply ntime_of_outcomes (machine D V) (3 * (c + K) + 4)
  intro x
  let T := 3 * (c + K) * (x.length + 1) + 1
  have done (w : List Bool) (hw : w.length ≤ x.length) (src : Turing.Tape (Sym D V)) :
      Outcome (machine D V) (stopped D V src (withGuess w x)) T (AcceptingGuess V c x w) := by
    apply (stopped_outcome D V K c x w src (hD w x) ((hV x).1 w)).mono
    have sizeBound : (withGuess w x).length + 1 ≤ 3 * (x.length + 1) := by
      simp only [withGuess, List.length_append, length_pre, List.length_cons]
      omega
    have bound := Nat.mul_le_mul_left (c + K) sizeBound
    rw [show (c + K) * (3 * (x.length + 1)) = 3 * (c + K) * (x.length + 1) by ring] at bound
    exact Nat.add_le_add_right bound 1
  have hN := prep_outcome D V x T (AcceptingGuess V c x) done
  have clock : T + 4 * x.length + 3 = (3 * (c + K) + 4) * (x.length + 1) := by
    dsimp only [T]
    ring
  rw [← clock]
  apply hN.congr
  constructor
  · rintro ⟨w, _, hw⟩
    exact (hV x).2.mpr ⟨w, hw⟩
  · intro hL
    obtain ⟨w, hw, hv⟩ := (hV x).2.mp hL
    exact ⟨w, by rw [hw]; exact guessLen_le _, hw, hv⟩

example {L : List Bool → Bool} (h : C1Challenge.NTIMELinLog L) : C1Challenge.NTIMEIn L (fun n => (n : ℝ)) :=
  P1NTime.ntime_of_ntimeLinLog h

#print axioms P1NTime.ntime_of_ntimeLinLog
