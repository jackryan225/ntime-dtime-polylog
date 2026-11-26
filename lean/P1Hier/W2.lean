import P1Hier.UTFinal
import P1Hier.CheckAssembly

/-!
# P1Hier.W2: the parity hierarchy, linked

`Hierarchy.parity_hierarchy_of` proves W2 from the machine statement `AccUMachine q`. Lane hierB's
`UM.accU_machine_of3` proves that statement from three inputs: the code parser `h2`, the transcript
parser `h5`, and the W1 checker `h7`. Here `h7` is supplied by `check_task_of_phases` (W1, proved).
Lane hierB proved the parsers (`UM.px2_easy`, `UM.decT2_easy`, file UTParse.lean) and closed W2
in UTFinal.lean (`UM.parity_hierarchy_proved`). Here the ORIGINAL names and statements of copy A
are restored with no hypothesis and no `sorry`: `accU_machine`, `universal_verifier`,
`parity_hierarchy` (the last one through copy A's own route `parity_hierarchy_of`).
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- The machine statement from the two parsers (W1 is supplied). -/
theorem accUMachine_of_parsers (q : ℕ) (d : MCode) (h2 : Easy (UM.px2 d)) (h5 : Easy UM.decT2) :
    AccUMachine q :=
  UM.accU_machine_of3 q d h2 h5 check_task_of_phases

/-- **W2** from the two parsers. -/
theorem parity_hierarchy_of_parsers (d : MCode) (h2 : Easy (UM.px2 d)) (h5 : Easy UM.decT2)
    (q : ℕ) (_hq : 1 ≤ q) : ∃ D : List Bool → Bool,
    (∃ (U : C1Challenge.Machine) (a b : ℕ),
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
    ∀ (V : C1Challenge.Machine) (c n₀ : ℕ), ¬ ParDecidesFrom V D (G q) (fun n => c * G q n) n₀ :=
  parity_hierarchy_of q (accUMachine_of_parsers q d h2 h5)

open Classical in
/-- The machine of W2 (original statement of copy A). -/
theorem accU_machine (q : ℕ) (hq : 1 ≤ q) : ∃ (U : C1Challenge.Machine) (b : ℕ), ∀ (x : List Bool)
    (u : Fin (gU x.length) → Bool),
    C1Challenge.HaltsWithin U (C1Challenge.withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
      (b * (x.length ^ 2 + 1) + (C1Challenge.withGuess (List.ofFn u) x).length) :=
  accUMachine_of_parsers q UM.dcode (UM.px2_easy UM.dcode) UM.decT2_easy

/-- The fast verifier of `D q` (original statement of copy A). -/
theorem universal_verifier (q : ℕ) (hq : 1 ≤ q) : ∃ (U : C1Challenge.Machine) (a b : ℕ),
    ParDecidesFrom U (D q) (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 :=
  universal_verifier_of q (accU_machine q hq)

/-- **W2**, the parity hierarchy (original statement of copy A), no hypothesis. -/
theorem parity_hierarchy (q : ℕ) (hq : 1 ≤ q) : ∃ D : List Bool → Bool,
    (∃ (U : C1Challenge.Machine) (a b : ℕ),
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
    ∀ (V : C1Challenge.Machine) (c n₀ : ℕ), ¬ ParDecidesFrom V D (G q) (fun n => c * G q n) n₀ :=
  parity_hierarchy_of q (accU_machine q hq)

end P1Hier

#print axioms P1Hier.parity_hierarchy_of_parsers
#print axioms P1Hier.accU_machine
#print axioms P1Hier.universal_verifier
#print axioms P1Hier.parity_hierarchy
