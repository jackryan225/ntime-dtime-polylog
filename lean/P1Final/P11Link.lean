import P1Final.Case1
import P1Int.P11
import P1Int.P11Count

/-!
# P1Final.P11Link: C1 from W3, W2 and the per-input count hypothesis of P11 (owner: P1-lean-integ)

`P1Int.P11.lemmaP_of_portTwo_of_setup` turns the P11 target shape (`SetupHyp` at a dyadic `s`, from the port) into
`LemmaPOfPort PortTwo`; with W3 and W2 this is the statement of `C1Challenge.c1`.
-/

namespace P1Final

open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- **C1 from the wave-2 target shape, W3 and W2.** -/
theorem c1_of_setup_parts
    (p11 : PortTwo → ∃ j : ℕ, P1Int.P11.SetupHyp ((2 : ℝ) ^ (-(j : ℤ))))
    (w3 : P1Int.PortWrapper) (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_open_parts (P1Int.P11.lemmaP_of_portTwo_of_setup p11) w3 w2

/-- **C1 from the adopted count (D8): `CountHyp` at a dyadic `s` from the port, W3 and W2.** -/
theorem c1_of_count_parts
    (p11 : PortTwo → ∃ j : ℕ, P1Int.P11.CountHyp ((2 : ℝ) ^ (-(j : ℤ))))
    (w3 : P1Int.PortWrapper) (w2 : P1Int.ParityHierarchy) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_open_parts (P1Int.P11.lemmaP_of_portTwo_of_countHyp p11) w3 w2

end P1Final
