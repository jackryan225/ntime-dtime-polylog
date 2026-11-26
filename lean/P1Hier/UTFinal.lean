import P1Hier.UTArith
import P1Hier.UTParse
import P1Hier.CheckAssembly
import P1Int.Links

/-!
# P1Hier.UTFinal (copy B of lane hier): the W2 machine, closed

* `UM.accU_machine_proved`: the statement of `P1Hier.accU_machine` (Hierarchy.lean, copy A),
  from `UM.accU_machine_of3` with the decoders `UM.px2_easy`, `UM.decT2_easy` and copy A's
  W1 check task `P1Hier.check_task_of_phases`.
* `UM.universal_verifier_proved`, `UM.parity_hierarchy_proved`: the text of the old
  `P1Hier.universal_verifier` and `P1Hier.parity_hierarchy` (now `P1Hier.parity_hierarchy_of`
  with the hypothesis `AccUMachine q`), proved here from the closed machine.
* `UM.parityHierarchy_closed : P1Int.ParityHierarchy` (via `P1Int.parityHierarchy_hier`).
-/

namespace P1Hier.UM

open C1Challenge

/-- A default code, used only when the input has no code prefix. -/
def dcode : MCode := ⟨0, 0, 0, 0, 0, []⟩

open Classical in
theorem accU_machine_proved (q : ℕ) (_hq : 1 ≤ q) : ∃ (U : Machine) (b : ℕ), ∀ (x : List Bool)
    (u : Fin (gU x.length) → Bool),
    HaltsWithin U (withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
      (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length) :=
  accU_machine_of3 q dcode (px2_easy dcode) decT2_easy check_task_of_phases

open Classical in
theorem universal_verifier_proved (q : ℕ) (hq : 1 ≤ q) : ∃ (U : Machine) (a b : ℕ),
    ParDecidesFrom U (D q) (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 := by
  obtain ⟨U, b, hU⟩ := accU_machine_proved q hq
  refine ⟨U, 4, b, fun x _ => ⟨fun u => ⟨_, hU x u⟩, ?_⟩⟩
  rw [D, decide_eq_true_iff]
  have : (Finset.univ.filter fun u : Fin (4 * (x.length ^ 2 + 1)) → Bool =>
        HaltsWithin U (withGuess (List.ofFn u) x) true
          (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length)) =
      (Finset.univ.filter fun u : Fin (gU x.length) → Bool => accU q x (List.ofFn u)) := by
    apply Finset.filter_congr
    intro u _
    constructor
    · intro h
      have := halts_det U _ h (hU x u)
      exact of_decide_eq_true this.symm
    · intro h
      have := hU x u
      rwa [decide_eq_true h] at this
  rw [this]
  rfl

/-- **W2** (two-constant form), with no open input. -/
theorem parity_hierarchy_proved (q : ℕ) (hq : 1 ≤ q) : ∃ D : List Bool → Bool,
    (∃ (U : Machine) (a b : ℕ),
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
    ∀ (V : Machine) (c n₀ : ℕ), ¬ ParDecidesFrom V D (G q) (fun n => c * G q n) n₀ :=
  ⟨P1Hier.D q, universal_verifier_proved q hq, diagonal q⟩

/-- **The open Prop `P1Int.ParityHierarchy`, closed.** -/
theorem parityHierarchy_closed : P1Int.ParityHierarchy :=
  P1Int.parityHierarchy_hier.mp parity_hierarchy_proved

end P1Hier.UM
