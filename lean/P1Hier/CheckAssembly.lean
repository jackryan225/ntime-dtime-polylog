import P1Hier.CheckParts

/-! # P1Hier.CheckAssembly: `check_task` from the four phase tasks (assembly only) -/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

def b34 (i : CIn) : ℕ := ((send i).count + (send i).count) + ((send i).count + checkBudget i)
def b234 (i : CIn) : ℕ := ((send i).count + tabBudget i) + ((send i).count + b34 i)
def b1234 (i : CIn) : ℕ := ((send i).count + (send i).count) + ((send i).count + b234 i)

theorem phase34 : Task (fun x : {i : CIn // lenB i = true ∧ tabB i = true} => b34 x.val)
    (fun x => send x.val) (fun x => send (chainB x.val && colsB x.val)) := by
  have h3 : Task (fun x : {i : CIn // lenB i = true ∧ tabB i = true} => (send x.val).count)
      (fun x => send x.val) (fun x => send (chainB x.val)) := chain_task.on Subtype.val
  have h4 : Task (fun x : {x : {i : CIn // lenB i = true ∧ tabB i = true} // chainB x.val = true} =>
      checkBudget x.val.val) (fun x => send x.val.val) (fun x => send (colsB x.val.val)) :=
    cols_task.on Subtype.val
  exact seqAnd (X := {i : CIn // lenB i = true ∧ tabB i = true}) (p := fun x => send x.val)
    (a₁ := fun x => (send x.val).count) (a₂ := fun x => checkBudget x.val)
    (b₁ := fun x => chainB x.val) (b₂ := fun x => colsB x.val) h3 h4

theorem phase234 : Task (fun x : {i : CIn // lenB i = true} => b234 x.val)
    (fun x => send x.val) (fun x => send (tabB x.val && (chainB x.val && colsB x.val))) := by
  have h34 : Task (fun x : {x : {i : CIn // lenB i = true} // tabB x.val = true} => b34 x.val.val)
      (fun x => send x.val.val) (fun x => send (chainB x.val.val && colsB x.val.val)) :=
    Task.on (X := {i : CIn // lenB i = true ∧ tabB i = true})
      (Y := {x : {i : CIn // lenB i = true} // tabB x.val = true})
      (b := fun x => b34 x.val) (p := fun x => send x.val)
      (q := fun x => send (chainB x.val && colsB x.val)) phase34
      (fun x => ⟨x.val.val, x.val.property, x.property⟩)
  exact seqAnd (X := {i : CIn // lenB i = true}) (p := fun x => send x.val)
    (a₁ := fun x => tabBudget x.val) (a₂ := fun x => b34 x.val)
    (b₁ := fun x => tabB x.val) (b₂ := fun x => chainB x.val && colsB x.val) tab_task h34

theorem phase1234 : Task b1234 send (fun i => send (lenB i && (tabB i && (chainB i && colsB i)))) :=
  seqAnd (X := CIn) (p := send) (a₁ := fun i => (send i).count) (a₂ := b234)
    (b₁ := lenB) (b₂ := fun i => tabB i && (chainB i && colsB i)) len_task phase234

open Classical in
theorem check_task_of_phases : Task checkBudget send
    (fun i => send (decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2))) := by
  refine (phase1234.bound 100 (b' := checkBudget) (fun i => ?_)).conform (fun _ => rfl) (fun _ => rfl)
    (fun i => by rw [check_bool])
  have hs : (send i).count ≤ _ := size_cin i
  have hT : (size i.1 + 1) ^ 2 * (i.2.2.1 + 1) ≤ (size i.1 + 1) ^ 2 * (i.2.1.length + i.2.2.1 + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [b1234, b234, b34, tabBudget, checkBudget] at hs ⊢
  generalize (size i.1 + 1) ^ 2 * (i.2.1.length + i.2.2.1 + 1) = X at *
  generalize (size i.1 + 1) ^ 2 * (i.2.2.1 + 1) = Y at *
  omega

open Classical in
/-- **W1** (Task form). One fixed program `P`, one constant `C`: for every machine `M`, input `y`,
time `T` and transcript candidate `τ`, `P` maps the encoded tuple to the bit
`τ = transcript M y T ∧ HaltsWithin M y true T`, at cost at most
`C ((size (code M) + 1)² (|y| + T + 1) + size τ + 1)`, on top of any parked data. -/
theorem universal_checker : ∃ (P : Cmd) (C : ℕ), ∀ (M : C1Challenge.Machine) (y : List Bool)
    (T : ℕ) (τ : List Entry) (env : Env),
    Fits.value env P 0 (send (code M, y, T, τ))
      (send (decide (τ = transcript M y T ∧ C1Challenge.HaltsWithin M y true T)))
      (C * ((size (code M) + 1) ^ 2 * (y.length + T + 1) + size τ + 1)) := by
  obtain ⟨P, C, h⟩ := check_task_of_phases
  refine ⟨P, C, fun M y T τ env => ?_⟩
  have := h (code M, y, T, τ) env
  simp only [checkBudget] at this
  have e : decide (Check (code M) y T τ) =
      decide (τ = transcript M y T ∧ C1Challenge.HaltsWithin M y true T) := by
    simp only [check_iff]
  rw [e] at this
  exact this

end P1Hier
