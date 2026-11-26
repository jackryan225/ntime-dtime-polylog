import P1SolCone.CheckedTables
import P1SolCone.BudgetLayout

namespace P1SolCone.SolCone

variable {F : Type}

abbrev CheckedTableState (F : Type) := Option (List KeyCode × List (P1P5.Level F))

/-- A checked backwards phase works only on the keys needed by its successor. -/
def advanceChecked (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) (s : CheckedTableState F) (ℓ : ℕ) :
    CheckedTableState F :=
  s.bind fun (keys, levels) =>
    if keys.all (allow ℓ) then
      let (old, data) := assembleLevel (pre ℓ) (halves ℓ) (kernel ℓ) keys
      some (old, data :: levels)
    else none

theorem assembleChecked_eq_fold (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) (levels : List ℕ) (keys : List KeyCode) :
    assembleCheckedChain allow pre halves kernel levels keys =
      levels.reverse.foldl (advanceChecked allow pre halves kernel) (some (keys, [])) := by
  induction levels with
  | nil => rfl
  | cons l ls ih =>
    rw [List.reverse_cons, List.foldl_append, ← ih]
    rfl

/-- Number of distinct physical positions represented by an ordered key list. -/
def positionCount (keys : List KeyCode) : ℕ := (keys.map Prod.fst).dedup.length

theorem checkedFrontier_le (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (halves : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) (cap : ℕ)
    (hcap : ∀ l q, allow l q = true → (pre l q.1).length ≤ cap)
    (levels : List ℕ) (final old : List KeyCode) (tabs : List (P1P5.Level F))
    (h : assembleCheckedChain allow pre halves kernel levels final = some (old,tabs)) :
    positionCount old ≤ positionCount final * cap ^ levels.length := by
  induction levels generalizing old tabs with
  | nil =>
    simp only [assembleCheckedChain, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_nil, pow_zero, Nat.mul_one]
  | cons l ls ih =>
    cases ht : assembleCheckedChain allow pre halves kernel ls final with
    | none =>
      rw [assembleCheckedChain, ht] at h
      contradiction
    | some pair =>
      obtain ⟨keys, levels⟩ := pair
      have hb := ih keys levels ht
      rw [assembleCheckedChain, ht] at h
      change (if keys.all (allow l) then
        some ((assembleLevel (pre l) (halves l) (kernel l) keys).1,
          (assembleLevel (pre l) (halves l) (kernel l) keys).2 :: levels) else none) = _ at h
      split at h
      next ok =>
        have he := congrArg Prod.fst (Option.some.inj h)
        change (assembleLevel (pre l) (halves l) (kernel l) keys).1 = old at he
        rw [← he]
        have hz := needKeys_frontier_le (pre l) (halves l) keys cap
          (fun q hq => hcap _ _ (List.all_eq_true.mp ok _ hq))
        change _ ≤ positionCount keys * cap at hz
        exact hz.trans (by
          rw [List.length_cons, pow_succ, ← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ hb)
      next => contradiction

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.checkedFrontier_le
