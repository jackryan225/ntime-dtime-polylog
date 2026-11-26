import P1SolCone.ConeStartTask
import P1SolCone.ConeStateSize
import P1SolCone.CheckedBudget

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

theorem getD_take_cone {A : Type} (s : List A) (v : A) (n i : ℕ) (h : i < n) :
    (s.take n).getD i v = s.getD i v := by
  induction n generalizing s i with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => rfl
    | cons z s =>
      cases i with
      | zero => rfl
      | succ i => exact ih s i (Nat.lt_of_succ_lt_succ h)

theorem stepEval_assemble_take {F : Type} [CommRing F]
    (pre : PositionCode → List PositionCode) (half : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F) (next : List KeyCode) (s : List F) :
    let entry := assembleLevel pre half kernel next
    P1P5.stepEval entry.2 (s.take (entry.1.length+1)) = P1P5.stepEval entry.2 s := by
  intro e
  unfold P1P5.stepEval
  apply List.map_congr_left
  intro row hrow
  apply congrArg List.sum
  apply List.map_congr_left
  intro item hitem
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  apply getD_take_cone
  change row ∈ (next.map fun key => (placedCodes half (pre key.1)).map
    (fun ps => (kernel key ps, ps.map (needKeys pre half next).idxOf))) at hrow
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp hrow
  obtain ⟨ps,_,rfl⟩ := List.mem_map.mp hitem
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hi
  exact Nat.lt_succ_of_le List.idxOf_le_length

/-- The first level needs only the prefix of the factor reply covered by its pointers.
The extra element also covers the final lookup when the schedule is empty. -/
theorem checkedLevels_take {F : Type} [CommRing F]
    (allow : ℕ → KeyCode → Bool) (pre : ℕ → PositionCode → List PositionCode)
    (half : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → F)
    (ls : List ℕ) (final old : List KeyCode) (levels : List (P1P5.Level F))
    (h : assembleCheckedChain allow pre half kernel ls final = some (old,levels)) (s : List F) :
    (P1P5.runLevels levels (s.take (old.length+1))).getD 0 0 =
      (P1P5.runLevels levels s).getD 0 0 := by
  cases ls with
  | nil =>
    simp only [assembleCheckedChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact getD_take_cone _ _ _ _ (Nat.succ_pos _)
  | cons l ls =>
    cases he : assembleCheckedChain allow pre half kernel ls final with
    | none => rw [assembleCheckedChain, he] at h; contradiction
    | some r =>
      obtain ⟨next,tabs⟩ := r
      rw [assembleCheckedChain, he] at h
      let e := assembleLevel (pre l) (half l) (kernel l) next
      change (if next.all (allow l) then some (e.1,e.2 :: tabs) else none) = _ at h
      split at h
      next yes =>
        have eq := Prod.mk.inj (Option.some.inj h)
        obtain ⟨rfl,rfl⟩ := eq
        rw [P1P5.runLevels,P1P5.runLevels,stepEval_assemble_take]
      next => contradiction

theorem factorsPrefix_easy {F : Type} [Fintype F] :
    Easy (fun p : Tally × List (Label F) => p.2.take p.1.length) :=
  (easy_cut Easy.identity).fstCompose

theorem factorsPrefix_size {F : Type} [Fintype F] (s : List (Label F)) (n : ℕ) :
    size (s.take n) ≤ n * (2 * Fintype.card F + 2) + 1 := by
  apply (sizeList_bound _ (2 * Fintype.card F + 1) (fun v _ => labelSize_bound v)).trans
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by simp : (s.take n).length ≤ n)) 1

end P1SolCone.SolCone
