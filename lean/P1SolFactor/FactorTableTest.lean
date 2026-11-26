import P1SolFactor.FactorTableOutput

namespace P1SolFactor.SolFactor

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1SolFactor.SolPolyWords P1SolFactor.SolMachine
open scoped Classical

noncomputable section

def moveCheckAt (V : FiniteMultiTapeMachine) (i : Fin (Fintype.card V.K))
    (p : Tally × (Config V × List Tally)) : Bool :=
  eqT ((tapePosition V ((kIdx V.K).symm i) (p.1, p.2.1)).1,
    Iter.pick [] (p.2.2, tally i.val))

private theorem moveCheckAt_poly (V : FiniteMultiTapeMachine) (i : Fin (Fintype.card V.K)) :
    Poly (moveCheckAt V i) := by unfold moveCheckAt; fun_prop

def moveCheck (V : FiniteMultiTapeMachine) (p : Tally × (Config V × List Tally)) : Bool :=
  allBits (List.ofFn (fun i => moveCheckAt V i p))

@[fun_prop] theorem moveCheck_poly (V : FiniteMultiTapeMachine) : Poly (moveCheck V) :=
  (ofFn_poly _ _ (moveCheckAt_poly V)).compose allBits_poly

private def isStopped (V : FiniteMultiTapeMachine) (r : Label (Reply V)) : Bool := r.val.isNone

private def acceptLabel (V : FiniteMultiTapeMachine) (q : Label V.Q) : Bool := V.accept q.val

@[local fun_prop] private theorem isStopped_poly (V : FiniteMultiTapeMachine) : Poly (isStopped V) :=
  (Easy.finite _).poly

@[local fun_prop] private theorem acceptLabel_poly (V : FiniteMultiTapeMachine) : Poly (acceptLabel V) :=
  (Easy.finite _).poly

def acceptConfig (V : FiniteMultiTapeMachine) (c : Config V) : Bool :=
  andB (isStopped V (command V c), acceptLabel V c.1)

@[fun_prop] theorem acceptConfig_poly (V : FiniteMultiTapeMachine) : Poly (acceptConfig V) := by
  unfold acceptConfig
  fun_prop

section Correctness

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]

theorem moveCheck_run (d : LocalIn V B) (moves : V.K → Fin 3) :
    moveCheck V (tally B, (SolMachine.encode V (3 * B) ((absStep V)^[B] d.toAbs),
      List.ofFn (fun i => tally (moves ((kIdx V.K).symm i)).val))) = true ↔
      (evolve d).move = moves := by
  let c := (absStep V)^[B] d.toAbs
  let row := List.ofFn (fun i => tally (moves ((kIdx V.K).symm i)).val)
  have hm (i : Fin (Fintype.card V.K)) :
      moveCheckAt V i (tally B, (SolMachine.encode V (3 * B) c, row)) = true ↔
        (evolve d).move ((kIdx V.K).symm i) = moves ((kIdx V.K).symm i) := by
    unfold moveCheckAt
    rw [tapePosition_encode V B c _ (run_window V B d le_rfl _)]
    change eqT (tally _, Iter.pick [] (row, tally i.val)) = true ↔ _
    unfold row
    rw [Iter.entry, eqT_tally, decide_eq_true_eq]
    exact Fin.ext_iff.symm
  change moveCheck V (tally B, (SolMachine.encode V (3 * B) c, row)) = true ↔ _
  unfold moveCheck
  rw [allBits_true]
  constructor
  · intro h
    funext k
    have hi := (hm (kIdx V.K k)).1 (h _ (List.mem_ofFn.mpr ⟨kIdx V.K k, rfl⟩))
    simpa only [Equiv.symm_apply_apply] using hi
  · intro hh b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact (hm i).2 (congrFun hh _)

theorem acceptConfig_run (d : LocalIn V B) :
    acceptConfig V (SolMachine.encode V (3 * B) ((absStep V)^[B] d.toAbs)) = true ↔
      Accepts B (evolve d) := by
  let c := (absStep V)^[B] d.toAbs
  have hpos (k : V.K) : 0 ≤ c.pos k ∧ c.pos k < 3 * (B : ℤ) := run_window V B d le_rfl k
  have hwidth (k : V.K) : 0 ≤ c.pos k ∧ c.pos k < ((3 * B : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpos k
  have hh : c.heads = fun k => (evolve d).blocks k ((evolve d).move k) ((evolve d).off k) := by
    funext k
    have hb : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
    have hq0 := Int.ediv_nonneg (hpos k).1 hb.le
    have hq1 : c.pos k / B < 3 := (Int.ediv_lt_iff_lt_mul hb).2 (hpos k).2
    have hq := finOfInt_val 3 hq0 (by exact_mod_cast hq1)
    have hr := finOfInt_val B (Int.emod_nonneg (c.pos k) (by omega)) (Int.emod_lt_of_pos _ hb)
    change c.cells k (c.pos k) = c.cells k
      (((finOfInt 3 (c.pos k / B)).val : ℤ) * B + (finOfInt B (c.pos k % B)).val)
    rw [hq, hr]
    have he := Int.emod_add_ediv_mul (c.pos k) B
    congr 1
    linarith
  change acceptConfig V (SolMachine.encode V (3 * B) c) = true ↔ _
  unfold acceptConfig command
  rw [reads_encode V (3 * B) c hwidth]
  change (andB ((V.code c.q c.heads).map _ |>.isNone, V.accept c.q)) = true ↔ _
  unfold Accepts
  rw [← hh]
  change (andB ((V.code c.q c.heads).map _ |>.isNone, V.accept c.q)) = true ↔
    V.code c.q c.heads = none ∧ V.accept c.q = true
  cases e : V.code c.q c.heads <;> simp only [andB, Option.map_none, Option.isNone_none,
    Bool.true_and, Option.map_some, Option.isNone_some, Bool.false_and, Bool.false_eq_true,
    Option.some_ne_none, false_and, true_and]

end Correctness

abbrev TableQuery := Tally × (Bool × (List Tally × List Bool))

def tableCore (V : FiniteMultiTapeMachine) (p : TableQuery) : Bool :=
  let B := p.1
  let word := p.2.2.2
  let initial := inputConfig V (B, word)
  let final := run V (B, initial)
  andB (exactEq (word, configTuple V (B, (initial, final))),
    andB (moveCheck V (B, (final, p.2.2.1)),
      bif p.2.1 then acceptConfig V final else true))

attribute [local fun_prop] SolMachine.run_poly

@[fun_prop] theorem tableCore_poly (V : FiniteMultiTapeMachine) : Poly (tableCore V) := by
  unfold tableCore
  fun_prop

theorem tableCore_correct (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (last : Bool)
    (moves : V.K → Fin 3) (word : List Bool) :
    tableCore V (tally B, (last, (List.ofFn (fun i => tally (moves ((kIdx V.K).symm i)).val), word))) = true ↔
      ∃ d : LocalIn V B, word = List.ofFn (tupleWord V B (extData V B d (evolve d))) ∧
        (evolve d).move = moves ∧ (last = true → Accepts B (evolve d)) := by
  let d := decodedIn V B word
  have he : run V (tally B, inputConfig V (tally B, word)) =
      SolMachine.encode V (3 * B) ((absStep V)^[B] d.toAbs) := by
    rw [inputConfig_decode]
    apply run_encode
    intro t ht k
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using run_window V B d ht.le k
  have ht (last : Bool) :
      (bif last then acceptConfig V (SolMachine.encode V (3 * B) ((absStep V)^[B] d.toAbs)) else true) = true ↔
        (last = true → Accepts B (evolve d)) := by
    cases last <;> simp [acceptConfig_run]
  dsimp only [tableCore, andB]
  rw [Bool.and_eq_true, Bool.and_eq_true, he, inputConfig_decode]
  change (exactEq (word, configTuple V (tally B, (SolMachine.encode V (3 * B) d.toAbs, _))) = true) ∧
    _ ∧ _ ↔ _
  rw [configTuple_run, exactEq_true, moveCheck_run, ht]
  refine ⟨fun h => ⟨d, h⟩, ?_⟩
  rintro ⟨d', hw, hm, ha⟩
  have hd : d = d' := by
    change decodedIn V B word = d'
    rw [hw, decodedIn_code]
  rw [hd]
  exact ⟨hw, hm, ha⟩

def tableTest (V : FiniteMultiTapeMachine) (p : Query) : Bool :=
  tableCore V (header 1 p, (flag (header 2 p), (dropT (tally 3, p.1), outSlot (p.2, tally 0))))

@[fun_prop] theorem tableTest_poly (V : FiniteMultiTapeMachine) : Poly (tableTest V) := by
  unfold tableTest
  fun_prop

end

end P1SolFactor.SolFactor
