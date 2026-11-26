import P1ChkFinal.ProgC13link
import P1P5.LevelsPoly
import P1P5.ConeBudget
import P1Wrap.ParamTask
import P1SolCone.ConeBatchInput
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace P1SolCone.SolCone

open Module
open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter

variable {R : Type} [CommRing R] [Fintype R]


/-- The input to the level evaluator, with its final lookup index. -/
abbrev EncodedLevels (R : Type) :=
  (List (List (List (Label R × List Tally))) × List (Label R)) × Tally

private theorem pick_tally {A : Type} (ls : List A) (i : ℕ) (fallback : A) :
    Iter.pick fallback (ls, tally i) = ls.getD i fallback := by
  simp only [Iter.pick, tally_length]
  induction i generalizing ls with
  | zero => cases ls <;> rfl
  | succ i ih =>
    cases ls with
    | nil => rfl
    | cons a as => exact ih as

/-- Given the posted Poly level evaluator, a fixed program evaluates the cone, selects the
requested half-assignment and translates the result into C13's basis coordinates. -/
theorem evalCoords_poly [Algebra (ZMod 2) R] {d : ℕ} (b : Basis (Fin d) (ZMod 2) R)
    : ∃ evaluate : EncodedLevels R → List Bool, Poly evaluate ∧
      ∀ (Ls : List (P1P5.Level R)) (st : List R) (i : ℕ),
        evaluate ((Ls.map P1P5.encLevel, st.map Label.mk), tally i) =
          P1ChkFinal.coords b ((P1P5.runLevels Ls st).getD i 0) := by
  obtain ⟨val, hval, hspec⟩ := P1P5.runLevels_poly (R := R)
  let encodeCoords (r : Label R) := P1ChkFinal.coords b r.val
  let evaluate (x : EncodedLevels R) := encodeCoords (Iter.pick (⟨0⟩ : Label R) (val x.1, x.2))
  have hcoords : Poly encodeCoords := (Easy.finite encodeCoords).poly
  have heval : Poly evaluate :=
    (hval.onleft.compose (Iter.facile (⟨0⟩ : Label R)).poly).compose hcoords
  refine ⟨evaluate, heval, fun Ls st i => ?_⟩
  simp only [evaluate, encodeCoords, hspec, pick_tally, List.getD_map]

/-- Running the Poly evaluator after a table-building task charges only local work. -/
theorem finishTables [Algebra (ZMod 2) R] {X : Type*} {d : ℕ} (b : Basis (Fin d) (ZMod 2) R)
    (q : X → Tree) (levels : X → List (P1P5.Level R)) (initial : X → List R) (index : X → ℕ)
    (scan localCost cap : X → ℕ)
    (hBuild : Task (fun x => scan x + localCost x) q (fun x =>
      send (((levels x).map P1P5.encLevel, (initial x).map Label.mk), tally (index x))))
    (hCost : Dom cap localCost)
    (hSize : Dom cap (fun x => size
      (((levels x).map P1P5.encLevel, (initial x).map Label.mk), tally (index x)))) :
    ∃ tailCost : X → ℕ, Dom cap tailCost ∧ Task (fun x => scan x + tailCost x) q
      (fun x => send (P1ChkFinal.coords b ((P1P5.runLevels (levels x) (initial x)).getD (index x) 0))) := by
  obtain ⟨evaluate, hEval, hSpec⟩ := evalCoords_poly b
  obtain ⟨cost, hcost, run⟩ := hEval.on hSize
  refine ⟨fun x => localCost x + cost x, hCost.add hcost, ?_⟩
  exact (hBuild.compose run).conform (fun x => Nat.add_assoc ..) (fun _ => rfl)
    (fun x => congrArg send (hSpec (levels x) (initial x) (index x)))

/-- Reading the binary length of an arbitrary witness can add that word to the small
state. Its polynomial processing cost is absorbed by the witness scan and the local bound. -/
theorem witnessMetadata_task {X : Type*} (q result : X → Tree) (scan m cap cost : X → ℕ)
    (hScan : ∀ x, m x + 1 ≤ scan x)
    (hCost : Dom (fun x => cap x + size (Carry.born (m x))) cost)
    (run : Task (fun x => scan x + cost x) q result) :
    ∃ tail : X → ℕ, Dom cap tail ∧ Task (fun x => scan x + tail x) q result := by
  obtain ⟨e, A, hA⟩ := hCost
  obtain ⟨C, hC⟩ := P1Wrap.W3.PT.absorb1 e (A * 2 ^ e)
  let tail (x : X) := (A * 2 ^ e) * (cap x + 1) ^ e
  refine ⟨tail, ⟨e, A * 2 ^ e, fun _ => le_rfl⟩, run.bound (C + 1) (fun x => ?_)⟩
  let bits := size (Carry.born (m x))
  have monoCost (z : ℕ) (hz : cap x + bits + 1 ≤ 2 * (z + 1)) :
      cost x ≤ (A * 2 ^ e) * (z + 1) ^ e := by
    calc
      _ ≤ A * (cap x + bits + 1) ^ e := hA x
      _ ≤ A * (2 * (z + 1)) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hz _)
      _ = _ := by rw [mul_pow, Nat.mul_assoc]
  have hbound : cost x ≤ C * scan x + tail x := by
    by_cases h : bits ≤ cap x
    · exact (monoCost (cap x) (by omega)).trans (Nat.le_add_left _ _)
    · exact ((monoCost bits (by omega)).trans ((hC (m x)).trans (Nat.mul_le_mul_left C (hScan x)))).trans
        (Nat.le_add_right _ _)
  have hbig := Nat.mul_le_mul_left C (show scan x ≤ scan x + tail x + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Convert a scan plus a polynomial in the local bound into the D14 form. -/
theorem d14_task {X : Type*} (q result : X → Tree) (scan exponent querySize localCost : X → ℕ)
    (hQuery : ∀ x, 1 ≤ querySize x)
    (hLocal : Dom (fun x => 2 ^ exponent x * querySize x) localCost)
    (hTask : Task (fun x => scan x + localCost x) q result) :
    ∃ c : ℕ, 1 ≤ c ∧ Task (fun x => c * scan x + 2 ^ (c * exponent x) * querySize x ^ c) q result := by
  obtain ⟨e, A, hA⟩ := hLocal
  let c := e + 1
  refine ⟨c, by dsimp only [c]; omega, hTask.bound (A * 2 ^ e + 1) (fun x => ?_)⟩
  have hp : 1 ≤ 2 ^ exponent x * querySize x :=
    Nat.mul_pos (Nat.two_pow_pos _) (hQuery x)
  have hf : (2 ^ exponent x * querySize x + 1) ^ e ≤
      2 ^ e * (2 ^ (c * exponent x) * querySize x ^ c) := by
    calc
      _ ≤ (2 * (2 ^ exponent x * querySize x)) ^ e := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ e * (2 ^ (e * exponent x) * querySize x ^ e) := by
        rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (exponent x) e]
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_right _ (Nat.le_succ e))) (Nat.pow_le_pow_right (hQuery x) (Nat.le_succ e))
  have h1 := (hA x).trans (Nat.mul_le_mul_left A hf)
  rw [← Nat.mul_assoc] at h1
  have h2 : scan x ≤ c * scan x := Nat.le_mul_of_pos_left _ (by dsimp only [c]; omega)
  have h3 := Nat.mul_le_mul_left (A * 2 ^ e) h2
  rw [Nat.add_mul]
  simp only [Nat.mul_one, Nat.mul_add] at *
  omega

/-- The layout's lane axis has polynomial length in the binary clock length. -/
theorem laneCount_le {t g : ℕ} (hg : g ≤ P1Wrap.Params.h t) :
    2 ^ g ≤ (P1Wrap.Params.lam t + 1) ^ 10 := by
  have hp : 2 ^ P1Wrap.Params.p t ≤ P1Wrap.Params.lam t + 1 := by
    unfold P1Wrap.Params.p
    by_cases hz : P1Wrap.Params.lam t = 0
    · simp only [hz, Nat.log_zero_right, pow_zero, Nat.zero_add, le_refl]
    · exact (Nat.pow_log_le_self 2 hz).trans (Nat.le_succ _)
  have h := hg.trans (show P1Wrap.Params.h t ≤ 10 * P1Wrap.Params.p t from by
    unfold P1Wrap.Params.h
    omega)
  calc
    _ ≤ 2 ^ (P1Wrap.Params.p t * 10) := Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using h)
    _ = (2 ^ P1Wrap.Params.p t) ^ 10 := pow_mul ..
    _ ≤ _ := Nat.pow_le_pow_left hp _

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.evalCoords_poly
#print axioms P1SolCone.SolCone.finishTables
#print axioms P1SolCone.SolCone.d14_task
#print axioms P1SolCone.SolCone.laneCount_le
#print axioms P1SolCone.SolCone.prepareConeQuery_easy

#print axioms P1SolCone.SolCone.witnessMetadata_task
