import P1Case1.CoTransProg

/-!
# P1, Case 1, task C1: the loops of the coTRANS verifier and their closed forms (part 1 of 2)

Register conventions (all registers are stacks of bits; "unary `v`" means `List.replicate v true`):
`3` fuel, `4` the number `N` (unary), `7` scratch, `8` flags (any failure pushes `true`).

R-build split this file out of `CoTransLoops.lean` on 2026-11-25 (no change of text; original:
`research/p1/lean/notes/CoTransLoops.lean.orig-20261125`). Part 2 (rounds, copies, `run_rest`): `CoTransLoops.lean`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace P1Case1.CoTrans

open OAI.Computability.IntegerMultiplication

/-! ## Pop loop: for every element of `S`, push `true` on `P` and pop `X` (flag if empty) -/

def popLoop (S X P : ℕ) : Pg := forEach S fun _ => .join (.push P true) (popOrFlag X)

def popAct (X P : ℕ) (_ : Bool) (r : Rg) : Rg :=
  popOrFlagF X (Function.update r P (true :: r P))

def popLoopF (S X P m : ℕ) (r : Rg) : Rg := fun j =>
  if j = S then [] else
  if j = X then (r X).drop m else
  if j = 8 then List.replicate (m - (r X).length) true ++ r 8 else
  if j = P then List.replicate m true ++ r P else r j

section popLoop

variable {S X P : ℕ} (hSX : S ≠ X) (hS8 : S ≠ 8) (hX8 : X ≠ 8) (hSP : S ≠ P) (hXP : X ≠ P)
  (hP8 : P ≠ 8)
include hSX hS8 hX8 hSP hXP hP8

theorem popAct_src (a : Bool) (r : Rg) : popAct X P a r S = r S := by
  unfold popAct popOrFlagF flagF
  rcases h : Function.update r P (true :: r P) X with _ | ⟨b, t⟩ <;>
    simp [Function.update_apply, hS8, hSX, hSP]

theorem popLoop_iterate (l : List Bool) : ∀ r : Rg, r S = l →
    (eachStep S (popAct X P))^[l.length] r = popLoopF S X P l.length r := by
  induction l with
  | nil =>
    intro r hr
    funext j
    simp only [List.length_nil, Function.iterate_zero, id, popLoopF, List.drop_zero, Nat.zero_sub,
      List.replicate_zero, List.nil_append]
    split_ifs with h1 h2 h3 h4 <;> subst_vars <;> simp_all
  | cons a l ih =>
    intro r hr
    have h1 : popAct X P a (Function.update r S l) S = l := by
      rw [popAct_src hSX hS8 hX8 hSP hXP hP8]; simp
    rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons hr, ih _ h1]
    funext j
    unfold popLoopF popAct popOrFlagF flagF
    cases hX : r X with
    | nil =>
      have e : (Function.update (Function.update r S l) P (true :: Function.update r S l P)) X = [] := by
        simp [Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
      simp only [e]
      by_cases j1 : j = S
      · simp [j1, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
      · by_cases j2 : j = X
        · subst j2; simp [j1, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
        · by_cases j3 : j = 8
          · subst j3
            simp [j1, j2, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
          · by_cases j4 : j = P
            · subst j4
              simp [j1, j2, j3, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
            · simp [j1, j2, j3, j4, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
    | cons b t =>
      have e : (Function.update (Function.update r S l) P (true :: Function.update r S l P)) X =
          b :: t := by
        simp [Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
      simp only [e]
      by_cases j1 : j = S
      · simp [j1, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
      · by_cases j2 : j = X
        · subst j2; simp [j1, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
        · by_cases j3 : j = 8
          · subst j3
            simp [j1, j2, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
          · by_cases j4 : j = P
            · subst j4
              simp [j1, j2, j3, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]
            · simp [j1, j2, j3, j4, Function.update_apply, hSX, hS8, hX8, hSP, hXP, hP8, hSX.symm, hS8.symm, hX8.symm, hSP.symm, hXP.symm, hP8.symm, hX, List.replicate_succ', List.append_assoc]

theorem runs_popLoop (Γ : Sc) (r : Rg) :
    Runs Γ (popLoop S X P) r (popLoopF S X P (r S).length r) ((r S).length * 12 + 3) := by
  have h := runs_forEach S _ (popAct X P) 5
    (fun Γ a r => ((Runs.push P true).join (runs_popOrFlag X _)).mono (by omega))
    (fun a r => popAct_src hSX hS8 hX8 hSP hXP hP8 a r) Γ r
  rw [popLoop_iterate hSX hS8 hX8 hSP hXP hP8 _ r rfl] at h
  exact h

end popLoop

theorem flatMap_nil' (l : List Bool) : l.flatMap (fun _ => ([] : List Bool)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem flatMap_true (l : List Bool) : l.flatMap (fun _ => [true]) = List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

/-! ## Skip `|N|` symbols of `X` (register 4 = `N` is restored through register 7) -/

def skipN (X : ℕ) : Pg := .join (popLoop 4 X 7) (xfer 7 [] [4])

def skipNF (X : ℕ) (r : Rg) : Rg := fun j =>
  if j = X then (r X).drop (r 4).length else
  if j = 8 then List.replicate ((r 4).length - (r X).length) true ++ r 8 else
  if j = 4 then List.replicate ((r 4).length + (r 7).length) true else
  if j = 7 then [] else r j

section skipN

variable {X : ℕ} (hX4 : X ≠ 4) (hX7 : X ≠ 7) (hX8 : X ≠ 8)
include hX4 hX7 hX8

theorem skipN_state (r : Rg) :
    xferF 7 [] [4] (popLoopF 4 X 7 (r 4).length r) = skipNF X r := by
  funext j
  by_cases j7 : j = 7
  · subst j7; simp [xferF, skipNF, hX7.symm]
  · by_cases j4 : j = 4
    · subst j4
      simp only [xferF, popLoopF, skipNF, hX4.symm, hX7.symm, if_false, if_true, List.count_singleton_self,
        List.count_nil, List.replicate_zero, List.append_nil, List.replicate_one]
      simp only [show (4:ℕ) ≠ 7 by decide, show (7:ℕ) ≠ 8 by decide, show (7:ℕ) ≠ 4 by decide,
        if_false, if_true, List.reverse_append, List.flatMap_append, flatMap_true, List.length_reverse,
        List.length_replicate, List.append_nil, List.reverse_replicate]
      rw [← List.replicate_add, Nat.add_comm]
      simp
    · have c1 : List.count j [4] = 0 := List.count_eq_zero_of_not_mem (by simp [j4])
      simp only [xferF, j7, if_false, c1, List.count_nil, List.replicate_zero, List.nil_append,
        flatMap_nil', popLoopF, skipNF, j4]

theorem runs_skipN (Γ : Sc) (r : Rg) :
    Runs Γ (skipN X) r (skipNF X r) (23 * ((r 4).length + (r 7).length) + 8) := by
  have h1 := runs_popLoop (S := 4) (X := X) (P := 7) hX4.symm (by decide) hX8 (by decide) hX7
    (by decide) Γ r
  have h2 := runs_xfer 7 [] [4] (by simp) (by simp) Γ (popLoopF 4 X 7 (r 4).length r)
  rw [skipN_state hX4 hX7 hX8] at h2
  refine (h1.join h2).mono ?_
  have e : (popLoopF 4 X 7 (r 4).length r 7).length = (r 4).length + (r 7).length := by
    simp [popLoopF, hX7.symm]
  simp only [List.length_cons, List.length_nil, e]
  omega

theorem skipNF_X (r : Rg) : skipNF X r X = (r X).drop (r 4).length := by simp [skipNF]
theorem skipNF_8 (r : Rg) :
    skipNF X r 8 = List.replicate ((r 4).length - (r X).length) true ++ r 8 := by
  simp [skipNF, hX8.symm]
theorem skipNF_4 (r : Rg) : skipNF X r 4 = List.replicate ((r 4).length + (r 7).length) true := by
  simp [skipNF, hX4.symm]
theorem skipNF_7 (r : Rg) : skipNF X r 7 = [] := by simp [skipNF, hX7.symm]
theorem skipNF_other (r : Rg) {j : ℕ} (h1 : j ≠ X) (h2 : j ≠ 8) (h3 : j ≠ 4) (h4 : j ≠ 7) :
    skipNF X r j = r j := by simp [skipNF, h1, h2, h3, h4]

end skipN

/-! ## Repeat `skipN X` once for every element of `S` -/

def repSkip (S X : ℕ) : Pg := forEach S fun _ => skipN X

def repF (S X m v : ℕ) (r : Rg) : Rg := fun j =>
  if j = S then [] else
  if j = X then (r X).drop (m * v) else
  if j = 8 then List.replicate (m * v - (r X).length) true ++ r 8 else r j

section repSkip

variable {S X : ℕ} (hX4 : X ≠ 4) (hX7 : X ≠ 7) (hX8 : X ≠ 8) (hSX : S ≠ X) (hS4 : S ≠ 4)
  (hS7 : S ≠ 7) (hS8 : S ≠ 8)
include hX4 hX7 hX8 hSX hS4 hS7 hS8

theorem rep_iterate (v : ℕ) (l : List Bool) : ∀ r : Rg, r S = l → r 4 = List.replicate v true →
    r 7 = [] → (eachStep S (fun _ => skipNF X))^[l.length] r = repF S X l.length v r := by
  induction l with
  | nil =>
    intro r hr _ _
    funext j
    simp only [List.length_nil, Function.iterate_zero, id, repF, zero_mul, List.drop_zero,
      Nat.zero_sub, List.replicate_zero, List.nil_append]
    split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all
  | cons a l ih =>
    intro r hr h4 h7
    set r1 := Function.update r S l with hr1
    have e4 : r1 4 = List.replicate v true := by simp [hr1, Function.update_apply, hS4.symm, h4]
    have e7 : r1 7 = [] := by simp [hr1, Function.update_apply, hS7.symm, h7]
    have eX : r1 X = r X := by simp [hr1, Function.update_apply, hSX.symm]
    have e8 : r1 8 = r 8 := by simp [hr1, Function.update_apply, hS8.symm]
    have hS : skipNF X r1 S = l := by
      rw [skipNF_other hX4 hX7 hX8 r1 hSX hS8 hS4 hS7]; simp [hr1]
    have h4' : skipNF X r1 4 = List.replicate v true := by
      rw [skipNF_4 hX4 hX7 hX8, e4, e7]; simp
    have h7' : skipNF X r1 7 = [] := skipNF_7 hX4 hX7 hX8 r1
    rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons hr, ih _ hS h4' h7']
    funext j
    simp only [repF]
    by_cases j1 : j = S
    · simp [j1]
    · by_cases j2 : j = X
      · subst j2
        simp only [j1, if_false, if_true]
        rw [skipNF_X hX4 hX7 hX8, eX, e4, List.length_replicate, List.drop_drop]
        congr 1; ring
      · by_cases j3 : j = 8
        · subst j3
          simp only [j1, j2, if_false, if_true]
          rw [skipNF_X hX4 hX7 hX8, skipNF_8 hX4 hX7 hX8, eX, e4, e8, List.length_replicate,
            List.length_drop, ← List.append_assoc, ← List.replicate_add]
          congr 2
          have e : (l.length + 1) * v = l.length * v + v := by ring
          rw [e]
          omega
        · simp only [j1, j2, j3, if_false]
          by_cases j4 : j = 4
          · subst j4; rw [h4', h4]
          · by_cases j5 : j = 7
            · subst j5; rw [h7', h7]
            · rw [skipNF_other hX4 hX7 hX8 r1 j2 j3 j4 j5]; simp [hr1, Function.update_apply, j1]

theorem runs_repSkip (v : ℕ) (Γ : Sc) (r : Rg) (h4 : r 4 = List.replicate v true) (h7 : r 7 = []) :
    Runs Γ (repSkip S X) r (repF S X (r S).length v r) ((r S).length * (23 * v + 15) + 3) := by
  have h := runs_forEach_inv S _ (fun _ => skipNF X) (23 * v + 8)
    (fun r => r 4 = List.replicate v true ∧ r 7 = [])
    (fun Γ a r hr => (runs_skipN hX4 hX7 hX8 Γ r).mono (by rw [hr.1, hr.2]; simp))
    (fun a r hr => ⟨by rw [skipNF_4 hX4 hX7 hX8, hr.1, hr.2]; simp, skipNF_7 hX4 hX7 hX8 r⟩)
    (fun r l hr => ⟨by simp [Function.update_apply, hS4.symm, hr.1],
      by simp [Function.update_apply, hS7.symm, hr.2]⟩)
    (fun a r => skipNF_other hX4 hX7 hX8 r hSX hS8 hS4 hS7) Γ r ⟨h4, h7⟩
  rw [rep_iterate hX4 hX7 hX8 hSX hS4 hS7 hS8 v _ r rfl h4 h7] at h
  exact h.mono (le_of_eq (by ring))

end repSkip

/-! ## Fuel: register 3 holds the fuel; `fuelPush R` moves one unit of fuel to `R` -/

def fuelPush (R : ℕ) : Pg := .look 3 fun o => match o with
  | none => flag
  | some _ => .join (.pop 3) (.push R true)

def fuelPushF (R : ℕ) (r : Rg) : Rg :=
  match r 3 with
  | [] => flagF r
  | _ :: l => Function.update (Function.update r 3 l) R (true :: r R)

theorem runs_fuelPush {Γ : Sc} {R : ℕ} (hR3 : R ≠ 3) (r : Rg) :
    Runs Γ (fuelPush R) r (fuelPushF R r) 5 := by
  unfold fuelPush
  cases h : r 3 with
  | nil =>
    have : fuelPushF R r = flagF r := by simp [fuelPushF, h]
    rw [this]
    refine Runs.look (c := fun o => match o with
      | none => flag | some _ => .join (.pop 3) (.push R true)) ?_
    rw [h]; exact (runs_flag r).mono (by omega)
  | cons a l =>
    have : fuelPushF R r = Function.update (Function.update r 3 l) R (true :: r R) := by
      simp [fuelPushF, h]
    rw [this]
    refine Runs.look (c := fun o => match o with
      | none => flag | some _ => .join (.pop 3) (.push R true)) ?_
    rw [h]
    have h2 := Runs.push (Γ := Γ) (r := Function.update r 3 l) R true
    have e : Function.update r 3 l R = r R := by simp [Function.update_apply, hR3]
    rw [e] at h2
    exact ((Runs.pop' h).join h2).mono (by omega)

/-- `k` fuel pushes on `R` from fuel `f`. -/
def pushK (R k f : ℕ) (r : Rg) : Rg := fun j =>
  if j = R then List.replicate (min k f) true ++ r R else
  if j = 3 then List.replicate (f - min k f) true else
  if j = 8 then List.replicate (k - min k f) true ++ r 8 else r j

section fuel

variable {R : ℕ} (hR3 : R ≠ 3) (hR7 : R ≠ 7) (hR8 : R ≠ 8)
include hR3 hR7 hR8

theorem fuelPushF_eq {f : ℕ} (r : Rg) (h3 : r 3 = List.replicate f true) :
    fuelPushF R r = pushK R 1 f r := by
  funext j
  unfold fuelPushF pushK flagF
  cases f with
  | zero =>
    simp only [List.replicate_zero] at h3
    simp only [h3]
    by_cases j1 : j = R
    · subst j1; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, hR8]
    · by_cases j2 : j = 3
      · subst j2; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, h3]
      · by_cases j3 : j = 8
        · subst j3; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8]
        · simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, j1, j2, j3]
  | succ g =>
    rw [List.replicate_succ] at h3
    simp only [h3]
    by_cases j1 : j = R
    · subst j1; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8]
    · by_cases j2 : j = 3
      · subst j2; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, Ne.symm hR3]
      · by_cases j3 : j = 8
        · subst j3; simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, Ne.symm hR8]
        · simp [Function.update_apply, hR3.symm, hR8.symm, hR3, hR8, j1, j2, j3]

theorem pushK_3 (k f : ℕ) (r : Rg) : pushK R k f r 3 = List.replicate (f - min k f) true := by
  simp [pushK, hR3.symm]

theorem pushK_zero {f : ℕ} (r : Rg) (h3 : r 3 = List.replicate f true) : pushK R 0 f r = r := by
  funext j
  unfold pushK
  split_ifs with h1 h2 h3' <;> subst_vars <;> simp_all

theorem pushK_pushK (a b f : ℕ) (r : Rg) :
    pushK R a (f - min b f) (pushK R b f r) = pushK R (b + a) f r := by
  funext j
  unfold pushK
  by_cases j1 : j = R
  · subst j1
    simp only [if_true, ← List.append_assoc, ← List.replicate_add]
    congr 2; omega
  · by_cases j2 : j = 3
    · subst j2; simp only [j1, if_false, if_true]; congr 1; omega
    · by_cases j3 : j = 8
      · subst j3
        simp only [j1, j2, if_false, if_true, ← List.append_assoc, ← List.replicate_add]
        congr 2; omega
      · simp [j1, j2, j3]

theorem pushK_7 (k f : ℕ) (r : Rg) : pushK R k f r 7 = r 7 := by
  simp [pushK, hR7.symm]

theorem pushK_upd7 (k f : ℕ) (r : Rg) (l : List Bool) :
    Function.update (pushK R k f (Function.update r 7 l)) 7 [] =
      Function.update (pushK R k f r) 7 [] := by
  funext j
  by_cases j7 : j = 7
  · subst j7; simp
  · simp [Function.update_apply, j7, pushK, hR7, hR7.symm]

theorem fuelPushF_7 (r : Rg) : fuelPushF R r 7 = r 7 := by
  unfold fuelPushF flagF
  rcases h : r 3 with _ | ⟨x, t⟩ <;> simp [Function.update_apply, hR7.symm]

def fpLoop (R : ℕ) : Pg := forEach 7 fun _ => .join (fuelPush R) (fuelPush R)

def fpAct (R : ℕ) (_ : Bool) (r : Rg) : Rg := fuelPushF R (fuelPushF R r)

theorem fpAct_eq {f : ℕ} (r : Rg) (h3 : r 3 = List.replicate f true) :
    fpAct R true r = pushK R 2 f r := by
  unfold fpAct
  rw [fuelPushF_eq hR3 hR7 hR8 r h3,
    fuelPushF_eq hR3 hR7 hR8 _ (pushK_3 hR3 hR7 hR8 1 f r), pushK_pushK hR3 hR7 hR8]

theorem fp_iterate (l : List Bool) : ∀ (r : Rg) (f : ℕ), r 7 = l → r 3 = List.replicate f true →
    (eachStep 7 (fpAct R))^[l.length] r = Function.update (pushK R (2 * l.length) f r) 7 [] := by
  induction l with
  | nil =>
    intro r f h7 h3
    simp only [List.length_nil, Function.iterate_zero, id, mul_zero]
    rw [pushK_zero hR3 hR7 hR8 r h3, ← h7, Function.update_eq_self]
  | cons a l ih =>
    intro r f h7 h3
    have h3' : (Function.update r 7 l) 3 = List.replicate f true := by
      simp [Function.update_apply, h3]
    have hA : fpAct R a (Function.update r 7 l) = pushK R 2 f (Function.update r 7 l) := by
      cases a <;> exact fpAct_eq hR3 hR7 hR8 _ h3'
    rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons h7, hA,
      ih _ (f - min 2 f) (by rw [pushK_7 hR3 hR7 hR8]; simp) (pushK_3 hR3 hR7 hR8 2 f _),
      pushK_pushK hR3 hR7 hR8, pushK_upd7 hR3 hR7 hR8]
    congr 2
    ring

theorem runs_fpLoop (Γ : Sc) (r : Rg) {f : ℕ} (h3 : r 3 = List.replicate f true) :
    Runs Γ (fpLoop R) r (Function.update (pushK R (2 * (r 7).length) f r) 7 [])
      ((r 7).length * 19 + 3) := by
  have h := runs_forEach 7 _ (fpAct R) 12
    (fun Γ a r => ((runs_fuelPush hR3 r).join (runs_fuelPush hR3 _)).mono (by omega))
    (fun a r => by unfold fpAct; rw [fuelPushF_7 hR3 hR7 hR8, fuelPushF_7 hR3 hR7 hR8]) Γ r
  rw [fp_iterate hR3 hR7 hR8 _ r f rfl h3] at h
  exact h

/-- Double the unary number in `R` and add `b`, paying every new unit with fuel. -/
def dbl (R : ℕ) (b : Bool) : Pg :=
  .join (xfer R [] [7]) (.join (fpLoop R) (if b then fuelPush R else .pass))

theorem runs_dbl (b : Bool) (Γ : Sc) (r : Rg) {f : ℕ} (h3 : r 3 = List.replicate f true)
    (h7 : r 7 = []) :
    Runs Γ (dbl R b) r (pushK R (2 * (r R).length + b.toNat) f (Function.update r R []))
      (30 * (r R).length + 15) := by
  have h1 := runs_xfer R [] [7] (by simp) (by simp [hR7]) Γ r
  set r1 := xferF R [] [7] r with hr1
  have e1 : r1 = Function.update (Function.update r R []) 7 (List.replicate (r R).length true) := by
    funext j
    simp only [hr1, xferF]
    by_cases jR : j = R
    · subst jR; simp [hR7]
    · by_cases j7 : j = 7
      · subst j7
        simp [jR, Function.update_apply, h7, flatMap_true]
      · have c1 : List.count j [7] = 0 := List.count_eq_zero_of_not_mem (by simp [j7])
        simp [jR, j7, c1, Function.update_apply, flatMap_nil']
  have h3' : r1 3 = List.replicate f true := by
    rw [e1]; simp [Function.update_apply, hR3.symm, h3]
  have h2 := runs_fpLoop hR3 hR7 hR8 Γ r1 h3'
  have e2 : Function.update (pushK R (2 * (r1 7).length) f r1) 7 [] =
      pushK R (2 * (r R).length) f (Function.update r R []) := by
    have : (r1 7).length = (r R).length := by rw [e1]; simp
    rw [this, e1, pushK_upd7 hR3 hR7 hR8]
    funext j
    by_cases j7 : j = 7
    · subst j7; simp [pushK, hR7.symm, Function.update_apply, h7]
    · simp [Function.update_apply, j7]
  rw [e2] at h2
  have hlen : (r1 7).length = (r R).length := by rw [e1]; simp
  set r2 := pushK R (2 * (r R).length) f (Function.update r R []) with hr2
  cases b with
  | false =>
    have h := h1.join (h2.join (Runs.pass (Γ := Γ) (r := r2)))
    rw [hlen] at h
    simp only [List.length_nil, List.length_cons, zero_add] at h
    simp only [Bool.toNat_false, add_zero]
    exact h.mono (by ring_nf; omega)
  | true =>
    have h4 := runs_fuelPush (Γ := Γ) hR3 r2
    rw [fuelPushF_eq hR3 hR7 hR8 r2 (pushK_3 hR3 hR7 hR8 _ f _), pushK_pushK hR3 hR7 hR8] at h4
    have h := h1.join (h2.join h4)
    rw [hlen] at h
    simp only [List.length_nil, List.length_cons, zero_add] at h
    simp only [Bool.toNat_true]
    exact h.mono (by ring_nf; omega)

end fuel

/-! ## Computing `N` from `n = |x|`: round `N` removes `4N + 2` units of register 10 -/

/-- Register shape during the computation of `N`: 4 = unary `N`, 7 empty, 10 = unary `m`,
8 = `f` flags on top of `L`; registers other than 4, 7, 8, 10, 13 equal `b`. -/
def U (r : Rg) (N m f : ℕ) (L : List Bool) (b : Rg) : Prop :=
  r 4 = List.replicate N true ∧ r 7 = [] ∧ r 10 = List.replicate m true ∧
    r 8 = List.replicate f true ++ L ∧
    ∀ j, j ≠ 4 → j ≠ 7 → j ≠ 8 → j ≠ 10 → j ≠ 13 → r j = b j

theorem U_congr {r : Rg} {N m f m' f' : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b)
    (hm : m = m') (hf : f = f') : U r N m' f' L b := by
  subst hm hf; exact h

theorem U_skip {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    U (skipNF 10 r) N (m - N) (f + (N - m)) L b := by
  obtain ⟨h4, h7, h10, h8, hj⟩ := h
  have a4 : (10 : ℕ) ≠ 4 := by decide
  have a7 : (10 : ℕ) ≠ 7 := by decide
  have a8 : (10 : ℕ) ≠ 8 := by decide
  refine ⟨?_, skipNF_7 a4 a7 a8 r, ?_, ?_, ?_⟩
  · rw [skipNF_4 a4 a7 a8, h4, h7]; simp
  · rw [skipNF_X a4 a7 a8, h10, h4, List.length_replicate, List.drop_replicate]
  · rw [skipNF_8 a4 a7 a8, h4, h10, h8, List.length_replicate, List.length_replicate,
      ← List.append_assoc, ← List.replicate_add, Nat.add_comm (N - m)]
  · intro j j4 j7 j8 j10 j13
    rw [skipNF_other a4 a7 a8 r j10 j8 j4 j7]; exact hj j j4 j7 j8 j10 j13

theorem U_pof {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    U (popOrFlagF 10 r) N (m - 1) (f + (1 - m)) L b := by
  obtain ⟨h4, h7, h10, h8, hj⟩ := h
  unfold popOrFlagF flagF
  cases m with
  | zero =>
    rw [h10]
    simp only [List.replicate_zero]
    refine ⟨by simp [Function.update_apply, h4], by simp [Function.update_apply, h7],
      by simp [Function.update_apply, h10], ?_, ?_⟩
    · simp [Function.update_apply, h8, List.replicate_succ]
    · intro j j4 j7 j8 j10 j13; simp [Function.update_apply, j8]; exact hj j j4 j7 j8 j10 j13
  | succ m =>
    rw [h10, List.replicate_succ]
    simp only []
    refine ⟨by simp [Function.update_apply, h4], by simp [Function.update_apply, h7],
      by simp [Function.update_apply], ?_, ?_⟩
    · simp [Function.update_apply, h8]
    · intro j j4 j7 j8 j10 j13; simp [Function.update_apply, j10]; exact hj j j4 j7 j8 j10 j13

theorem U_push {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    U (Function.update r 4 (true :: r 4)) (N + 1) m f L b := by
  obtain ⟨h4, h7, h10, h8, hj⟩ := h
  refine ⟨by simp [h4, List.replicate_succ], by simp [Function.update_apply, h7],
    by simp [Function.update_apply, h10], by simp [Function.update_apply, h8], ?_⟩
  intro j j4 j7 j8 j10 j13; simp [Function.update_apply, j4]; exact hj j j4 j7 j8 j10 j13

/-- One round: remove `4N + 2` units of register 10 (flag the shortfall), then `N := N + 1`. -/
def round : Pg := .join (skipN 10) (.join (skipN 10) (.join (skipN 10) (.join (skipN 10)
  (.join (popOrFlag 10) (.join (popOrFlag 10) (.push 4 true))))))

def roundF (r : Rg) : Rg :=
  let r4 := skipNF 10 (skipNF 10 (skipNF 10 (skipNF 10 r)))
  let r6 := popOrFlagF 10 (popOrFlagF 10 r4)
  Function.update r6 4 (true :: r6 4)

theorem U_round {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    U (roundF r) (N + 1) (m - (4 * N + 2)) (f + (4 * N + 2 - m)) L b := by
  have h6 := U_pof (U_pof (U_skip (U_skip (U_skip (U_skip h)))))
  have := U_push h6
  unfold roundF
  exact U_congr this (by omega) (by omega)

theorem runs_round {Γ : Sc} {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    Runs Γ round r (roundF r) (92 * N + 49) := by
  have a4 : (10 : ℕ) ≠ 4 := by decide
  have a7 : (10 : ℕ) ≠ 7 := by decide
  have a8 : (10 : ℕ) ≠ 8 := by decide
  have s1 := runs_skipN a4 a7 a8 Γ r
  have u1 := U_skip h
  have s2 := runs_skipN a4 a7 a8 Γ (skipNF 10 r)
  have u2 := U_skip u1
  have s3 := runs_skipN a4 a7 a8 Γ (skipNF 10 (skipNF 10 r))
  have u3 := U_skip u2
  have s4 := runs_skipN a4 a7 a8 Γ (skipNF 10 (skipNF 10 (skipNF 10 r)))
  have u4 := U_skip u3
  have p1 := runs_popOrFlag (Γ := Γ) 10 (skipNF 10 (skipNF 10 (skipNF 10 (skipNF 10 r))))
  have p2 := runs_popOrFlag (Γ := Γ) 10
    (popOrFlagF 10 (skipNF 10 (skipNF 10 (skipNF 10 (skipNF 10 r)))))
  have p3 := Runs.push (Γ := Γ)
    (r := popOrFlagF 10 (popOrFlagF 10 (skipNF 10 (skipNF 10 (skipNF 10 (skipNF 10 r)))))) 4 true
  rw [h.1, h.2.1] at s1
  rw [u1.1, u1.2.1] at s2
  rw [u2.1, u2.2.1] at s3
  rw [u3.1, u3.2.1] at s4
  refine (s1.join (s2.join (s3.join (s4.join (p1.join (p2.join p3)))))).mono ?_
  simp only [List.length_replicate, List.length_nil]
  omega

/-- The act of the `N` loop: a round while register 10 is nonempty. -/
def nAct : Pg := .look 10 fun o => match o with
  | none => .pass
  | some _ => round

def nActF (r : Rg) : Rg :=
  match r 10 with
  | [] => r
  | _ :: _ => roundF r

/-- The abstract round on `(N, m, f)`. -/
def rnd (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if s.2.1 = 0 then s else (s.1 + 1, s.2.1 - (4 * s.1 + 2), s.2.2 + (4 * s.1 + 2 - s.2.1))

theorem U_nAct {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    U (nActF r) (rnd (N, m, f)).1 (rnd (N, m, f)).2.1 (rnd (N, m, f)).2.2 L b := by
  unfold nActF rnd
  cases m with
  | zero => rw [h.2.2.1]; simpa using h
  | succ m =>
    rw [h.2.2.1, List.replicate_succ]
    simpa using U_round h

/-- Potential of the `N` loop. -/
def nPot (r : Rg) : ℕ := 100 * (r 10).length + (if r 10 = [] then 0 else 100 * (r 4).length + 50)

theorem nPot_U {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    nPot r = 100 * m + (if m = 0 then 0 else 100 * N + 50) := by
  unfold nPot
  rw [h.2.2.1, h.1, List.length_replicate, List.length_replicate]
  congr 1
  cases m <;> simp

theorem runs_nAct {Γ : Sc} {r : Rg} {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    Runs Γ nAct r (nActF r) (2 + nPot r - nPot (nActF r)) := by
  have h10 := h.2.2.1
  cases m with
  | zero =>
    have e : nActF r = r := by simp [nActF, h10]
    rw [e]
    have hl : Runs Γ nAct r r 2 := by
      refine Runs.look (c := fun o => match o with | none => .pass | some _ => round) ?_
      rw [h10]; exact Runs.pass
    exact hl.mono (by omega)
  | succ m =>
    have e : nActF r = roundF r := by simp [nActF, h10, List.replicate_succ]
    rw [e]
    have hr := runs_round (Γ := Γ) h
    have p1 := nPot_U h
    have p2 := nPot_U (U_round h)
    have hl : Runs Γ nAct r (roundF r) (92 * N + 49 + 1) := by
      refine Runs.look (c := fun o => match o with | none => .pass | some _ => round) ?_
      rw [h10, List.replicate_succ]; exact hr
    refine hl.mono ?_
    rw [p1, p2]
    rw [if_neg (Nat.succ_ne_zero m)]
    by_cases hz : m + 1 - (4 * N + 2) = 0
    · rw [if_pos hz]; omega
    · rw [if_neg hz]; omega

theorem pof_other (X : ℕ) (r : Rg) {j : ℕ} (h1 : j ≠ X) (h2 : j ≠ 8) : popOrFlagF X r j = r j := by
  unfold popOrFlagF flagF
  rcases e : r X with _ | ⟨x, t⟩ <;> simp [Function.update_apply, h1, h2]

theorem nActF_13 (r : Rg) : nActF r 13 = r 13 := by
  have a4 : (10 : ℕ) ≠ 4 := by decide
  have a7 : (10 : ℕ) ≠ 7 := by decide
  have a8 : (10 : ℕ) ≠ 8 := by decide
  unfold nActF
  rcases e : r 10 with _ | ⟨x, t⟩
  · rfl
  · simp only []
    unfold roundF
    simp only [Function.update_apply, show (13 : ℕ) ≠ 4 by decide, if_false]
    rw [pof_other 10 _ (by decide) (by decide), pof_other 10 _ (by decide) (by decide)]
    repeat rw [skipNF_other a4 a7 a8 _ (by decide) (by decide) (by decide) (by decide)]

def nLoop : Pg := forEach 13 fun _ => nAct

theorem n_iterate (L : List Bool) (b : Rg) (l : List Bool) : ∀ (r : Rg) (s : ℕ × ℕ × ℕ),
    r 13 = l → U r s.1 s.2.1 s.2.2 L b →
      U ((eachStep 13 (fun _ => nActF))^[l.length] r) (rnd^[l.length] s).1
        (rnd^[l.length] s).2.1 (rnd^[l.length] s).2.2 L b := by
  induction l with
  | nil => intro r s _ h; simpa using h
  | cons a l ih =>
    intro r s h13 h
    rw [List.length_cons, Function.iterate_succ_apply, Function.iterate_succ_apply, eachStep_cons h13]
    have h' : U (Function.update r 13 l) s.1 s.2.1 s.2.2 L b := by
      obtain ⟨h4, h7, h10, h8, hj⟩ := h
      refine ⟨by simp [Function.update_apply, h4], by simp [Function.update_apply, h7],
        by simp [Function.update_apply, h10], by simp [Function.update_apply, h8], ?_⟩
      intro j j4 j7 j8 j10 j13
      simp [Function.update_apply, j13]; exact hj j j4 j7 j8 j10 j13
    exact ih _ _ (by rw [nActF_13]; simp) (U_nAct h')

theorem runs_nLoop (Γ : Sc) (r : Rg) {N m f : ℕ} {L : List Bool} {b : Rg} (h : U r N m f L b) :
    Runs Γ nLoop r ((eachStep 13 (fun _ => nActF))^[(r 13).length] r)
      ((r 13).length * 9 + nPot r + 3) := by
  refine runs_forEach_gen 13 (fun _ => nAct) (fun _ => nActF) 2 nPot
    (fun r => ∃ N m f, U r N m f L b)
    (fun Γ a r ⟨N, m, f, hU⟩ => runs_nAct hU)
    (fun a r ⟨N, m, f, hU⟩ => ?_)
    (fun r l ⟨N, m, f, hU⟩ => le_of_eq (by simp [nPot, Function.update_apply]))
    (fun a r ⟨N, m, f, hU⟩ => ⟨_, _, _, U_nAct hU⟩)
    (fun r l ⟨N, m, f, hU⟩ => ?_)
    (fun a r => nActF_13 r) Γ r ⟨N, m, f, h⟩
  · rw [nPot_U hU, nPot_U (U_nAct hU)]
    unfold rnd
    split_ifs <;> simp_all <;> omega
  · obtain ⟨h4, h7, h10, h8, hj⟩ := hU
    refine ⟨N, m, f, by simp [Function.update_apply, h4], by simp [Function.update_apply, h7],
      by simp [Function.update_apply, h10], by simp [Function.update_apply, h8], ?_⟩
    intro j j4 j7 j8 j10 j13
    simp [Function.update_apply, j13]; exact hj j j4 j7 j8 j10 j13

end P1Case1.CoTrans
