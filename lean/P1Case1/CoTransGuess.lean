import P1Case1.CoTransProg
import P1Case1.CoTransSpec

/-!
# P1, Case 1, task C1: reading the guess (lane case1b, copy A)

`readGuess` reads the guess prefix of `withGuess w x` from register `0`: every guess bit comes as the pair
`true, b`; bits at even positions go to register `1`, bits at odd positions to register `2`; the separator
`false` is popped. Afterwards register `0` holds `x`.

`run_readGuess`: exact cost `readCost w + 1 ≤ 12 |w| + 14`, result `readF w x r`.
-/

namespace P1Case1.CoTransV

open OAI.Computability.IntegerMultiplication P1Case1.CoTrans C1Challenge

theorem Run_cost_eq {Γ : Sc} {p : Pg} {r s : Rg} {n m : ℕ} (h : Prog.Run Γ p r n s) (e : n = m) :
    Prog.Run Γ p r m s := e ▸ h

theorem Run_state_eq {Γ : Sc} {p : Pg} {r s s' : Rg} {n : ℕ} (h : Prog.Run Γ p r n s) (e : s = s') :
    Prog.Run Γ p r n s' := e ▸ h

/-- One or two guess bits per round. -/
def readBody : Pg :=
  .look 0 fun o => match o with
  | some true => .join (.pop 0) (.look 0 fun o => match o with
      | some v => .join (.pop 0) (.join (.push 1 v) (.look 0 fun o => match o with
          | some true => .join (.pop 0) (.look 0 fun o => match o with
              | some v' => .join (.pop 0) (.join (.push 2 v') (.again 0))
              | none => .pass)
          | _ => .pop 0))
      | none => .pass)
  | _ => .pop 0

def readGuess : Pg := .tie readBody

/-- The guess prefix. -/
def pairs (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

theorem withGuess_eq (w x : List Bool) : withGuess w x = pairs w ++ false :: x := rfl

/-- Registers after reading the guess. -/
def readF (w x : List Bool) (r : Rg) : Rg :=
  Function.update (Function.update (Function.update r 0 x) 1 ((evens w).reverse ++ r 1)) 2
    ((odds w).reverse ++ r 2)

/-- Exact cost of the loop body. -/
def readCost : List Bool → ℕ
  | [] => 2
  | [_] => 13
  | _ :: _ :: t => readCost t + 23

theorem readCost_le : ∀ w : List Bool, readCost w ≤ 12 * w.length + 13
  | [] => by simp [readCost]
  | [_] => by simp [readCost]
  | _ :: _ :: t => by
    have := readCost_le t
    simp only [readCost, List.length_cons]
    omega

theorem run_readBody (Γ : Sc) (x : List Bool) :
    ∀ (m : ℕ) (w : List Bool), w.length ≤ m → ∀ r : Rg, r 0 = pairs w ++ false :: x →
      Prog.Run (readBody :: Γ) readBody r (readCost w) (readF w x r) := by
  intro m
  induction m with
  | zero =>
    intro w hw r hr
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [← Function.update_eq_self 0 r, hr]
    refine Run_state_eq (Run_cost_eq (Prog.Run.look Prog.Run.pop) rfl) ?_
    funext j
    simp only [readF, Function.update_apply, evens, odds, List.reverse_nil, List.nil_append, pairs,
      List.flatMap_nil]
    split_ifs <;> simp_all
  | succ m ih =>
    intro w hw r hr
    match w, hw, hr with
    | [], _, hr =>
      rw [← Function.update_eq_self 0 r, hr]
      refine Run_state_eq (Run_cost_eq (Prog.Run.look Prog.Run.pop) rfl) ?_
      funext j
      simp only [readF, Function.update_apply, evens, odds, List.reverse_nil, List.nil_append, pairs,
        List.flatMap_nil]
      split_ifs <;> simp_all
    | [v], _, hr =>
      rw [← Function.update_eq_self 0 r, hr]
      refine Run_state_eq (Run_cost_eq (Prog.Run.look (Prog.Run.join Prog.Run.pop
        (Prog.Run.look (Prog.Run.join Prog.Run.pop (Prog.Run.join Prog.Run.push
          (Prog.Run.look Prog.Run.pop)))))) rfl) ?_
      funext j
      simp only [readF, Function.update_apply, evens, odds, List.reverse_nil, List.nil_append, pairs]
      split_ifs <;> simp_all
    | v :: v' :: t, hw, hr =>
      have hrest := ih t (by simp only [List.length_cons] at hw; omega)
      rw [← Function.update_eq_self 0 r, hr]
      refine Run_state_eq (Run_cost_eq (Prog.Run.look (Prog.Run.join Prog.Run.pop
        (Prog.Run.look (Prog.Run.join Prog.Run.pop (Prog.Run.join Prog.Run.push
          (Prog.Run.look (Prog.Run.join Prog.Run.pop (Prog.Run.look (Prog.Run.join Prog.Run.pop
            (Prog.Run.join Prog.Run.push (Prog.Run.again rfl (hrest _ ?h0)))))))))))) ?cost) ?state
      case h0 => simp [pairs]
      case cost => simp only [readCost]; omega
      case state =>
        funext j
        rcases Nat.lt_or_ge j 3 with hj | hj
        · interval_cases j <;> simp [readF, evens, odds, pairs]
        · have h0 : j ≠ 0 := by omega
          have h1 : j ≠ 1 := by omega
          have h2 : j ≠ 2 := by omega
          simp [readF, h0, h1, h2]

/-- **Reading the guess.** -/
theorem run_readGuess (Γ : Sc) (w x : List Bool) (r : Rg) (hr : r 0 = withGuess w x) :
    Runs Γ readGuess r (readF w x r) (12 * w.length + 14) :=
  ⟨1 + readCost w, Prog.Run.tie (run_readBody Γ x w.length w le_rfl r hr),
    by have := readCost_le w; omega⟩

end P1Case1.CoTransV
