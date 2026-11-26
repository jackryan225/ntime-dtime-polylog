import P1Case1.CoTransGuess

/-!
# P1, Case 1, task C1: decoding the guess bits into unary numbers (lane case1b, copy A)

`decode S R = forEach S (dbl0 R)`: pop the bits of register `S` (top first) and replace the unary number
`v` in register `R` by `2 v + b` (`dbl0`, through the scratch register `7`). From `v = 0` the result is
`val s` (`CoTransSpec.lean`). The cost is not uniform: a step costs `O(v)`; the bound
`40 qq |s| (v + 1) + 40 |s| + 3` (with `qq L = 2^(L+1) - 1`) pays for it.

Register contract with copy B (board 09:19Z): after `readGuess; decode 1 5; decode 2 6` the registers are
`0 = x`, `5 = i` (unary), `6 = k` (unary), all other registers as before (`1`, `2`, `7` empty).
-/

namespace P1Case1.CoTransV

open OAI.Computability.IntegerMultiplication P1Case1.CoTrans C1Challenge

theorem fm_const (l : List Bool) (k : ℕ) :
    l.flatMap (fun _ => List.replicate k true) = List.replicate (k * l.length) true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, ih, ← List.replicate_add]
    congr 1
    simp only [List.length_cons]
    ring

theorem fm_nil (l : List Bool) : l.flatMap (fun _ => ([] : List Bool)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Double the unary number of `R` and add `b` (scratch register `7`). -/
def dbl0 (R : ℕ) (b : Bool) : Pg :=
  .join (xfer R [] [7]) (.join (xfer 7 [] [R, R]) (if b then .push R true else .pass))

theorem runs_dbl0 {R : ℕ} (hR7 : R ≠ 7) (b : Bool) (Γ : Sc) (r : Rg) (v : ℕ)
    (hR : r R = List.replicate v true) (h7 : r 7 = []) :
    Runs Γ (dbl0 R b) r (Function.update r R (List.replicate (2 * v + b.toNat) true))
      (25 * v + 12) := by
  have h1 := runs_xfer R [] [7] (by simp) (by simp [hR7]) Γ r
  have e1 : xferF R [] [7] r =
      Function.update (Function.update r R []) 7 (List.replicate v true) := by
    funext j
    simp only [xferF]
    by_cases jR : j = R
    · rw [jR]; simp [hR7]
    · by_cases j7 : j = 7
      · rw [j7]
        have jR' : ¬ (7 = R) := by rw [← j7]; exact jR
        have hc : List.count 7 [7] = 1 := by simp
        simp only [jR', if_false, hR, List.reverse_replicate, hc, List.count_nil,
          List.replicate_zero, List.append_nil, fm_const, h7, Function.update_self, one_mul,
          List.length_replicate]
      · have hc : List.count j [7] = 0 := List.count_eq_zero_of_not_mem (by simp [j7])
        simp only [jR, if_false, hc, List.count_nil, List.replicate_zero, List.append_nil,
          fm_nil, List.nil_append]
        rw [Function.update_of_ne j7, Function.update_of_ne jR]
  rw [e1] at h1
  set r1 := Function.update (Function.update r R []) 7 (List.replicate v true) with hr1
  have h17 : r1 7 = List.replicate v true := by simp [hr1]
  have h1R : r1 R = [] := by simp [hr1, hR7]
  have h2 := runs_xfer 7 [] [R, R] (by simp) (by simp [Ne.symm hR7]) Γ r1
  have e2 : xferF 7 [] [R, R] r1 = Function.update r R (List.replicate (2 * v) true) := by
    funext j
    simp only [xferF]
    by_cases j7 : j = 7
    · rw [j7]; simp [Function.update_apply, Ne.symm hR7, h7]
    · by_cases jR : j = R
      · rw [jR]
        have hc : List.count R [R, R] = 2 := by simp
        simp only [hR7, if_false, h17, List.reverse_replicate, hc, List.count_nil,
          List.replicate_zero, List.append_nil, fm_const, h1R, Function.update_self,
          List.length_replicate]
      · have hc : List.count j [R, R] = 0 := List.count_eq_zero_of_not_mem (by simp [jR])
        simp only [j7, if_false, hc, List.count_nil, List.replicate_zero, List.append_nil,
          fm_nil, List.nil_append, hr1]
        rw [Function.update_of_ne j7, Function.update_of_ne jR, Function.update_of_ne jR]
  rw [e2] at h2
  rw [h17, List.length_replicate] at h2
  rw [hR, List.length_replicate] at h1
  cases b with
  | false =>
    have h := h1.join (h2.join (Runs.pass (Γ := Γ)
      (r := Function.update r R (List.replicate (2 * v) true))))
    simp only [Bool.toNat_false, add_zero]
    exact h.mono (by simp only [List.length_nil, List.length_cons]; omega)
  | true =>
    have h3 := Runs.push (Γ := Γ) (r := Function.update r R (List.replicate (2 * v) true)) R true
    have e3 : Function.update (Function.update r R (List.replicate (2 * v) true)) R
        (true :: Function.update r R (List.replicate (2 * v) true) R) =
        Function.update r R (List.replicate (2 * v + Bool.toNat true) true) := by
      rw [Function.update_idem, Function.update_self]
      congr 1
    rw [e3] at h3
    have h := h1.join (h2.join h3)
    exact h.mono (by simp only [List.length_nil, List.length_cons]; omega)

/-- `qq L = 2^(L+1) - 1`. -/
def qq : ℕ → ℕ
  | 0 => 1
  | L + 1 => 2 * qq L + 1

theorem qq_succ_eq (L : ℕ) : qq L + 1 = 2 ^ (L + 1) := by
  induction L with
  | zero => simp [qq]
  | succ L ih => rw [qq, pow_succ, ← ih]; ring

theorem qq_le (L : ℕ) : qq L ≤ 2 ^ (L + 1) := by
  have := qq_succ_eq L; omega

/-- The unary step on numbers. -/
def stepV (v : ℕ) (b : Bool) : ℕ := 2 * v + b.toNat

/-- Registers after decoding `l` from register `S` onto `v` in register `R`. -/
def decF (S R : ℕ) (l : List Bool) (v : ℕ) (r : Rg) : Rg :=
  Function.update (Function.update r S []) R (List.replicate (l.foldl stepV v) true)

theorem run_decBody {S R : ℕ} (hSR : S ≠ R) (hS7 : S ≠ 7) (hR7 : R ≠ 7) (Γ : Sc) :
    ∀ (l : List Bool) (r : Rg) (v : ℕ), r S = l → r R = List.replicate v true → r 7 = [] →
      Runs (eachBody S (dbl0 R) :: Γ) (eachBody S (dbl0 R)) r (decF S R l v r)
        (40 * qq l.length * (v + 1) + 40 * l.length + 2) := by
  intro l
  induction l with
  | nil =>
    intro r v hS hR h7
    have e : decF S R [] v r = r := by
      funext j
      simp only [decF, List.foldl_nil, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; exact hR.symm
      · subst h2; exact hS.symm
      · rfl
    rw [e]
    have h : Runs (eachBody S (dbl0 R) :: Γ) (eachBody S (dbl0 R)) r r 2 := by
      refine Runs.look (c := fun o => match o with
        | none => .pass
        | some a => .join (.pop S) (.join (dbl0 R a) (.again 0))) ?_
      rw [hS]
      exact Runs.pass
    exact h.mono (by omega)
  | cons b l ih =>
    intro r v hS hR h7
    set r1 := Function.update r S l with hr1
    have h1R : r1 R = List.replicate v true := by rw [hr1, Function.update_of_ne (Ne.symm hSR), hR]
    have h17 : r1 7 = [] := by rw [hr1, Function.update_of_ne (by omega), h7]
    have hd := runs_dbl0 hR7 b (eachBody S (dbl0 R) :: Γ) r1 v h1R h17
    set r2 := Function.update r1 R (List.replicate (2 * v + b.toNat) true) with hr2
    have h2S : r2 S = l := by rw [hr2, Function.update_of_ne hSR, hr1, Function.update_self]
    have h2R : r2 R = List.replicate (stepV v b) true := by rw [hr2, Function.update_self]; rfl
    have h27 : r2 7 = [] := by rw [hr2, Function.update_of_ne (Ne.symm hR7), h17]
    have hrest := ih r2 (stepV v b) h2S h2R h27
    have e : decF S R l (stepV v b) r2 = decF S R (b :: l) v r := by
      funext j
      simp only [decF, List.foldl_cons, Function.update_apply, hr2, hr1]
      split_ifs <;> simp_all
    rw [e] at hrest
    have h : Runs (eachBody S (dbl0 R) :: Γ) (eachBody S (dbl0 R)) r (decF S R (b :: l) v r)
        ((1 + ((25 * v + 12) + ((40 * qq l.length * (stepV v b + 1) + 40 * l.length + 2) + 1) + 2)
          + 2) + 1) := by
      refine Runs.look (c := fun o => match o with
        | none => .pass
        | some a => .join (.pop S) (.join (dbl0 R a) (.again 0))) ?_
      rw [hS]
      exact (Runs.pop' hS).join (hd.join (Runs.again0 hrest))
    refine h.mono ?_
    have key : qq l.length * (stepV v b + 1) ≤ qq l.length * (2 * (v + 1)) :=
      Nat.mul_le_mul_left _ (by cases b <;> simp [stepV] <;> omega)
    simp only [List.length_cons, qq]
    nlinarith [key]

/-- Decode register `S` onto register `R` (through the scratch register `7`). -/
def decode (S R : ℕ) : Pg := forEach S (dbl0 R)

theorem foldl_stepV_zero (l : List Bool) : l.foldl stepV 0 = val l := rfl

/-- **Decoding.** From `R = []` and `7 = []`: afterwards `S = []`, `R` = `val (r S)` in unary. -/
theorem runs_decode {S R : ℕ} (hSR : S ≠ R) (hS7 : S ≠ 7) (hR7 : R ≠ 7) (Γ : Sc) (r : Rg)
    (hR : r R = []) (h7 : r 7 = []) :
    Runs Γ (decode S R) r
      (Function.update (Function.update r S []) R (List.replicate (val (r S)) true))
      (80 * 2 ^ (r S).length + 40 * (r S).length + 3) := by
  have h := (run_decBody hSR hS7 hR7 Γ (r S) r 0 rfl (by rw [hR]; rfl) h7).tie
  have hq := qq_le (r S).length
  rw [pow_succ] at hq
  exact h.mono (by nlinarith [hq])

/-- Value bound. -/
theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  have key : ∀ (l : List Bool) (v : ℕ), l.foldl stepV v < (v + 1) * 2 ^ l.length := by
    intro l
    induction l with
    | nil => intro v; simp
    | cons b l ih =>
      intro v
      have := ih (stepV v b)
      simp only [List.foldl_cons, List.length_cons, pow_succ]
      have hb : stepV v b + 1 ≤ 2 * (v + 1) := by cases b <;> simp [stepV] <;> omega
      calc l.foldl stepV (stepV v b) < (stepV v b + 1) * 2 ^ l.length := this
        _ ≤ (2 * (v + 1)) * 2 ^ l.length := Nat.mul_le_mul_right _ hb
        _ = (v + 1) * (2 ^ l.length * 2) := by ring
  rw [← foldl_stepV_zero]
  simpa using key l 0

end P1Case1.CoTransV
