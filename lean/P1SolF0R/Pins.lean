import P1P5.Factor0Target
import P1SolC10P.Primitives

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

def symbolCode (M : FiniteMultiTapeMachine) (s : M.Γ) : ℕ :=
  (Fintype.equivFin M.Γ s).val + 1

/-- A fixed symbol code (zero for an unknown guess bit), or an address in the raw input. -/
abbrev PinQuery := ℕ ⊕ ℕ

/-- Positions are supplied as a difference of two natural numbers. -/
def pinQuery (M : FiniteMultiTapeMachine) (p : Bool × ℕ × ℕ × ℕ) : PinQuery :=
  let (inputTape, guessLen, pos, neg) := p
  let cell := pos - neg
  bif !inputTape || decide (pos < neg) then .inl (symbolCode M default) else
    bif decide (cell < 2 * guessLen) then
      bif decide (cell % 2 = 1) then .inl 0 else .inl (symbolCode M (M.inputSymbol true))
    else bif decide (cell = 2 * guessLen) then .inl (symbolCode M (M.inputSymbol false))
    else .inr (cell - (2 * guessLen + 1))

@[local fun_prop] theorem pinAddress_poly : Poly (Sum.inr : ℕ → PinQuery) :=
  Easy.rightSum.poly

theorem pinQuery_poly (M : FiniteMultiTapeMachine) : Poly (pinQuery M) := by
  unfold pinQuery
  fun_prop

/-- Fetch one bit for a raw input pin. Fixed pins use a zero-width request. -/
def pinReq : PinQuery → P1Batch.Req
  | .inl _ => ([], [])
  | .inr i => (binary i, [true])

def resolvePin (M : FiniteMultiTapeMachine) (q : PinQuery) (bits : List Bool) : ℕ :=
  match q with
  | .inl v => v
  | .inr _ => symbolCode M ((bits.head?).elim default M.inputSymbol)

private theorem singleton_slice {A : Type} (xs : List A) (i : ℕ) :
    (((xs.drop i).take 1).head?) = xs[i]? := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

/-- An initial-content pin looks up precisely the requested raw input bit. -/
theorem resolvePin_eq (M : FiniteMultiTapeMachine) (x : List Bool) (g p n : ℕ) (k : M.K) :
    let q := pinQuery M (decide (k = M.inputTape), g, p, n)
    let cell := (p : ℤ) - (n : ℤ)
    resolvePin M q (P1Batch.fetch x (pinReq q)) =
      if ((withGuessLayout (M := M) x g).guessAt k cell).isSome then 0
      else symbolCode M ((withGuessLayout (M := M) x g).base k cell) := by
  dsimp only
  change _ = if (withGuessAt (M := M) g k ((p : ℤ) - (n : ℤ))).isSome then 0
    else symbolCode M ((absRun M (guessWord (List.ofFn fun _ : Fin g => false) x) 0).cells k ((p : ℤ) - (n : ℤ)))
  rw [absInit_cells]
  by_cases hk : k = M.inputTape
  · by_cases hp : p < n
    · have ht : ¬ (0 : ℤ) ≤ (p : ℤ) - (n : ℤ) := by omega
      simp only [pinQuery, hk, hp, decide_true, Bool.not_true, Bool.false_or, Bool.cond_true, resolvePin,
        withGuessAt, ht, and_false, false_and, dite_false, Option.isSome_none, Bool.false_eq_true, if_false]
    · let c := p - n
      have hnp : n ≤ p := Nat.le_of_not_gt hp
      have hz : (p : ℤ) - (n : ℤ) = (c : ℤ) := by
        simp only [c, Int.ofNat_sub hnp]
      rw [hz]
      have hc : k = M.inputTape ∧ (0 : ℤ) ≤ (c : ℤ) := ⟨hk, Int.natCast_nonneg _⟩
      rw [ite_eq_left hc]
      have hTape : decide (k = M.inputTape) = true := decide_eq_true hk
      simp only [pinQuery, hTape, hp, decide_true, decide_false, Bool.not_true, Bool.false_or,
        Bool.cond_false, Int.toNat_natCast, guessWord_getElem?, List.length_ofFn]
      by_cases hguess : c < 2 * g
      · by_cases hodd : c % 2 = 1
        · have hh : k = M.inputTape ∧ (0 : ℤ) ≤ (c : ℤ) ∧ (c : ℤ) < 2 * g ∧ (c : ℤ) % 2 = 1 := by
            refine ⟨hk, Int.natCast_nonneg _, ?_, ?_⟩ <;> omega
          simp only [show p - n = c from rfl, hguess, hodd, decide_true, Bool.cond_true,
            withGuessAt, dite_eq_left hh, Option.isSome_some, if_true, resolvePin]
        · have heven : c % 2 = 0 := by omega
          have hh : ¬ (k = M.inputTape ∧ (0 : ℤ) ≤ (c : ℤ) ∧ (c : ℤ) < 2 * g ∧ (c : ℤ) % 2 = 1) := by
            intro h
            exact hodd (by omega)
          simp only [show p - n = c from rfl, hguess, hodd, heven, Nat.zero_ne_one, decide_true, decide_false,
            Bool.cond_true, Bool.cond_false, withGuessAt, dite_eq_right hh, Option.isSome_none,
            Bool.false_eq_true, if_false, if_true, resolvePin, Option.map_some, Option.getD_some]
      · have hh : ¬ (k = M.inputTape ∧ (0 : ℤ) ≤ (c : ℤ) ∧ (c : ℤ) < 2 * g ∧ (c : ℤ) % 2 = 1) := by
          intro h
          exact hguess (by omega)
        simp only [show p - n = c from rfl, hguess, decide_false, Bool.cond_false,
          withGuessAt, dite_eq_right hh, Option.isSome_none, Bool.false_eq_true, if_false]
        by_cases he : c = 2 * g
        · simp only [he, Nat.sub_self, List.getElem?_cons_zero, Option.map_some, Option.getD_some,
            decide_true, Bool.cond_true, resolvePin]
        · have hs : c - 2 * g = (c - (2 * g + 1)) + 1 := by omega
          rw [hs, List.getElem?_cons_succ]
          simp only [he, decide_false, Bool.cond_false, resolvePin, P1Batch.fetch, pinReq, bval_binary,
            P1Batch.bval, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, singleton_slice]
          cases x[c - (2 * g + 1)]? <;> rfl
  · simp only [pinQuery, hk, decide_false, Bool.not_false, Bool.true_or, Bool.cond_true,
      resolvePin, withGuessAt, false_and, dite_false, Option.isSome_none, Bool.false_eq_true, if_false]

private def pinView : PinQuery → Bool × ℕ
  | .inl i => (false, i)
  | .inr i => (true, i)

private theorem pinView_poly : Poly pinView := by
  apply Easy.poly
  exact ((Easy.identity (X := Bool × ℕ)).on pinView).conform
    (fun q => by cases q <;> rfl) (fun q => by cases q <;> rfl) (fun _ => rfl)

theorem pinReq_poly : Poly pinReq := by
  let f (p : Bool × ℕ) : P1Batch.Req := bif p.1 then (binary p.2, [true]) else ([], [])
  have hf : Poly f := by unfold f; fun_prop
  convert pinView_poly.compose hf using 1
  funext q
  cases q <;> rfl

theorem resolvePin_poly (M : FiniteMultiTapeMachine) :
    Poly (fun p : PinQuery × List Bool => resolvePin M p.1 p.2) := by
  let code (p : Bool × Bool) : ℕ :=
    symbolCode M (bif p.1 then default else M.inputSymbol p.2)
  have hc : Poly code := (Easy.finite _).poly
  let sub (p : (Bool × ℕ) × List Bool) :=
    bif p.1.1 then code (p.2.isEmpty, p.2.headD false) else p.1.2
  have hs : Poly sub := by
    have he : Poly (fun p : (Bool × ℕ) × List Bool => p.2.isEmpty) :=
      Easy.snd.poly.compose (Carry.vacant Bool).poly
    have hh : Poly (fun p : (Bool × ℕ) × List Bool => p.2.headD false) :=
      Easy.snd.poly.compose (Iter.leader false).poly
    have ht : Poly (fun p : (Bool × ℕ) × List Bool => p.1.1) := by fun_prop
    exact ht.choose ((he.pair hh).compose hc) (by fun_prop)
  convert (((Easy.fst.poly.compose pinView_poly).pair Easy.snd.poly).compose hs) using 1
  funext p
  obtain ⟨q, bits⟩ := p
  cases q <;> cases bits <;> rfl


end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.resolvePin_eq
