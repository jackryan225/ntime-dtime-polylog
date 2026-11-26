import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Bits.Add

/-!
# P1Batch.Sort: polynomial-time insertion sort by a key, and the two comparators of the batch

`splice`, `arrange`, `fold_perm`, `arrange_poly` are COPIES of OpenAI's
`OAI/Computability/MultitapeWeakETH/SyntaxSort.lean` (openai/math@3344da5; `splice` and `fold_perm` are private
there, and that module is not in the closure of the P1 projects). New here: sortedness by a numeric key
(`arrange_sorted`), the address comparator (borrow of `Bits.sub`) and the tag comparator (`Iter.small`).
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open scoped List

section Arrange
variable {X : Type} (lt : X × X → Bool)

/-- Insert `x` after the entries that are smaller (copy of OAI `SyntaxSort.splice`). -/
def splice (xs : List X) (x : X) : List X :=
  xs.filter (fun y => lt (y,x)) ++ x :: xs.filter (fun y => !(lt (y,x)))

theorem splice_perm (xs : List X) (x : X) : splice lt xs x ~ x::xs :=
  List.perm_middle.trans ((List.filter_append_perm (fun y => lt (y,x)) xs).cons x)

/-- Insertion sort (copy of OAI `SyntaxSort.arrange`). -/
def arrange (xs : List X) : List X := xs.foldl (splice lt) []

theorem fold_perm (xs acc : List X) : xs.foldl (splice lt) acc ~ acc++xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    exact (ih (splice lt acc x)).trans (((splice_perm lt acc x).append_right xs).trans List.perm_middle.symm)

theorem arrange_perm (xs : List X) : arrange lt xs ~ xs := by
  unfold arrange
  simpa using fold_perm lt xs []

/-- Copy of OAI `SyntaxSort.arrange_poly`. -/
theorem arrange_poly [Codec X] [Inhabited X] (p : Poly lt) : Poly (arrange lt) := by
  have part (test : X × X → Bool) (hp : Poly test) :
      Poly (fun q : List X × X => q.1.filter fun y => test (y,q.2)) := by
    have row : Poly (fun q : X × X => bif test q.swap then [q.2] else []) :=
      Poly.choose (Easy.exchange.poly.compose hp) (by fun_prop) (Code.Poly.const ([] : List X))
    have take := (Easy.exchange.poly.compose (Poly.push default default row)).compose Easy.flatten.poly
    convert take using 1
    funext q
    rcases q with ⟨xs,x⟩
    induction xs with
    | nil => rfl
    | cons y xs ih =>
      change (y::xs).filter _ = (bif test (y,x) then [y] else []) ++ _
      cases eq : test (y,x) <;> simpa [List.filter,eq,polyPush] using
        congrArg (fun t => (bif test (y,x) then [y] else []) ++ t) ih
  have hp : Poly (fun q : List X × X => splice lt q.1 q.2) :=
    (part lt p).app ((Easy.snd.poly.pair (part _ (p.compose Iter.negate.poly))).compose Easy.cons.poly)
  have loop := Poly.fold_left hp 1 1 (fun ⟨xs,acc⟩ l h => ?_)
  exact (Poly.identity.pair (Code.Poly.const ([] : List X))).compose loop
  have perm := fold_perm lt l acc
  have eqsize {a b : List X} (pm : a~b) : size a=size b := by
    induction pm with
    | nil => rfl
    | cons _ _ ih => simp [ih]
    | swap => simp; omega
    | trans _ _ ih ij => exact ih.trans ij
  have e := size_append_right acc l
  obtain ⟨rest,hr⟩ := h
  change l++rest=xs at hr
  have b := size_append_right l rest
  rw [hr] at b
  have ge : 0 < size rest := Nat.zero_lt_of_lt (duration _)
  change size (l.foldl (splice lt) acc) ≤ 1*(size xs+size acc+1+1)^1
  rw [eqsize perm,pow_one,one_mul]
  omega

variable {lt} {κ : X → ℕ}

theorem splice_sorted (hlt : ∀ y x, lt (y,x) = decide (κ y < κ x)) {xs : List X}
    (h : xs.Pairwise (fun a b => κ a ≤ κ b)) (x : X) :
    (splice lt xs x).Pairwise (fun a b => κ a ≤ κ b) := by
  unfold splice
  apply List.pairwise_append.mpr
  refine ⟨h.filter _, List.pairwise_cons.mpr ⟨?_, h.filter _⟩, ?_⟩
  · intro y hy
    have hy' := (List.mem_filter.mp hy).2
    rw [hlt] at hy'
    simp at hy'
    omega
  · intro y hy z hz
    have low := (List.mem_filter.mp hy).2
    rw [hlt] at low
    simp at low
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · have hz' := (List.mem_filter.mp hz).2
      rw [hlt] at hz'
      simp at hz'
      omega

theorem arrange_sorted (hlt : ∀ y x, lt (y,x) = decide (κ y < κ x)) (xs : List X) :
    (arrange lt xs).Pairwise (fun a b => κ a ≤ κ b) := by
  have go : ∀ (ys acc : List X), acc.Pairwise (fun a b => κ a ≤ κ b) →
      (ys.foldl (splice lt) acc).Pairwise (fun a b => κ a ≤ κ b) := by
    intro ys
    induction ys with
    | nil => intro acc h; exact h
    | cons y ys ih => intro acc h; exact ih _ (splice_sorted hlt h y)
  exact go xs [] List.Pairwise.nil

end Arrange

/-! ## Binary values and the comparators -/

theorem bval_eq_value (l : List Bool) : bval l = Bits.value l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bval, Bits.value_cons, ih]

/-- A tagged request: (tag = tally of its index, request). -/
abbrev TReq := Tally × Req

/-- Address comparator: the borrow of `Bits.sub` (true iff the first address is smaller). -/
def ltA (p : TReq × TReq) : Bool := (Bits.sub (p.1.2.1, p.2.2.1)).2

theorem ltA_eq (y x : TReq) : ltA (y, x) = decide (bval y.2.1 < bval x.2.1) := by
  rw [bval_eq_value, bval_eq_value, Bool.eq_iff_iff, decide_eq_true_iff]
  exact Bits.sub_borrow _ _

theorem easy_ltA : Easy ltA := by
  unfold ltA
  fun_prop

/-- A record: (tag, fetched field). -/
abbrev Rec := Tally × List Bool

/-- Tag comparator (true iff the first tag is shorter). -/
def ltT (p : Rec × Rec) : Bool := Iter.small (p.1.1, p.2.1)

theorem ltT_eq (y x : Rec) : ltT (y, x) = decide (y.1.length < x.1.length) := rfl

theorem easy_ltT : Easy ltT := by
  unfold ltT
  fun_prop

end P1Batch
