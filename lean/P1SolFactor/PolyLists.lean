import P1SolFactor.PolyWords
import OAI.Computability.IntegerMultiplication.Code.Decompose

namespace P1SolFactor.SolPolyWords

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code

def andB (p : Bool × Bool) : Bool := p.1 && p.2

def eqB (p : Bool × Bool) : Bool := p.1 == p.2

@[fun_prop] theorem andB_poly : Poly andB := (Easy.finite _).poly
@[fun_prop] theorem eqB_poly : Poly eqB := (Easy.finite _).poly

def allBits (xs : List Bool) : Bool := xs.all id

theorem allBits_true (xs : List Bool) : allBits xs = true ↔ ∀ b ∈ xs, b = true := by
  simp only [allBits, List.all_eq_true, id_eq]

@[fun_prop] theorem allBits_poly : Poly allBits := by
  have h := Code.Poly.fold_left (f := andB) andB_poly 1 0 (by
    intro s l hl
    simp only [size_bit, pow_zero, Nat.mul_one, le_refl])
  have hfold (xs : List Bool) (b : Bool) :
      xs.foldl (fun a c => andB (a, c)) b = (b && allBits xs) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp only [andB, allBits, List.all_cons, id_eq, Bool.and_assoc]
  simpa only [hfold, Bool.true_and] using
    ((Code.Poly.identity (X := List Bool)).pair (Code.Poly.const true)).compose h

@[fun_prop] theorem fill_poly {X : Type} [Codec X] (x : X) : Poly (fill x) :=
  (easy_fill x Easy.identity).poly

@[fun_prop] theorem flatten_poly {X : Type} [Codec X] : Poly (List.flatten : List (List X) → List X) :=
  Easy.flatten.poly

def takeT {X : Type} (p : Tally × List X) : List X := (cutLists p).1

def dropT {X : Type} (p : Tally × List X) : List X := (cutLists p).2

@[fun_prop] theorem takeT_poly {X : Type} [Codec X] : Poly (takeT (X := X)) := cut_poly.fstCompose
@[fun_prop] theorem dropT_poly {X : Type} [Codec X] : Poly (dropT (X := X)) := cut_poly.sndCompose

@[simp] theorem takeT_tally {X : Type} (n : ℕ) (xs : List X) :
    takeT (tally n, xs) = xs.take n := by simp [takeT, cutLists]

@[simp] theorem dropT_tally {X : Type} (n : ℕ) (xs : List X) :
    dropT (tally n, xs) = xs.drop n := by simp [dropT, cutLists]

def mulT (p : Tally × Tally) : Tally := (polyPush (fun x : Tally × Unit => x.1) p).flatten

@[fun_prop] theorem mulT_poly : Poly mulT :=
  (Code.Poly.push [] () Easy.fst.poly).compose flatten_poly

@[simp] theorem mulT_tally (m n : ℕ) : mulT (tally m, tally n) = tally (m * n) := by
  have h (xs : Tally) : (xs.map fun _ => tally m).flatten = tally (m * xs.length) := by
    induction xs with
    | nil => simp [tally]
    | cons a xs ih =>
      simp only [List.map_cons, List.flatten_cons, ih, List.length_cons, Nat.mul_succ]
      change List.replicate m () ++ List.replicate (m * xs.length) () =
        List.replicate (m * xs.length + m) ()
      rw [List.replicate_append_replicate, Nat.add_comm m]
  simpa only [mulT, polyPush, tally_length] using h (tally n)

def divConst (d : ℕ) (p : Tally) : Tally :=
  if h : 2 ≤ d then (catalog d h p).1 else if d = 1 then p else []

@[fun_prop] theorem divConst_poly (d : ℕ) : Poly (divConst d) := by
  unfold divConst
  split
  · rename_i h
    exact (easy_catalog d h).poly.fstCompose
  · split
    · exact Code.Poly.identity
    · exact Code.Poly.const _

@[simp] theorem divConst_tally (d n : ℕ) : divConst d (tally n) = tally (n / d) := by
  unfold divConst
  by_cases h : 2 ≤ d
  · rw [dite_eq_left h]
    have hq := len_catalog d h (tally n)
    have hr := (catalog d h (tally n)).2.isLt
    rw [tally_length] at hq
    conv_rhs => rw [hq]
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    exact (recover_tally _).symm
  · rw [dite_eq_right h]
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · simp [tally]
    · simp only [↓reduceIte, Nat.div_one]

def atWidth {X : Type} (c : X) (p : Tally × List X) : List X :=
  polyPush (Iter.pick c) (p.2, Iter.lineup p.1)

@[fun_prop] theorem atWidth_poly {X : Type} [Codec X] (c : X) : Poly (atWidth c) := by
  unfold atWidth
  exact ((by fun_prop : Poly (fun p : Tally × List X => (p.2, Iter.lineup p.1)))).compose
    (Code.Poly.push [] [] (pick_poly c))

@[simp] theorem atWidth_tally {X : Type} (c : X) (n : ℕ) (xs : List X) :
    atWidth c (tally n, xs) = List.ofFn (fun i : Fin n => xs.getD i.val c) := by
  simp only [atWidth, polyPush, Iter.lined, List.map_ofFn, Function.comp_def, pick_getD]

def bitsMatchAt (p : (List Bool × List Bool) × Tally) : Bool :=
  eqB (Iter.pick false (p.1.1, p.2), Iter.pick false (p.1.2, p.2))

@[fun_prop] theorem bitsMatchAt_poly : Poly bitsMatchAt := by unfold bitsMatchAt; fun_prop

def paddedEq (p : List Bool × List Bool) : Bool :=
  allBits (polyPush bitsMatchAt (p, Iter.lineup (ruler p.1 ++ ruler p.2)))

@[fun_prop] theorem paddedEq_poly : Poly paddedEq := by
  unfold paddedEq
  have h : Poly (fun p : List Bool × List Bool => (p, Iter.lineup (ruler p.1 ++ ruler p.2))) := by
    fun_prop
  exact (h.compose (Code.Poly.push ([], []) [] bitsMatchAt_poly)).compose allBits_poly

theorem paddedEq_true (xs ys : List Bool) :
    paddedEq (xs, ys) = true ↔ ∀ i, xs.getD i false = ys.getD i false := by
  have h : ruler xs ++ ruler ys = tally (xs.length + ys.length) := by
    rw [← recover_tally (ruler xs ++ ruler ys), List.length_append, ruler_length, ruler_length]
  unfold paddedEq
  rw [h, allBits_true]
  simp only [polyPush, Iter.lined, List.map_ofFn, Function.comp_def]
  constructor
  · intro h i
    by_cases hi : i < xs.length + ys.length
    · have hb := h _ (List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩)
      simpa only [bitsMatchAt, pick_getD, eqB, beq_iff_eq] using hb
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro h b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    simp only [bitsMatchAt, pick_getD, eqB, beq_iff_eq]
    exact h i.val

def exactEq (p : List Bool × List Bool) : Bool :=
  andB (eqT (ruler p.1, ruler p.2), paddedEq p)

@[fun_prop] theorem exactEq_poly : Poly exactEq := by unfold exactEq; fun_prop

theorem exactEq_true (xs ys : List Bool) : exactEq (xs, ys) = true ↔ xs = ys := by
  simp only [exactEq, andB, Bool.and_eq_true, eqT, ruler_length, decide_eq_true_eq, paddedEq_true]
  refine ⟨fun ⟨hl, h⟩ => List.ext_getElem hl (fun i hx hy => ?_), fun h => by subst ys; exact ⟨rfl, fun _ => rfl⟩⟩
  simpa only [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy] using h i

end P1SolFactor.SolPolyWords
