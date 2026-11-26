import P1OaiReuse.Entry

/-!
# P1OaiReuse.Plan: sums of products of ring letters are polynomial-time (generic part of `planEval` in Poly form)

Owner: P1-lean-oaireuse. Row 2 of `research/p1/lean/OaiReuse/SPIKE-TABLE.md`.

`P1P5.planValue f pl = (pl.map fun tm => (tm.map (evalReq f)).prod).sum` (P5/P1P5/KernelPlan.lean:65). Here: for ANY
request code `X` and ANY polynomial-time request evaluator `v : X → Label R` (for example `P1OaiReuse.entry_poly`),
the plan evaluator `planVal v : List (List X) → Label R` is `Code.Poly`, and its value is the sum over the terms of the
products of the request values (`planVal_val`).
-/

namespace P1OaiReuse

open OAI.Computability OAI.Computability.MultitapeWeakETH
open IntegerMultiplication Code StackInterpreter

noncomputable section

variable {R : Type} [CommRing R] [Fintype R]

/-- Sum of two ring letters. -/
def addL (p : Label R × Label R) : Label R := ⟨p.1.val + p.2.val⟩

/-- Sum of a list of ring letters (a left fold from `0`). -/
def sumL (l : List (Label R)) : Label R := l.foldl (fun x y => addL (x, y)) ⟨0⟩

theorem foldl_addL (l : List (Label R)) (c : Label R) :
    (l.foldl (fun x y => addL (x, y)) c).val = c.val + (l.map Label.val).sum := by
  induction l generalizing c with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons y l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    simp only [addL, add_assoc]

theorem sumL_val (l : List (Label R)) : (sumL l).val = (l.map Label.val).sum := by
  rw [sumL, foldl_addL]
  exact zero_add _

theorem sumL_poly : Poly (sumL (R := R)) := by
  have hf : Poly (addL (R := R)) := (Easy.finite _).poly
  have hfold := Poly.fold_left (f := addL (R := R)) hf (2 * Fintype.card R + 1) 0
    (fun s l _ => by
      rw [pow_zero, Nat.mul_one]
      exact label_size (l.foldl (fun x y => addL (x, y)) s.2).val)
  exact (Poly.identity.pair (Code.Poly.const (⟨0⟩ : Label R))).compose hfold

/-- Value of a plan: the sum over the terms of the product of the values of the requests. -/
def planVal {X : Type} (v : X → Label R) (pl : List (List X)) : Label R :=
  sumL (pl.map fun tm => prodL (tm.map v))

/-- **Plans are polynomial-time**, for any polynomial-time request evaluator. -/
theorem planVal_poly {X : Type} [Codec X] {v : X → Label R} (hv : Poly v) : Poly (planVal v) :=
  (Poly.maps _ ((Poly.maps v hv).compose prodL_poly)).compose sumL_poly

theorem planVal_val {X : Type} (v : X → Label R) (pl : List (List X)) :
    (planVal v pl).val = (pl.map fun tm => (tm.map fun x => (v x).val).prod).sum := by
  rw [planVal, sumL_val, List.map_map]
  congr 1
  refine List.map_congr_left (fun tm _ => ?_)
  show (prodL (tm.map v)).val = (tm.map fun x => (v x).val).prod
  rw [prodL_val, List.map_map, Function.comp_def]

/-- A tagged request of two kinds (OpenAI's calculus has no case combinator for `Sum`, so a request carries a Boolean
tag and BOTH inputs, with a dummy in the unused place): `false` = first kind with input `q.2.1`, `true` = second
kind with input `q.2.2`. -/
def tagVal {X Y : Type} (v : X → Label R) (w : Y → Label R) (q : Bool × X × Y) : Label R :=
  bif q.1 then w q.2.2 else v q.2.1

theorem tagVal_poly {X Y : Type} [Codec X] [Codec Y] {v : X → Label R} {w : Y → Label R}
    (hv : Poly v) (hw : Poly w) : Poly (tagVal v w) :=
  Poly.choose (Easy.fst (X := Bool) (Y := X × Y)).poly
    (((Easy.snd (X := Bool) (Y := X × Y)).poly.compose (Easy.snd (X := X) (Y := Y)).poly).compose hw)
    (((Easy.snd (X := Bool) (Y := X × Y)).poly.compose (Easy.fst (X := X) (Y := Y)).poly).compose hv)

theorem tagVal_false {X Y : Type} (v : X → Label R) (w : Y → Label R) (x : X) (y : Y) :
    tagVal v w (false, x, y) = v x := rfl

theorem tagVal_true {X Y : Type} (v : X → Label R) (w : Y → Label R) (x : X) (y : Y) :
    tagVal v w (true, x, y) = w y := rfl

end

end P1OaiReuse
