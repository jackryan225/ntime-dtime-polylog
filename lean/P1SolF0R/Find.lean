import P1ChkFinal.C10RcPoly
import P1SolC10P.Primitives
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open scoped P1ChkFinal.AstraC10

/-- A first-match scan using polynomial work on a supplied finite list of candidates. -/
def firstMatch {A X : Type} (test : A × X → Bool) (p : A × List X) : Option X :=
  p.2.find? (fun x => test (p.1, x))

private theorem firstMatch_tagged {X : Type} (test : X → Bool) (xs : List X) :
    ((xs.map (fun x => (x, test x))).filter Prod.snd).head?.map Prod.fst = xs.find? test := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : test x <;> simp [hx, Function.comp_def]

theorem firstMatch_poly {A X : Type} [Codec A] [Codec X] (a : A) (x : X)
    {test : A × X → Bool} (h : Poly test) : Poly (firstMatch test) := by
  have ht : Poly (fun p : A × X => (p.2, test p)) := Easy.snd.poly.pair h
  let tagged : A × List X → List (X × Bool) := polyPush (fun p : A × X => (p.2, test p))
  have hp : Poly tagged := Poly.push a x ht
  have hf : Poly (fun p => (tagged p).filter Prod.snd) := hp.compose (Poly.filter _ Easy.snd.poly)
  have hm : Poly (fun p => ((tagged p).filter Prod.snd).map (fun t => some t.1)) :=
    hf.compose (Poly.maps _ (Easy.fst.poly.compose Easy.some.poly))
  have ho := hm.compose (Iter.leader (none : Option X)).poly
  convert ho using 1
  funext p
  unfold firstMatch tagged polyPush
  rw [← firstMatch_tagged]
  cases ((p.2.map fun x => (x, test (p.1, x))).filter Prod.snd) <;> rfl

/-- Selecting the first passing index of a range gives its least passing index. -/
theorem range_find_eq_some {n j : ℕ} {test : ℕ → Bool} :
    (List.range n).find? test = some j ↔
      j < n ∧ test j = true ∧ ∀ i < j, test i = false := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hj, i, hi, hget, hearly⟩
    have hij : i = j := by simpa only [List.getElem_range] using hget
    subst i
    refine ⟨by simpa only [List.length_range] using hi, hj, ?_⟩
    intro i hi
    have h := hearly i hi
    simpa only [List.getElem_range, Bool.not_eq_true'] using h
  · rintro ⟨hj, ht, hmin⟩
    refine ⟨ht, j, by simpa only [List.length_range], by simp only [List.getElem_range], ?_⟩
    intro i hi
    simp only [List.getElem_range, hmin i hi, Bool.not_false]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.firstMatch_poly
