import P1SolCone.FieldCache
import P1SolCone.ProgramLevel
import P1SolCone.ConeBatchInput
import P1SolFmt.Offsets

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1ProgEng.SolKWR
open scoped P1ChkFinal.AstraC10

open private sumWords sumWords_poly value_sumWords from P1SolFmt.Offsets

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

theorem bitsVal_eq_batch (w : List Bool) : bitsVal w = P1Batch.bval w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp only [bitsVal, P1Batch.bval, ih] <;> rfl

@[fun_prop] theorem poly_bitsVal {X : Type} [Codec X] {f : X → List Bool} (hf : Poly f) :
    Poly (fun x => bitsVal (f x)) := by
  simpa only [bitsVal_eq_batch] using poly_bval hf

theorem fieldCache_poly : Poly (fun p : List FieldKey × List (List Bool) => fieldCache p.1 p.2) := by
  have vals : Poly (fun p : List FieldKey × List (List Bool) => p.2.map bitsVal) :=
    Easy.snd.poly.compose (Poly.maps bitsVal (poly_bitsVal Code.Poly.identity))
  exact (Easy.fst.poly.pair vals).compose poly_zipLists

private theorem iter_pick_eq_getD {A : Type} (d : A) (xs : List A) (i : ℕ) :
    Iter.pick d (xs, tally i) = xs.getD i d := by
  simp only [Iter.pick, tally_length]
  induction i generalizing xs with
  | zero => cases xs <;> rfl
  | succ i ih =>
    cases xs with
    | nil => rfl
    | cons a as => exact ih _

theorem fieldCache_read_index (c : FieldCache) (key : FieldKey) :
    (c.map Prod.snd).getD ((c.map Prod.fst).idxOf key) 0 = c.read key := by
  induction c with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p.1 = key
    · simp [List.map_cons, h, FieldCache.read, List.find?_cons]
    · simp only [List.map_cons, List.idxOf_cons_ne _ h, List.getD_cons_succ, FieldCache.read,
        List.find?_cons, show (p.1 == key) = false from beq_eq_false_iff_ne.mpr h] at ih ⊢
      exact ih

/-- Lookup in the small batch table by its P6 section/index pair. -/
theorem fieldCache_read_poly : Poly (fun p : FieldCache × FieldKey => p.1.read p.2) := by
  have keys : Poly (fun p : FieldCache × FieldKey => p.1.map Prod.fst) :=
    Easy.fst.poly.compose (Poly.maps _ Easy.fst.poly)
  have vals : Poly (fun p : FieldCache × FieldKey => p.1.map Prod.snd) :=
    Easy.fst.poly.compose (Poly.maps _ Easy.snd.poly)
  have ix := (keys.pair Easy.snd.poly).compose (poly_indexTally poly_eqPosition)
  simpa only [iter_pick_eq_getD, fieldCache_read_index] using
    (vals.pair ix).compose (Iter.facile (0 : ℕ)).poly

/-- Numerically encoded offset, width and index to a batch request. -/
def numericFieldReq (p : ℕ × ℕ × ℕ) : P1Batch.Req :=
  (bin (p.1 + p.2.2 * p.2.1), bin p.2.1)

theorem numericFieldReq_poly : Poly numericFieldReq := by
  unfold numericFieldReq
  fun_prop

theorem numericFieldReq_eq (D : Dims) (s i : ℕ) :
    numericFieldReq (D.off s, D.width s, i) = fieldReq D s i := rfl

/-- Enumerate an axis only up to the size of an explicitly available tally. -/
def capRange (p : Tally × ℕ) : List ℕ := List.range (min p.2 p.1.length)

theorem capRange_poly : Poly capRange := by
  have ht := poly_tallyCap 1 (Easy.snd.poly : Poly (Prod.snd : Tally × ℕ → ℕ))
    (Easy.fst.poly : Poly (Prod.fst : Tally × ℕ → Tally))
  have h := (ht.compose Iter.poly_line).compose
    (Poly.maps List.length (poly_lengthNat (Code.Poly.identity (X := Tally))))
  convert h using 1
  funext p
  simp only [capRange, Nat.one_mul, Iter.lined, List.map_ofFn, Function.comp_def, tally_length]
  apply List.ext_getElem
  · simp only [List.length_range, List.length_ofFn]
  · intros
    simp only [List.getElem_range, List.getElem_ofFn]

theorem sumNats_poly : Poly (List.sum (α := ℕ)) := by
  have hb : Poly (fun n : ℕ => binary n) := Code.Poly.identity (X := ℕ)
  have h := (Poly.maps _ hb).compose sumWords_poly
  simpa [bval_eq_value, value_sumWords, List.map_map, Function.comp_def, value_binary] using
    poly_bval h

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.fieldCache_read_poly
