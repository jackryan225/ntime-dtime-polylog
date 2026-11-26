import P1SolF0R.AccessRows
import OAI.Computability.IntegerMultiplication.Carry.Square
import P1P5.KWRefresh

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1Wit P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

/-- Euclidean division of a signed start code. The quotient is a difference of naturals. -/
def startParts (p : ℕ × ℕ) : (ℕ × ℕ) × ℕ :=
  let q := p.2 / 2 / p.1
  let r := p.2 / 2 % p.1
  bif decide (p.2 % 2 = 0) then ((q, 0), r) else ((0, q + 1), p.1 - 1 - r)

theorem startParts_poly : Poly startParts := by
  unfold startParts
  fun_prop

theorem startParts_eq (N raw : ℕ) (hN : 0 < N) :
    let p := startParts (N, raw)
    (unzigzag raw / (N : ℤ) = (p.1.1 : ℤ) - (p.1.2 : ℤ)) ∧
      (unzigzag raw % (N : ℤ) = (p.2 : ℤ)) := by
  let p := startParts (N, raw)
  let q := raw / 2 / N
  let r := raw / 2 % N
  have hr : r < N := Nat.mod_lt _ hN
  have hd : (raw / 2 : ℕ) = r + N * q := (Nat.mod_add_div (raw / 2) N).symm
  have hdecomp : unzigzag raw = ((p.1.1 : ℤ) - (p.1.2 : ℤ)) * (N : ℤ) + (p.2 : ℤ) ∧ p.2 < N := by
    by_cases hv : raw % 2 = 0
    · simp only [p, unzigzag, startParts, hv, decide_true, Bool.cond_true, ite_true, Prod.fst, Prod.snd]
      change (((raw / 2 : ℕ) : ℤ) = ((q : ℤ) - 0) * (N : ℤ) + r) ∧ r < N
      constructor
      · rw [hd]
        push_cast
        ring
      · exact hr
    · have hsub : r ≤ N - 1 := by omega
      have hv' : Int.negSucc (raw / 2) = - ((raw / 2 : ℕ) : ℤ) - 1 := by omega
      simp only [p, startParts, unzigzag, hv, decide_false, Bool.cond_false, ite_false]
      change (Int.negSucc (raw / 2) = (0 - ((q + 1 : ℕ) : ℤ)) * (N : ℤ) + ((N - 1 - r : ℕ) : ℤ)) ∧
        N - 1 - r < N
      rw [hv', hd, Int.ofNat_sub hsub, Int.ofNat_sub hN, Nat.cast_add, Nat.cast_mul, Nat.cast_add]
      constructor
      · push_cast
        ring
      · omega
  obtain ⟨hnum, hrange⟩ := hdecomp
  have hdv : unzigzag raw / (N : ℤ) = (p.1.1 : ℤ) - (p.1.2 : ℤ) := by
    apply ediv_eq_of_bounds (by exact_mod_cast hN)
    · rw [hnum]
      omega
    · rw [hnum]
      have hp : (p.2 : ℤ) < (N : ℤ) := by exact_mod_cast hrange
      omega
  refine ⟨hdv, ?_⟩
  have hh := Int.ediv_mul_add_emod (unzigzag raw) (N : ℤ)
  rw [hdv] at hh
  change unzigzag raw % (N : ℤ) = (p.2 : ℤ)
  exact add_left_cancel (hh.trans hnum)

private def sumStep (p : Unit × Bits.Word × Bits.Word) : Bits.Word :=
  Bits.add (p.2.1, p.2.2)

private def sumWords (xs : List Bits.Word) : Bits.Word :=
  Carry.trek sumStep (xs, (), [])

private theorem sumWords_poly : Poly sumWords := by
  have hStep : Poly sumStep := by unfold sumStep; fun_prop
  have hCount := Carry.polyTrek sumStep hStep 3 (by
    intro z acc w
    simp only [sumStep, P1ChkFinal.size_listBool, Bits.add_length]
    omega)
  exact (show Poly (fun xs : List Bits.Word => (xs, (), ([] : Bits.Word))) from by fun_prop).compose hCount

private theorem value_sumWords (xs : List Bits.Word) :
    Bits.value (sumWords xs) = (xs.map Bits.value).sum := by
  have H (ys : List Bits.Word) (acc : Bits.Word) :
      Bits.value (Carry.trek sumStep (ys, (), acc)) =
        Bits.value acc + (ys.map Bits.value).sum := by
    induction ys generalizing acc with
    | nil => rfl
    | cons y ys ih =>
      change Bits.value (Carry.trek sumStep (ys, (), Bits.add (acc, y))) =
        Bits.value acc + ((y :: ys).map Bits.value).sum
      rw [ih, Bits.add_val, List.map_cons, List.sum_cons, Nat.add_assoc]
  simp only [sumWords, H, Bits.value_nil, Nat.zero_add]

private theorem sumNat_poly : Poly (List.sum : List ℕ → ℕ) := by
  have hbits : Poly (List.map binary : List ℕ → List (List Bool)) :=
    Poly.maps _ (poly_binary Poly.identity)
  have hsum := hbits.compose sumWords_poly
  have h := poly_bval hsum
  convert h using 1
  funext xs
  simp only [bval_eq_value, value_sumWords, List.map_map, Function.comp_def,
    value_binary]
  rw [show (fun x : ℕ => x) = id from rfl, List.map_id]

/-- The numeric centers of all lanes, computed from the slice of interval moves and the start remainder. -/
def centerValues (p : List ℕ × ℕ) : List ℕ :=
  (List.range p.1.length).map fun j => center p.1.length p.2 p.1 j

theorem centerValues_poly : Poly centerValues := by
  have ht : Poly (fun p : (List ℕ × ℕ) × ℕ => p.1.1.take p.2) :=
    P1ProgEng.SolKWR.poly_take Easy.snd.poly (by fun_prop)
  have hs := ht.compose sumNat_poly
  have hval : Poly (fun p : (List ℕ × ℕ) × ℕ => center p.1.1.length p.1.2 p.1.1 p.2) := by
    unfold center
    fun_prop
  exact poly_mapWith (Easy.fst.poly.compose range_length_poly) hval

theorem centerValues_genuine {K : Type} {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)
    (raw : ℕ) (hraw : raw = zigzag (betaOf σ k (ι.val * 2 ^ h))) :
    centerValues (intervalMoves σ ι k, (startParts (2 ^ h, raw)).2) = trueCenters σ ι k := by
  subst raw
  have hs := (startParts_eq (2 ^ h) (zigzag (betaOf σ k (ι.val * 2 ^ h))) (Nat.two_pow_pos h)).2
  rw [unzigzag_zigzag] at hs
  have he := congrArg Int.toNat hs
  simp only [Int.toNat_natCast] at he
  unfold centerValues trueCenters
  simp only [intervalMoves, List.length_ofFn, ← he]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intros
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.startParts_eq
#print axioms P1SolF0R.SolReader.centerValues_genuine
