import P1SolFinal.Prepare
import OAI.Computability.IntegerMultiplication.Code.Loop

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

def mulStep (a x : Word) (b : Bool) : Word :=
  Bits.add (false :: x, bif b then a else [])

def multiply (p : Req) : Word :=
  p.2.reverse.foldl (mulStep p.1) []

theorem multiply_value (a b : Word) : Bits.value (multiply (a, b)) = Bits.value a * Bits.value b := by
  induction b with
  | nil => simp only [multiply, List.reverse_nil, List.foldl_nil, Bits.value_nil, Nat.mul_zero]
  | cons bit b ih =>
    simp only [multiply, List.reverse_cons, List.foldl_append]

    change Bits.value (mulStep a (multiply (a, b)) bit) = _
    simp only [mulStep, Bits.add_val, Bits.value_cons, Bits.d0, Nat.zero_add, ih]
    cases bit <;> simp only [Bits.d0, Bits.d1, Nat.zero_add, Bool.cond_false, Bool.cond_true, Bits.value_nil,
      Nat.add_zero] <;> ring

theorem mulStep_length (a x : Word) (b : Bool) : (mulStep a x b).length ≤ x.length + a.length + 2 := by
  cases b <;> simp only [mulStep, Bits.add_length, List.length_cons, List.length_nil,
    Bool.cond_true, Bool.cond_false] <;> omega

theorem mulFold_length (a z : Word) (s : Word) :
    (s.foldl (mulStep a) z).length ≤ z.length + s.length * (a.length + 2) := by
  induction s generalizing z with
  | nil => simp only [List.length_nil, List.foldl_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b s ih =>
    have h₁ := ih (mulStep a z b)
    have h₂ := mulStep_length a z b
    simp only [List.foldl_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

set_option maxHeartbeats 1000000 in
theorem poly_multiply : Poly multiply := by
  let step : (Word × Word) × Bool → Word × Word := fun s =>
    (mulStep s.1.2 s.1.1 s.2, s.1.2)
  have ep : Easy step := by
    unfold step mulStep
    fun_prop
  have H := Poly.fold_left ep.poly 8 2 (fun i l hl => ?_)
  · let inp : Req → Word × (Word × Word) := fun i => (i.2.reverse, [], i.1)
    have ei : Easy inp := by unfold inp; fun_prop
    have hs (a z : Word) (l : Word) :
        l.foldl (fun s b => step (s, b)) (z, a) = (l.foldl (mulStep a) z, a) := by
      induction l generalizing z with
      | nil => rfl
      | cons b l ih => exact ih (mulStep a z b)
    have hv (i : Req) :
        ((inp i).1.foldl (fun s b => step (s, b)) (inp i).2).1 = multiply i := by
      rw [show (inp i).1 = i.2.reverse from rfl, show (inp i).2 = ([], i.1) from rfl, hs]
      rfl
    simpa only [hv] using (ei.poly.compose H).fstCompose
  · rcases i with ⟨s, z, a⟩
    have foldParts : l.foldl (fun x b => step (x, b)) (z, a) = (l.foldl (mulStep a) z, a) := by
      clear hl s
      induction l generalizing z with
      | nil => rfl
      | cons b l ih => exact ih (mulStep a z b)
    rw [foldParts]
    let N := size (s, z, a) + 1
    have hs : s.length ≤ N := by simp only [N, size_prod, size_listBool]; omega
    have hz : z.length ≤ N := by simp only [N, size_prod, size_listBool]; omega
    have ha : a.length + 2 ≤ N := by simp only [N, size_prod, size_listBool]; omega
    have hN : N ≤ N * N := by
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hmul := Nat.mul_le_mul (hl.length_le.trans hs) ha
    have hlen := mulFold_length a z l
    change size (l.foldl (mulStep a) z, a) ≤ 8 * N ^ 2
    simp only [size_prod, size_listBool, pow_two]
    omega

end P1ChkFinal.SolFinal
