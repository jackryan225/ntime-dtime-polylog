import P1Net.AccessPerm
import P1Wit.Decode

namespace P1SolF0R.SolReader

open P1Net

variable {K : Type} {n : ℕ}

/-- The starting block at relative time j follows from a single start record and j local trits. -/
theorem betaOf_local (σ : Fin n → K → Fin 3) (k : K) (base : ℕ) (moves : List ℕ)
    (hfit : base + moves.length ≤ n)
    (hmoves : ∀ j (hj : j < moves.length), moves[j] = (σ ⟨base + j, by omega⟩ k).val)
    (j : ℕ) (hj : j ≤ moves.length) :
    betaOf σ k (base + j) = betaOf σ k base + ((moves.take j).sum : ℤ) - j := by
  induction j with
  | zero => simp only [Nat.add_zero, List.take_zero, List.sum_nil, Int.cast_ofNat_Int, add_zero, sub_zero]
  | succ j ih =>
    have hlt : j < moves.length := by omega
    have hidx : base + j < n := by omega
    rw [Nat.add_succ, betaOf, dif_pos hidx, ih (by omega), List.take_succ_eq_append_getElem hlt,
      List.sum_append, List.sum_singleton, hmoves j hlt, Nat.cast_add, Nat.cast_succ]
    ring

section Interval

variable {I h : ℕ} (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

def intervalMoves : List ℕ := List.ofFn fun j : Fin (2 ^ h) =>
  (σ ⟨ι.val * 2 ^ h + j.val, by
    calc
      _ < ι.val * 2 ^ h + 2 ^ h := Nat.add_lt_add_left j.isLt _
      _ = (ι.val + 1) * 2 ^ h := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ I * 2 ^ h := Nat.mul_le_mul_right _ ι.isLt⟩ k).val

/-- The numeric coordinate of the head block relative to the first owned port block. -/
def center (N start : ℕ) (moves : List ℕ) (j : ℕ) : ℕ :=
  start + N + (moves.take j).sum - j

theorem center_eq (j : Fin (2 ^ h)) :
    (center (2 ^ h) ((betaOf σ k (ι.val * 2 ^ h)) % (2 ^ h : ℕ)).toNat
      (intervalMoves σ ι k) j.val : ℤ) =
      laneBeta I σ ι k j.val - (bigQ I σ k ι - 1) * (2 ^ h : ℕ) := by
  let N := 2 ^ h
  let base := ι.val * N
  let b := betaOf σ k base
  let rest := b % (N : ℤ)
  have hN : 0 < N := Nat.two_pow_pos _
  have hnz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr : 0 ≤ rest := Int.emod_nonneg _ hnz
  have hsum := betaOf_local σ k base (intervalMoves σ ι k)
    (by
      simp only [intervalMoves, List.length_ofFn, base]
      change ι.val * N + N ≤ I * N
      calc
        _ = (ι.val + 1) * N := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ I * N := Nat.mul_le_mul_right N ι.isLt)
    (fun j hj => by
      simp only [intervalMoves, List.getElem_ofFn, base, N])
    j.val (by simpa only [intervalMoves, List.length_ofFn] using j.isLt.le)
  have hnonneg : j.val ≤ rest.toNat + N + ((intervalMoves σ ι k).take j.val).sum := by
    have hj : j.val < N := j.isLt
    omega
  change (center N rest.toNat (intervalMoves σ ι k) j.val : ℤ) =
    betaOf σ k (base + j.val) - (b / (N : ℤ) - 1) * (N : ℤ)
  unfold center
  rw [Int.ofNat_sub hnonneg, Nat.cast_add, Nat.cast_add, Int.toNat_of_nonneg hr, hsum]
  have hdiv := Int.ediv_mul_add_emod b (N : ℤ)
  change b / (N : ℤ) * (N : ℤ) + rest = b at hdiv
  linarith [hdiv]

end Interval

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.center_eq
