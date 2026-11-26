import P1P5.Factor0Target
import P1ChkDir.C4
import P1ChkFinal.C10RcPoly
import P1SolC10SA.Primitives

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1ChkFinal.AstraC10
open scoped Classical P1ChkFinal.AstraC10

/-- The untwinned location number, the big interval, and the twin flag. -/
abbrev BaseCode := (ℕ × ℕ) × Bool

def baseCode (count address : ℕ) : BaseCode :=
  ((address / 2 % count, address / 2 / count), decide (address % 2 = 1))

theorem address_poly : Poly (fun p : ℕ × ℕ => baseCode p.1 p.2) := by
  unfold baseCode
  have h : Poly (fun p : ℕ × ℕ => p.2 % 2) := by fun_prop
  have e : Poly (fun p : ℕ × ℕ => decide (p.2 % 2 = 1)) :=
    P1SolC10SA.SolShrink.eqOn_poly h (Code.Poly.const 1)
  exact (show Poly (fun p : ℕ × ℕ => (p.2 / 2 % p.1, p.2 / 2 / p.1)) from by fun_prop).pair e

section Correct

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}

theorem baseCode_addrL (ι : Fin I) (l : Loc K h) (t : Bool) :
    baseCode (locCount K h) (P1ChkDir.addrL ((ι, l), t)) = ((locNum K h l, ι.val), t) := by
  have hp : 0 < locCount K h := (Nat.zero_le _).trans_lt (P1ChkDir.locNum_lt l)
  have hlt := P1ChkDir.locNum_lt l
  have hdiv : P1ChkDir.addrL ((ι, l), t) / 2 = locNum K h l + locCount K h * ι.val := by
    unfold P1ChkDir.addrL
    cases t <;> simp only [Bool.false_eq_true, if_false, if_true, Prod.fst, Prod.snd] <;> omega
  have hmod : P1ChkDir.addrL ((ι, l), t) % 2 = t.toNat := by
    unfold P1ChkDir.addrL
    cases t <;> simp only [Bool.false_eq_true, if_false, if_true, Prod.fst, Prod.snd, Bool.toNat, Bool.cond_false, Bool.cond_true] <;> omega
  unfold baseCode
  rw [hdiv, hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, Nat.zero_add]
  cases t <;> rfl

theorem baseCode_state {V : FiniteMultiTapeMachine} (B : ℕ) [NeZero B] [NeZero I]
    (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
    (ι : Fin I) (l : Loc V.K h) (t : Bool) :
    baseCode (locCount V.K h) (P1P7.addr (rnState V B I σ ha) ((ι, l), t)) =
      ((locNum V.K h l, ι.val), t) := by
  rw [show P1P7.addr (rnState V B I σ ha) ((ι, l), t) = P1ChkDir.addrL ((ι, l), t) from
    P1ChkDir.stateNet_addr ha σ _ _ _ ((ι, l), t)]
  exact baseCode_addrL ι l t

end Correct

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.baseCode_state
