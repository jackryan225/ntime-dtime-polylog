import P1SolFactor.FieldSplit
import P1SolFactor.FrameTransfer

namespace P1SolFactor.SolRows

open OAI.Computability.IntegerMultiplication P1ProgEng

variable {A : Type}

/-- Clear the consecutive field registers, preserving the inputs and decision registers. -/
def clearFields (j : ℕ) : ℕ → Prog A
  | 0 => .pass
  | count + 1 => .join (clearFields (j + 1) count) (SolOrbit.clearTo (fieldReg j) (fun _ => false))

theorem clearFields_runs {Γ : Scope A} (base : Reg A) (j : ℕ) (fields : List (List A))
    (hbase : ∀ k, k < fields.length → base (fieldReg (j + k)) = []) :
    Runs Γ (clearFields j fields.length) (putFields base j fields) base
      (7 * fields.flatten.length + 5 * fields.length + 1) := by
  induction fields generalizing base j with
  | nil => exact Runs.pass
  | cons word fields ih =>
    have hfirst : base (fieldReg j) = [] := by simpa only [Nat.add_zero] using hbase 0 (by simp)
    let mid := Function.update base (fieldReg j) (word ++ base (fieldReg j))
    have htail (k : ℕ) (hk : k < fields.length) : mid (fieldReg (j + 1 + k)) = [] := by
      have hne : fieldReg (j + 1 + k) ≠ fieldReg j := by unfold fieldReg; omega
      have hk' : 1 + k < (word :: fields).length := by simp only [List.length_cons]; omega
      dsimp only [mid]
      rw [Function.update_of_ne hne]
      simpa only [Nat.add_assoc] using hbase (1 + k) hk'
    have ht := ih mid (j + 1) htail
    have hc := SolOrbit.clearAll_runs (Γ := Γ) (r := mid) (fieldReg j)
    have hword : mid (fieldReg j) = word := by
      simp only [mid, Function.update_self, hfirst, List.append_nil]
    have hrestore : Function.update mid (fieldReg j) [] = base := by
      dsimp only [mid]
      rw [Function.update_idem, ← hfirst, Function.update_eq_self]
    rw [hrestore, hword] at hc
    have h := ht.join hc
    apply h.mono
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

end P1SolFactor.SolRows
