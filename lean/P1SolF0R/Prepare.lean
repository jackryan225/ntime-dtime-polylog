import P1SolF0R.BatchReader
import P1SolF0R.Public
import OAI.Computability.IntegerMultiplication.Code.Product

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open scoped P1ChkFinal.AstraC10

theorem keepLength_task : Computes (fun w : List Bool => w.length) (fun w => (w.length, w)) := by
  have hc := (Easy.clone (X := List Bool)).on (id : List Bool → List Bool)
  have hl := length_task.left (fun w : List Bool => send w)
  refine (hc.compose hl).bound 3 (fun w => ?_)
  change size w + w.length + 1 ≤ 3 * (w.length + 1)
  rw [P1ChkFinal.size_listBool]
  omega

abbrev RawInput (S : Type) := (List Bool × List Bool) × S
abbrev MeasuredInput (S : Type) := (List Bool × List Bool) × ((ℕ × ℕ) × S)

def measureInput {S : Type} (p : RawInput S) : MeasuredInput S :=
  (p.1, ((p.1.1.length, p.1.2.length), p.2))

/-- Obtain both length words in linear time while retaining both tapes. -/
theorem measureInput_task {S : Type} [Codec S] :
    Computes (fun p : RawInput S => p.1.1.length + p.1.2.length + size p.2) measureInput := by
  have arrange₁ : Easy (fun p : RawInput S => (p.1.1, (p.1.2, p.2))) := by fun_prop
  have first := (keepLength_task.on (fun p : RawInput S => p.1.1)).left
    (fun p => send (p.1.2, p.2))
  have arrange₂ : Easy (fun p : (ℕ × List Bool) × (List Bool × S) => (p.2.1, (p.1, p.2.2))) := by
    fun_prop
  have second := (keepLength_task.on (fun p : RawInput S => p.1.2)).left
    (fun p => send ((p.1.1.length, p.1.1), p.2))
  have arrange₃ : Easy (fun p : (ℕ × List Bool) × ((ℕ × List Bool) × S) =>
      ((p.2.1.2, p.1.2), ((p.2.1.1, p.1.1), p.2.2))) := by fun_prop
  have h := ((((arrange₁.on (id : RawInput S → RawInput S)).compose first).compose
    (arrange₂.on (fun p : RawInput S => ((p.1.1.length, p.1.1), (p.1.2, p.2))))).compose second).compose
    (arrange₃.on (fun p : RawInput S => ((p.1.2.length, p.1.2), ((p.1.1.length, p.1.1), p.2))))
  refine h.bound 40 (fun p => ?_)
  simp only [id_eq, size_prod, P1ChkFinal.size_listBool]
  have lenBound (n : ℕ) : size n ≤ 2 * n + 3 := by
    change size (P1ChkFinal.AstraC10.binary n) ≤ _
    rw [P1SolC10P.SolC10prog.binary_eq_bin, P1ChkFinal.size_listBool]
    have hpow : n < 2 ^ (n + 1) :=
      (show n < 2 ^ n from Nat.lt_two_pow_self).trans_le
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_succ n))
    have h := P1ChkFinal.length_bin_le (n + 1) n hpow
    omega
  have hx := lenBound p.1.1.length
  have hu := lenBound p.1.2.length

  omega

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.measureInput_task
