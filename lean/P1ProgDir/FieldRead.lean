import P1Wit.Layout
import P1Batch.Sort

namespace P1ProgDir.SolFieldRead

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Wit

theorem bitsVal_eq_value (l : Word) : bitsVal l = value l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bitsVal, value_cons, ih]

theorem fetch_value (D : Dims) (u : List Bool) (s i : ℕ) (q : P1Batch.Req)
    (ha : value q.1 = D.off s + i * D.width s) (hw : value q.2 = D.width s) :
    value (P1Batch.fetch u q) = readField D u s i := by
  rw [P1Batch.fetch, P1Batch.bval_eq_value, P1Batch.bval_eq_value, ha, hw, readField, readNat,
    bitsVal_eq_value]

end P1ProgDir.SolFieldRead
