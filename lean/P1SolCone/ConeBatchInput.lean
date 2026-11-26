import P1SolFmt.Length
import P1ChkFinal.ProgC11
import P1SolCone.ProgramLists

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open scoped P1ChkFinal.AstraC10

/-- Keep the input and witness as separate texts and compute their lengths in binary. -/
def prepareConeQuery (q : P1ChkFinal.Qry) :
    (List Bool × List Bool) × (List Bool × List Bool × List Bool) :=
  ((q.1, q.2.1), (P1ChkFinal.bin q.1.length, P1ChkFinal.bin q.2.1.length, q.2.2))

theorem prepareConeQuery_easy : Easy prepareConeQuery := by
  have len : Easy (fun x : List Bool => P1ChkFinal.bin x.length) := by
    apply (P1ChkFinal.lenHyp_bin P1SolFmt.SolLength.lenHyp).mono
    intro w
    rw [P1ChkFinal.size_listBool]
    omega
  have x : Easy (fun q : P1ChkFinal.Qry => q.1) := Easy.fst
  have u : Easy (fun q : P1ChkFinal.Qry => q.2.1) := Easy.snd.compose Easy.fst
  have ρ : Easy (fun q : P1ChkFinal.Qry => q.2.2) := Easy.snd.compose Easy.snd
  exact (x.pair u).pair ((x.compose len).pair ((u.compose len).pair ρ))

/-- Clip a request to the end of the text. This makes even malformed offsets satisfy
the batched lookup command's input condition. -/
def clipConeRequest (m : ℕ) (r : P1Batch.Req) : P1Batch.Req :=
  (P1ChkFinal.bin (min (P1Batch.bval r.1) m), r.2)

theorem clipConeRequest_offset (m : ℕ) (r : P1Batch.Req) :
    P1Batch.bval (clipConeRequest m r).1 ≤ m := by
  change P1Batch.bval (P1ChkFinal.bin (min (P1Batch.bval r.1) m)) ≤ m
  rw [P1ChkFinal.bval_bin]
  exact min_le_right _ _

theorem fetch_clipConeRequest (w : List Bool) (r : P1Batch.Req) :
    P1Batch.fetch w (clipConeRequest w.length r) = P1Batch.fetch w r := by
  unfold P1Batch.fetch clipConeRequest
  simp only [P1ChkFinal.bval_bin]
  by_cases h : P1Batch.bval r.1 ≤ w.length
  · rw [min_eq_left h]
  · rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h)), List.drop_length,
      List.drop_eq_nil_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h))]

theorem clipConeRequest_poly : Poly (fun p : ℕ × P1Batch.Req => clipConeRequest p.1 p.2) := by
  have h : Poly (fun p : ℕ × P1Batch.Req => P1Batch.bval p.2.1) := poly_bval (Easy.snd.compose Easy.fst).poly
  exact (poly_bin (poly_min h Easy.fst.poly)).pair (Easy.snd.compose Easy.snd).poly

end P1SolCone.SolCone
