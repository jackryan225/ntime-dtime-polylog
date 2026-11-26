import P1ProgDir.FamDir
import P1ChkFinal.Progs
import P1ProgDir.Adapter
import P1ProgDir.Budget

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Int

namespace P1ProgDir.SolFamTask

open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry

private theorem log_succ_le_born_length (n : ℕ) : Nat.log 2 (n + 1) ≤ (born n).length := by
  have hvalue := value_lt (born n)
  rw [birthValue] at hvalue
  have hpow : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 :=
    Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
  by_contra h
  have hexp : (born n).length + 1 ≤ Nat.log 2 (n + 1) := by omega
  have hstep := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hexp
  rw [pow_succ] at hstep
  have hpos : 0 < (2 : ℕ) ^ (born n).length := Nat.pow_pos (by decide)
  omega

private theorem header_poly (c : ℕ) (q : P1ChkFinal.Qry) :
    (Nat.log 2 (q.1.length + 1) + q.2.2.length + 1) ^ c ≤
      (size (SolGeometry.lengthHeader q).1 + 1) ^ c := by
  apply Nat.pow_le_pow_left _ c
  change _ ≤ size (born q.1.length, q.2.2) + 1
  simp only [size_prod, size_word]
  have h := log_succ_le_born_length q.1.length
  omega

private theorem decide_bool (v : Bool) [Decidable (v = true)] : decide (v = true) = v := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]

end P1ProgDir.SolFamTask

open P1ProgDir

open Classical in
theorem P1ProgDir.famProg_of_task {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b)
    (ck : List Bool → List Bool → ℕ → Bool) (c : ℕ)
    (T : Code.Task (fun p : P1ChkFinal.QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) => P1ChkFinal.budget c p.val)
      (fun p => send p.val) (fun p => send (ck p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc ck s a b cc n₂ := by
  let X := SolAdapter.Input s a b 0
  let q : X → P1ChkFinal.Qry := SolAdapter.raw
  have hu (p : X) : (q p).2.1.length = lpM2 s a b (q p).1.length := List.length_ofFn
  have hρ (p : X) : (q p).2.2.length = lpK2 a b (q p).1.length - 4 := p.2.2.property
  let toQuery (p : X) : P1ChkFinal.QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) :=
    ⟨q p, hu p, hρ p⟩
  have ht : Task (fun p => P1ChkFinal.budget c (q p)) (fun p => send (q p))
      (fun p => send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))) := T.on toQuery
  let β (p : X) := (Nat.log 2 ((q p).1.length + 1) + (q p).2.2.length + 1) ^ c
  have hβ : Dom (fun p => size (SolGeometry.lengthHeader (q p)).1) β :=
    ⟨c, 1, fun p => by simpa only [one_mul] using SolFamTask.header_poly c (q p)⟩
  obtain ⟨C, hC⟩ := SolBudget.raw_poly_cost q s hs a b hb hu
    (fun p => (hρ p).trans_le (Nat.sub_le _ _)) hβ
  have hbounded : Task (fun p : X => SolAdapter.budget s a b p.1.val.length)
      (fun p => send (q p))
      (fun p => send (ck (q p).1 (q p).2.1 (P1Batch.bval (q p).2.2))) := by
    apply ht.bound C
    intro p
    refine (show P1ChkFinal.budget c (q p) + 1 ≤
      size (q p) + (q p).2.1.length + β p + 1 from ?_).trans (hC p)
    change (q p).1.length + (q p).2.1.length + (q p).2.2.length + β p + 1 ≤ _
    simp only [size_prod, P1Dispatch.size_list]
    omega
  have hcheck := SolAdapter.checkProgram (s := s) (a := a) (b := b) (n₀ := 0)
    (fun x u i => ck x u i = true) (by simpa only [SolFamTask.decide_bool] using hbounded)
  suffices hf : ∃ (Rc : Prog Ltr) (cc : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc ck s a b cc 0 by
    obtain ⟨Rc, cc, hRc⟩ := hf
    exact ⟨Rc, cc, 0, hRc⟩
  apply FamDir.famProg_of_D8
  simpa only [SolFamTask.decide_bool] using hcheck

#print axioms P1ProgDir.famProg_of_task
