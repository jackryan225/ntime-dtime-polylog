import P1Hier.UTRoot

/-!
# P1Hier.UTArith (copy B of lane hier): input `h6` of `UM.accU_machine_of`

`arith_task q : Computes (fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) (arith q)`, i.e. on unary `(n, s)`
the guard bit `(s+1)² ≤ rootLog q n`, `G q n = n² / rootLog q n` and `n² / (s+1)²`, with budget
`n² + s²`. Pipeline: copy `(n, s+1)` (linear), square both (`sqT`, budget `n² + (s+1)²`),
then one linear stage (`easy_rootLog`, `easy_le`, `easy_div`).

`accU_machine_of3`: the statement of `Hierarchy.accU_machine` from the three remaining inputs
`h2` (code parser), `h5` (transcript parser), `h7` (copy A's W1 check task).
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open C1Challenge (withGuess HaltsWithin)

theorem easy_pred : Easy (fun n : ℕ => n - 1) :=
  easy_congr (easy_tally.compose easy_tailU) (fun n => by
    show send ((tally n).tail) = send (tally (n - 1))
    simp only [tally, List.tail_replicate])

/-- Squares of both components. -/
theorem sq2 : Computes (fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) (fun i => (i.1 ^ 2, i.2 ^ 2)) := by
  have T1 := Task.left (sqT.on (fun i : ℕ × ℕ => i.1)) (fun i => send i.2)
  have T2 := Task.right (sqT.on (fun i : ℕ × ℕ => i.2)) (fun i : ℕ × ℕ => send (i.1 ^ 2))
  refine Task.bound (T1.compose T2) 4 (fun i => ?_)
  show i.1 ^ 2 + ((send (i.1 ^ 2)).count + i.2 ^ 2) + 1 ≤ 4 * (i.1 ^ 2 + i.2 ^ 2 + 1)
  have : (send (i.1 ^ 2)).count = 2 * i.1 ^ 2 + 1 := size_nat' _
  omega

/-- **Input `h6`.** -/
theorem arith_task (q : ℕ) : Computes (fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) (arith q) := by
  have A1 : Easy (fun i : ℕ × ℕ => ((i.1, i.2 + 1), (i.1, i.2 + 1))) :=
    ((Easy.fst (X := ℕ) (Y := ℕ)).pair ((Easy.snd (X := ℕ) (Y := ℕ)).compose easy_succ)).compose
      Easy.clone
  have A2 : Computes (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 ^ 2 + x.1.2 ^ 2)
      (fun x => ((x.1.1 ^ 2, x.1.2 ^ 2), x.2)) :=
    Task.left (sq2.on (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1)) (fun x => send x.2)
  have hρ : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => rootLog q st.2.1) :=
    (Easy.fstCompose (Easy.snd (X := ℕ × ℕ) (Y := ℕ × ℕ))).compose (easy_rootLog q)
  have hN : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => st.1.1) :=
    Easy.fstCompose (Easy.fst (X := ℕ × ℕ) (Y := ℕ × ℕ))
  have hS : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => st.1.2) :=
    Easy.sndCompose (Easy.fst (X := ℕ × ℕ) (Y := ℕ × ℕ))
  have hg : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => decide (st.1.2 ≤ rootLog q st.2.1)) :=
    (hS.pair hρ).compose easy_le
  have hG : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => st.1.1 / (rootLog q st.2.1 - 1 + 1)) :=
    (hN.pair (hρ.compose easy_pred)).compose easy_div
  have hT : Easy (fun st : (ℕ × ℕ) × (ℕ × ℕ) => st.1.1 / (st.1.2 - 1 + 1)) :=
    (hN.pair (hS.compose easy_pred)).compose easy_div
  have A3 := hg.pair (hG.pair hT)
  have c2 := Computes.comp A3 (Computes.comp A2 A1)
  refine (Task.bound (b' := fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) c2 30 (fun i => ?_)).conform
    (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  · show size i + (i.1 ^ 2 + (i.2 + 1) ^ 2) +
        size (((i.1 ^ 2, (i.2 + 1) ^ 2), (i.1, i.2 + 1)) : (ℕ × ℕ) × (ℕ × ℕ)) + 1 ≤
      30 * (i.1 ^ 2 + i.2 ^ 2 + 1)
    simp only [size_prod, size_nat']
    have e1 : (i.2 + 1) ^ 2 = i.2 ^ 2 + 2 * i.2 + 1 := by ring
    have hn : i.1 ≤ i.1 ^ 2 := Nat.le_self_pow (by norm_num) _
    have hs : i.2 ≤ i.2 ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  · show send (decide ((i.2 + 1) ^ 2 ≤ rootLog q i.1), i.1 ^ 2 / (rootLog q i.1 - 1 + 1),
        i.1 ^ 2 / ((i.2 + 1) ^ 2 - 1 + 1)) =
      send (decide ((i.2 + 1) ^ 2 ≤ rootLog q i.1), i.1 ^ 2 / rootLog q i.1,
        i.1 ^ 2 / (i.2 + 1) ^ 2)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (rootLog_pos q i.1)),
      Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity : 0 < (i.2 + 1) ^ 2))]

open Classical in
/-- `accU_machine` from the three remaining inputs: the code parser, the transcript parser,
and copy A's W1 check task. -/
theorem accU_machine_of3 (q : ℕ) (d : MCode) (h2 : Easy (px2 d)) (h5 : Easy decT2)
    (h7 : Task checkBudget send (fun i : MCode × List Bool × ℕ × List Entry =>
      send (decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2)))) :
    ∃ (U : C1Challenge.Machine) (b : ℕ), ∀ (x : List Bool) (u : Fin (gU x.length) → Bool),
      HaltsWithin U (withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
        (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length) :=
  accU_machine_of q d easy_unGuess h2 h5 (arith_task q) h7 size_code_le

end P1Hier.UM
