import P1SolFinal.Access

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit

theorem not_true_iff_false (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> decide

theorem decide_false_iff (p : Prop) [Decidable p] : decide p = false ↔ ¬p := by
  by_cases h : p <;> simp [h]

def numEq (p : Req) : Bool := !(less p || less (p.2, p.1))

theorem numEq_eq (a b : Word) : numEq (a, b) = decide (Bits.value a = Bits.value b) := by
  unfold numEq
  rw [less_eq, less_eq]
  by_cases h : Bits.value a = Bits.value b
  · simp only [h, lt_irrefl, decide_false, decide_true, Bool.or_self, Bool.not_false]
  · rcases lt_or_gt_of_ne h with ht | ht
    · simp only [ht, decide_true, Bool.true_or, Bool.not_true, decide_eq_false h]
    · simp only [ht, decide_true, Bool.or_true, Bool.not_true, decide_eq_false h]

@[fun_prop] theorem easy_bor : Easy (fun x : Bool × Bool => x.1 || x.2) := Easy.finite _

@[fun_prop] theorem easy_bnot : Easy (fun x : Bool => !x) := Easy.finite _

@[fun_prop] theorem easy_numEq : Easy numEq := by
  unfold numEq
  exact ((easy_less.pair (Easy.exchange.compose easy_less)).compose easy_bor).compose easy_bnot

def wordAt : ℕ → List Word → Word
  | 0 => fun l => List.casesOn l [] (fun a _ => a)
  | i + 1 => fun l => List.casesOn l [] (fun _ t => wordAt i t)

theorem easy_wordAt (i : ℕ) : Easy (wordAt i) := by
  induction i with
  | zero =>
    exact Easy.listCase (X := Word) [] Easy.fst
  | succ i ih =>
    exact Easy.listCase (X := Word) [] (Easy.snd.compose ih)

abbrev Index := Word × Word

def fmtAt (dims : ℕ → Dims) (i : Index) : List Word × Word :=
  (fmt (dims (P1Batch.bval i.1)), i.2)

theorem poly_fmtAt (dims : ℕ → Dims) (hf : FmtHyp dims) : Poly (fmtAt dims) :=
  Poly.onleft hf

/-- Budget used to compare the sizes of the small data. -/
def smallSize {M K : ℕ → ℕ} (p : QDom M K) : ℕ :=
  Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length

theorem index_size {M K : ℕ → ℕ} :
    Dom (smallSize (M := M) (K := K)) (fun p => size (bin p.val.1.length, p.val.2.2)) := by
  refine ⟨1, 5, fun p => ?_⟩
  have h := (length_bin_log p.val.1.length).trans
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)
  simp only [Nat.succ_eq_add_one] at h
  simp only [size_prod, size_listBool, smallSize, pow_one]
  omega

set_option maxHeartbeats 1000000 in
/-- Evaluate a polynomial-time format calculation on the binary length and the index, keeping the witness. -/
theorem prepare {M K : ℕ → ℕ} {S : Type*} [Codec S] (hl : LenHyp)
    (setup : Index → S) (hs : Poly setup) :
    ∃ t : QDom M K → ℕ, Dom smallSize t ∧
      Task (fun p => p.val.1.length + p.val.2.1.length + t p)
        (fun p => send p.val)
        (fun p => send (setup (bin p.val.1.length, p.val.2.2), p.val.2.1)) := by
  let ix : QDom M K → Index := fun p => (bin p.val.1.length, p.val.2.2)
  let w : QDom M K → Word := fun p => p.val.2.1
  obtain ⟨t, ht, T⟩ := hs.on (q := ix) index_size
  let costs : QDom M K → ℕ := fun p => size (ix p) + t p + 3
  have hc : Dom smallSize costs := (index_size.add ht).add (Dom.const _ 3)
  have T₁ := (hl.on (fun p : QDom M K => p.val.1)).left (fun p => send p.val.2)
  have e : Easy (fun i : Word × (Word × Word) => ((i.1, i.2.2), i.2.1)) := by fun_prop
  have T₂ := e.on (fun p : QDom M K => (bin p.val.1.length, p.val.2))
  have T₃ := T.left (fun p => send (w p))
  refine ⟨costs, hc, ?_⟩
  have H := (T₁.compose T₂).compose T₃
  refine H.bound 3 (fun p => ?_)
  simp only [size_prod, size_listBool, costs, ix]
  omega

theorem pack_budget {M K : ℕ → ℕ} {t : QDom M K → ℕ} {reply : QDom M K → Tree} {E : ℕ}
    (ht : Dom smallSize t)
    (T : Task (fun p => E * (p.val.1.length + p.val.2.1.length + p.val.2.2.length) + t p)
      (fun p => send p.val) reply) :
    ∃ c : ℕ, Task (fun p => budget c p.val) (fun p => send p.val) reply := by
  obtain ⟨k, C, hC⟩ := ht
  refine ⟨k, T.bound (E+C+1) fun p => ?_⟩
  have h := hC p
  simp only [budget, smallSize] at h ⊢
  set L := p.val.1.length + p.val.2.1.length + p.val.2.2.length
  set P := (Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length + 1) ^ k
  have he := Nat.mul_le_mul_left E (show L ≤ L + P + 1 by omega)
  have hc := Nat.mul_le_mul_left C (show P ≤ L + P + 1 by omega)
  simp only [Nat.add_mul, Nat.one_mul] at *
  omega

set_option maxHeartbeats 1000000 in
/-- A linear function of the prepared format and the whole witness has the desired mixed budget. -/
theorem finish {M K : ℕ → ℕ} {S : Type*} [Codec S] (hl : LenHyp)
    (setup : Index → S) (hsetup : Poly setup) (test : S × Word → Bool) (htest : Easy test) :
    ∃ c : ℕ, Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (test (setup (bin p.val.1.length, p.val.2.2), p.val.2.1))) := by
  obtain ⟨t, ht, T⟩ := prepare (M := M) (K := K) hl setup hsetup
  let ix : QDom M K → Index := fun p => (bin p.val.1.length, p.val.2.2)
  have hf : Dom smallSize (fun p => size (setup (ix p))) := (hsetup.length.map ix).sub index_size
  let extra : QDom M K → ℕ := fun p => t p + size (setup (ix p)) + 2
  have he : Dom smallSize extra := (ht.add hf).add (Dom.const _ 2)
  apply pack_budget (E := 3) he
  refine (T.compose (htest.on (fun p : QDom M K => (setup (ix p), p.val.2.1)))).mono (fun p => ?_)
  simp only [size_prod, size_listBool, extra]
  omega

end P1ChkFinal.SolFinal
