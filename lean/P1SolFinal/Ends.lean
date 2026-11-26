import P1SolFinal.Arithmetic

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open scoped Classical

@[fun_prop] theorem easy_band : Easy (fun p : Bool × Bool => p.1 && p.2) := Easy.finite _

theorem easy_any_fixed {X Y : Type*} [Codec X] (test : Y → X → Bool) (ys : List Y)
    (h : ∀ y, Easy (test y)) : Easy (fun x => ys.any (fun y => test y x)) := by
  induction ys with
  | nil => exact Easy.const false
  | cons y ys ih => exact ((h y).pair ih).compose easy_bor

noncomputable def endVote {d : ℕ} (f : Fin d → Prop) (w : Word) : Bool :=
  (Finset.univ.toList : List (Fin d)).any fun j => numEq (w, bin j.val) && decide (f j)

theorem endVote_eq {d : ℕ} (f : Fin d → Prop) (w : Word) :
    endVote f w = true ↔ ∃ h : Bits.value w < d, f ⟨Bits.value w, h⟩ := by
  simp only [endVote, List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and,
    Bool.and_eq_true, numEq_eq, decide_eq_true_eq, value_bin]
  constructor
  · rintro ⟨⟨j, h⟩, hj, hf⟩
    change Bits.value w = j at hj
    subst j
    exact ⟨h, hf⟩
  · rintro ⟨h, hf⟩
    exact ⟨⟨Bits.value w, h⟩, rfl, hf⟩

@[fun_prop] theorem easy_endVote {d : ℕ} (f : Fin d → Prop) : Easy (endVote f) := by
  apply easy_any_fixed
  intro j
  exact (((Easy.identity.pair (Easy.const _)).compose easy_numEq).pair
    (Easy.const (decide (f j)))).compose easy_band

abbrev EndsData := (Bool × Bool) × Req × Req

def endsSetup (f : List Word × Word) : EndsData :=
  let o := wordAt 8 f.1
  let w := wordAt 9 f.1
  let v := minus (wordAt 11 f.1, [true])
  ((numEq (f.2, []), numEq (f.2, [true])), ((o, w), (Bits.add (o, multiply (v, w)), w)))

theorem poly_endsSetup : Poly endsSetup := by
  let items : List Word × Word → Word × Word × Word := fun f =>
    (wordAt 8 f.1, wordAt 9 f.1, minus (wordAt 11 f.1, [true]))
  have hi : Easy items :=
    (Easy.fst.compose (easy_wordAt 8)).pair ((Easy.fst.compose (easy_wordAt 9)).pair
      (((Easy.fst.compose (easy_wordAt 11)).pair (Easy.const [true])).compose easy_minus))
  let flags : List Word × Word → Bool × Bool := fun f => (numEq (f.2, []), numEq (f.2, [true]))
  have hf : Easy flags :=
    (((Easy.snd.pair (Easy.const [])).compose easy_numEq)).pair
      ((Easy.snd.pair (Easy.const [true])).compose easy_numEq)
  have hp : Poly (fun i : Word × Word × Word => multiply (i.2.2, i.2.1)) :=
    (show Easy (fun i : Word × Word × Word => (i.2.2, i.2.1)) from by fun_prop).poly.compose poly_multiply
  have hq : Poly (fun i : Word × Word × Word => Bits.add (i.1, multiply (i.2.2, i.2.1))) :=
    (Easy.fst.poly.pair hp).compose (Bits.easy_add Easy.identity).poly
  have hh : Poly (fun i : Word × Word × Word =>
      ((i.1, i.2.1), (Bits.add (i.1, multiply (i.2.2, i.2.1)), i.2.1))) :=
    (show Easy (fun i : Word × Word × Word => (i.1, i.2.1)) from by fun_prop).poly.pair
      (hq.pair (Easy.sndCompose Easy.identity |>.fstCompose).poly)
  exact hf.poly.pair (hi.poly.compose hh)

noncomputable def endsTest {d : ℕ} (start last : Fin d → Prop) (q : EndsData × Word) : Bool :=
  (!q.1.1.1 || endVote start (slice (q.1.2.1, q.2))) &&
    (!q.1.1.2 || endVote last (slice (q.1.2.2, q.2)))

set_option maxHeartbeats 1000000 in
theorem easy_endsTest {d : ℕ} (hl : LenHyp) (start last : Fin d → Prop) : Easy (endsTest start last) := by
  have hs : Easy slice := computes_slice hl
  unfold endsTest
  have h₀ : Easy (fun q : EndsData × Word => (q.1.2.1, q.2)) := by fun_prop
  have h₁ : Easy (fun q : EndsData × Word => (q.1.2.2, q.2)) := by fun_prop
  have hp₀ : Easy (fun q : EndsData × Word => !q.1.1.1) := by fun_prop
  have hp₁ : Easy (fun q : EndsData × Word => !q.1.1.2) := by fun_prop
  exact ((hp₀.pair ((h₀.compose hs).compose (easy_endVote start))).compose easy_bor |>.pair
    ((hp₁.pair ((h₁.compose hs).compose (easy_endVote last))).compose easy_bor)).compose easy_band

theorem value_slice (q : Req) (u : Word) :
    Bits.value (slice (q, u)) = readNat u (Bits.value q.1) (Bits.value q.2) := by
  exact (value_field _).symm

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

set_option maxHeartbeats 1000000 in
theorem endsTest_correct (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
    (dims : ℕ → Dims) (x u ρ : Word) :
    endsTest (fun j => b.repr 1 j = 1) (fun j => l (b j) = 1)
      (endsSetup (fmtAt dims (bin x.length, ρ)), u) =
        decide (C13endsw b l dims x u (P1Batch.bval ρ)) := by
  unfold fmtAt
  rw [bval_bin]
  set D := dims x.length
  let a := D.off D.secChain
  let w := D.width D.secChain
  have he0 : Bits.value (wordAt 8 (fmt D)) = a := by
    change Bits.value a.bits = a
    exact value_bits _
  have he1 : Bits.value (wordAt 9 (fmt D)) = w := by
    change Bits.value w.bits = w
    exact value_bits _
  have he2 : Bits.value (wordAt 11 (fmt D)) = D.chainLen := by
    change Bits.value D.chainLen.bits = D.chainLen
    exact value_bits _
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [endsTest, endsSetup, Bool.and_eq_true, Bool.or_eq_true, not_true_iff_false, endVote_eq,
    numEq_eq, Bits.value_nil, Bits.value_cons, Bits.d1, Nat.mul_zero, Nat.add_zero, value_slice,
    Bits.add_val, multiply_value, minus_eq, he0, he1, he2, ← P1Batch.bval_eq_value ρ]
  have s₀ : readNat u a w = rdChain D u 0 := by simp only [rdChain, readField, Nat.zero_mul, Nat.add_zero, a, w]
  have s₁ : readNat u (a + (D.chainLen - 1) * w) w = rdChain D u (finP D) := rfl
  simp only [s₀, s₁, C13endsw, C13ends, decide_false_iff]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨fun e => h₀.resolve_left (fun hn => hn e), fun e => h₁.resolve_left (fun hn => hn e)⟩
  · rintro ⟨h₀, h₁⟩
    constructor
    · by_cases h : P1Batch.bval ρ = 0
      · exact Or.inr (h₀ h)
      · exact Or.inl h
    · by_cases h : P1Batch.bval ρ = 1
      · exact Or.inr (h₁ h)
      · exact Or.inl h

/-- Family 13, with the exact statement from the owner's program interface. -/
theorem progC13ends (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C13endsw b l dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  obtain ⟨c, T⟩ := finish (M := M) (K := K) hl (fun i => endsSetup (fmtAt dims i))
    ((poly_fmtAt dims hf).compose poly_endsSetup) _ (easy_endsTest hl (fun j => b.repr 1 j = 1) (fun j => l (b j) = 1))
  exact ⟨c, T.conform (fun _ => rfl) (fun _ => rfl)
    (fun p => congrArg send (endsTest_correct b l dims p.val.1 p.val.2.1 p.val.2.2))⟩

end P1ChkFinal.SolFinal

#print axioms P1ChkFinal.SolFinal.progC13ends
