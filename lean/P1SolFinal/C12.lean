import P1SolFinal.Group
import P1SolFinal.Arithmetic

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit
open scoped Classical

/-- The request for field number `i`, given the section start and width. -/
def requestAt (p : Req × Word) : Req :=
  (Bits.add (p.1.1, multiply (p.2, p.1.2)), p.1.2)

theorem poly_requestAt : Poly requestAt := by
  let input : Req × Word → Req := fun p => (p.2, p.1.2)
  have h : Easy input := by unfold input; fun_prop
  have a : Easy (fun p : Req × Word => p.1.1) := by fun_prop
  have w : Easy (fun p : Req × Word => p.1.2) := by fun_prop
  exact ((a.poly.pair (h.poly.compose poly_multiply)).compose (Bits.easy_add Easy.identity).poly).pair w.poly

theorem requestAt_value (o w i : Word) :
    Bits.value (requestAt ((o, w), i)).1 = Bits.value o + Bits.value i * Bits.value w := by
  simp only [requestAt, Bits.add_val, multiply_value]

/-- Request a contiguous block and keep the width of its individual fields. -/
def blockRequest (p : Req × Req) : Req × Word :=
  (requestAt ((p.1.1, multiply (p.2.1, p.1.2)), p.2.2), p.1.2)

theorem poly_blockRequest : Poly blockRequest := by
  have h₁ : Easy (fun p : Req × Req => (p.2.1, p.1.2)) := by fun_prop
  have h₂ : Easy (fun p : Req × Req => p.1.1) := by fun_prop
  have h₃ : Easy (fun p : Req × Req => p.2.2) := by fun_prop
  have h₄ : Easy (fun p : Req × Req => p.1.2) := by fun_prop
  exact (((h₂.poly.pair (h₁.poly.compose poly_multiply)).pair h₃.poly).compose poly_requestAt).pair h₄.poly

abbrev C12Data := (Bool × Bool) × Word × Req × (Req × Word)

def setupC12 (f : List Word × Word) : C12Data :=
  let n := wordAt 0 f.1
  let y := minus (n, [true])
  let arcs := wordAt 1 f.1
  ((numEq (f.2, []), numEq (n, [])),
    wordAt 10 f.1, requestAt ((wordAt 4 f.1, wordAt 5 f.1), y),
    blockRequest ((wordAt 6 f.1, wordAt 7 f.1), (arcs, y)))

theorem poly_setupC12 : Poly setupC12 := by
  let V := List Word × Word
  let N : V → Word := fun f => wordAt 0 f.1
  let Y : V → Word := fun f => minus (N f, [true])
  have e (n : ℕ) : Easy (fun f : V => wordAt n f.1) := Easy.fst.compose (easy_wordAt n)
  have hN : Easy N := e 0
  have hY : Easy Y := (hN.pair (Easy.const _)).compose easy_minus
  have hflags : Easy (fun f : V => (numEq (f.2, []), numEq (N f, []))) :=
    ((Easy.snd.pair (Easy.const [])).compose easy_numEq).pair ((hN.pair (Easy.const [])).compose easy_numEq)
  have hΩ := (((e 4).pair (e 5)).pair hY).poly.compose poly_requestAt
  have hBlock := (((e 6).pair (e 7)).pair ((e 1).pair hY)).poly.compose poly_blockRequest
  exact hflags.poly.pair ((e 10).poly.pair (hΩ.pair hBlock))

def dropWord (i : Word × Word) : Word := i.2.drop (Bits.value i.1)

theorem easy_dropWord (hl : LenHyp) : Easy dropWord := by
  have e : Easy (fun p : Word × (Word × Word) => ((p.2.1, p.1), p.2.2)) := by fun_prop
  have T := ((easy_lenPair (S := Word) hl).compose e).compose (show Easy slice from computes_slice hl)
  refine T.conform (fun _ => rfl) (fun _ => rfl) (fun i => ?_)
  apply congrArg send
  simp only [slice, value_bin, dropWord]
  apply List.take_of_length_le
  rw [List.length_drop]
  omega

private def zeroStep (bit good : Bool) : Bool × List Unit :=
  (!bit && good, [])

def zeroScan (w : Word) : Bool := (machine zeroStep (w, true)).2

theorem zeroScan_eq (w : Word) : zeroScan w = true ↔ ∀ b ∈ w, b = false := by
  have h (w : Word) (c : Bool) :
      (machine zeroStep (w, c)).2 = true ↔ c = true ∧ ∀ b ∈ w, b = false := by
    induction w generalizing c with
    | nil => simp only [machine_nil, List.not_mem_nil, false_implies, implies_true, and_true]
    | cons bit w ih =>
      simp only [machine_cons, zeroStep, ih, Bool.and_eq_true, not_true_iff_false,
        List.forall_mem_cons, and_assoc, and_left_comm]
  simpa only [zeroScan, true_and] using h w true

theorem easy_zeroScan : Easy zeroScan := by
  have e : Easy (fun w : Word => (w, true)) := Easy.identity.pair (Easy.const true)
  exact (Easy.machine (step := zeroStep) e).sndCompose

def tailTest (i : Word × (Word × Word)) : Bool :=
  !less (i.1, i.2.1) && zeroScan (slice ((i.2.1, i.1), i.2.2))

theorem easy_tailTest (hl : LenHyp) : Easy (fun p : Word × Word => tailTest (bin p.2.length, p)) := by
  have hs : Easy slice := computes_slice hl
  have e₁ : Easy (fun i : Word × (Word × Word) => !less (i.1, i.2.1)) := by fun_prop
  have e₂ : Easy (fun i : Word × (Word × Word) => slice ((i.2.1, i.1), i.2.2)) := by fun_prop
  have E : Easy tailTest :=
    (e₁.pair (e₂.compose easy_zeroScan)).compose (Easy.finite (fun i : Bool × Bool => i.1 && i.2))
  exact (easy_lenPair hl).compose E

theorem tailTest_eq (x u : Word) :
    tailTest (bin u.length, (x, u)) = true ↔ Bits.value x ≤ u.length ∧
      ∀ b ∈ u.drop (Bits.value x), b = false := by
  have e : slice ((x, bin u.length), u) = u.drop (Bits.value x) := by
    simp only [slice, value_bin]
    apply List.take_of_length_le
    rw [List.length_drop]
    omega
  simp only [tailTest, Bool.and_eq_true, not_true_iff_false, less_eq, value_bin,
    decide_false_iff, not_lt, e, zeroScan_eq]

def claimedLength (p : C12Data × Word) : Word :=
  bif p.1.1.2 then [] else Bits.add (slice (p.1.2.2.1, p.2),
    sumFields (p.1.2.2.2.2, slice (p.1.2.2.2.1, p.2)))

def testC12 (p : C12Data × Word) (hl : Word → Word) : Bool :=
  let tail := dropWord (p.1.2.1, p.2)
  !p.1.1.1 || tailTest (hl tail, (claimedLength p, tail))

theorem easy_testC12 (hl : LenHyp) :
    Easy (fun p : C12Data × Word => testC12 p (fun tail => bin tail.length)) := by
  have hs : Easy slice := computes_slice hl
  have hw : Easy sumFields := easy_sumFields hl
  have hd : Easy dropWord := easy_dropWord hl
  have hc : Easy claimedLength := by unfold claimedLength; fun_prop
  have h₁ : Easy (fun p : C12Data × Word => !p.1.1.1) := by fun_prop
  have h₂ : Easy (fun p : C12Data × Word => (claimedLength p, dropWord (p.1.2.1, p.2))) := by fun_prop
  exact (h₁.pair (h₂.compose (easy_tailTest hl))).compose easy_bor

theorem value_wordAt_fmt (D : Dims) :
    Bits.value (wordAt 0 (fmt D)) = finN D ∧
    Bits.value (wordAt 1 (fmt D)) = finArcs D ∧
    Bits.value (wordAt 4 (fmt D)) = D.off D.secOmega ∧
    Bits.value (wordAt 5 (fmt D)) = D.width D.secOmega ∧
    Bits.value (wordAt 6 (fmt D)) = D.off (secLev D.top .width) ∧
    Bits.value (wordAt 7 (fmt D)) = D.width (secLev D.top .width) ∧
    Bits.value (wordAt 10 (fmt D)) = D.fixedLen := by
  exact ⟨value_bits _, value_bits _, value_bits _, value_bits _, value_bits _, value_bits _, value_bits _⟩

theorem sumFields_block (D : Dims) (y : ℕ) (u : Word) (a w : Word) (h₁ : Bits.value a =
    D.off (secLev D.top .width) + y * (finArcs D * D.width (secLev D.top .width)))
    (h₂ : Bits.value w = D.width (secLev D.top .width)) :
    Bits.value (sumFields (w, (u.drop (Bits.value a)).take (finArcs D * Bits.value w))) = wsOf D u y := by
  rw [sumFields_value, fixedChunks_sum, h₁, h₂]
  unfold wsOf
  congr 1
  funext t
  let L := D.lv D.top
  have hidx : (y * L.lanes + t / L.slots) * L.slots + t % L.slots =
      y * finArcs D + t := by
    have h := Nat.div_add_mod t L.slots
    change (y * L.lanes + t / L.slots) * L.slots + t % L.slots = y * (L.lanes * L.slots) + t
    simp only [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm (t / L.slots) L.slots]
    omega
  rw [List.drop_drop]
  simp only [arcW, rdWidth, readField, readNat, value_field]
  have haddr : D.off (secLev D.top .width) + y * (finArcs D * D.width (secLev D.top .width)) +
      t * D.width (secLev D.top .width) =
      D.off (secLev D.top .width) + ((y * L.lanes + t / L.slots) * L.slots + t % L.slots) *
        D.width (secLev D.top .width) := by
    rw [hidx]
    ring
  rw [haddr]

set_option maxHeartbeats 1200000 in
theorem claimedLength_correct (D : Dims) (u ρ : Word) :
    Bits.value (claimedLength (setupC12 (fmt D, ρ), u)) =
    total (finN D) (rdOmega D u) (wsOf D u) := by
  obtain ⟨hN, hA, hO, hOW, hW, hWW, hLen⟩ := value_wordAt_fmt D
  unfold claimedLength setupC12 total
  dsimp only
  rw [numEq_eq, Bits.value_nil, hN]
  by_cases h : finN D = 0
  · simp only [h, decide_true, Bool.cond_true, Bits.value_nil, ite_true]
  simp only [h, decide_false, Bool.cond_false, ite_false, Bits.add_val]
  let s := secLev D.top Mem.width
  let y := finN D - 1
  have hY : Bits.value (minus (wordAt 0 (fmt D), [true])) = y := by
    rw [minus_eq, hN]
    rfl
  have hΩ : Bits.value (slice (requestAt ((wordAt 4 (fmt D), wordAt 5 (fmt D)),
      minus (wordAt 0 (fmt D), [true])), u)) = rdOmega D u y := by
    simp only [slice, requestAt, Bits.add_val, multiply_value, hO, hOW, hY,
      rdOmega, readField, readNat, value_field]
  rw [hΩ]
  congr 1
  let q := blockRequest ((wordAt 6 (fmt D), wordAt 7 (fmt D)),
    (wordAt 1 (fmt D), minus (wordAt 0 (fmt D), [true])))
  change Bits.value (sumFields (q.2, slice (q.1, u))) = wsOf D u y
  have he : Bits.value q.1.2 = finArcs D * Bits.value q.2 := by
    simp only [q, blockRequest, requestAt, multiply_value, hA]
  unfold slice
  rw [he]
  apply sumFields_block
  · simp only [q, blockRequest, requestAt_value, multiply_value, hW, hWW, hA, hY]
  · exact hWW

set_option maxHeartbeats 1200000 in
theorem testC12_correct (dims : ℕ → Dims) (x u ρ : Word) :
    testC12 (setupC12 (fmtAt dims (bin x.length, ρ)), u) (fun tail => bin tail.length) =
      decide (C12w dims x u (P1Batch.bval ρ)) := by
  unfold fmtAt
  rw [bval_bin]
  set D := dims x.length
  have e : dropWord ((setupC12 (fmt D, ρ)).2.1, u) = rdPayload D u := by
    change u.drop (Bits.value (wordAt 10 (fmt D))) = u.drop D.fixedLen
    rw [(value_wordAt_fmt D).2.2.2.2.2.2]
  have f : (setupC12 (fmt D, ρ)).1.1 = decide (P1Batch.bval ρ = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [setupC12, numEq_eq, Bits.value_nil, P1Batch.bval_eq_value, decide_eq_true_eq]
    exact decide_eq_true_iff
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [testC12, Bool.or_eq_true, not_true_iff_false, f, tailTest_eq, e,
    claimedLength_correct, C12w, C12, decide_false_iff]
  constructor
  · rintro (h | h) h₀
    · exact False.elim (h h₀)
    · exact h
  · intro h
    by_cases h₀ : P1Batch.bval ρ = 0
    · exact Or.inr (h h₀)
    · exact Or.inl h₀

/-- Family 11, including the zero at the first padding bit. -/
theorem progC12 (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C12w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  obtain ⟨c, T⟩ := finish (M := M) (K := K) hl (fun i => setupC12 (fmtAt dims i))
    ((poly_fmtAt dims hf).compose poly_setupC12) _ (easy_testC12 hl)
  exact ⟨c, T.conform (fun _ => rfl) (fun _ => rfl)
    (fun p => congrArg send (testC12_correct dims p.val.1 p.val.2.1 p.val.2.2))⟩

end P1ChkFinal.SolFinal

#print axioms P1ChkFinal.SolFinal.progC12
