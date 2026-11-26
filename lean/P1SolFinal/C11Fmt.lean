import P1SolFinal.C12

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit
open scoped Classical

abbrev C11Data := (Bool × Bool × Bool) × Req × Req × (Req × Word)

def setupC11 (f : List Word × Word) : C11Data :=
  let n := wordAt 0 f.1
  let y := f.2
  let y' := Bits.add (y, [true])
  let Ω := (wordAt 4 f.1, wordAt 5 f.1)
  ((!less (y, n), numEq (y, []), less (y', n)), requestAt (Ω, y), requestAt (Ω, y'),
    blockRequest ((wordAt 6 f.1, wordAt 7 f.1), (wordAt 1 f.1, y)))

theorem poly_setupC11 : Poly setupC11 := by
  let V := List Word × Word
  let N : V → Word := fun f => wordAt 0 f.1
  let Y' : V → Word := fun f => Bits.add (f.2, [true])
  have e (n : ℕ) : Easy (fun f : V => wordAt n f.1) := Easy.fst.compose (easy_wordAt n)
  have hY' : Easy Y' := Bits.easy_add (Easy.snd.pair (Easy.const _))
  have eout : Easy (fun f : V => !less (f.2, N f)) := ((Easy.snd.pair (e 0)).compose easy_less).compose easy_bnot
  have ezero : Easy (fun f : V => numEq (f.2, [])) := (Easy.snd.pair (Easy.const _)).compose easy_numEq
  have esucc : Easy (fun f : V => less (Y' f, N f)) := (hY'.pair (e 0)).compose easy_less
  have eΩ := (e 4).pair (e 5)
  have hΩ := (eΩ.pair Easy.snd).poly.compose poly_requestAt
  have hΩ' := (eΩ.pair hY').poly.compose poly_requestAt
  have hBlock := (((e 6).pair (e 7)).pair ((e 1).pair Easy.snd)).poly.compose poly_blockRequest
  exact (eout.pair (ezero.pair esucc)).poly.pair (hΩ.pair (hΩ'.pair hBlock))

def testC11 (p : C11Data × Word) : Bool :=
  let omega := slice (p.1.2.1, p.2)
  let next := slice (p.1.2.2.1, p.2)
  let widths := sumFields (p.1.2.2.2.2, slice (p.1.2.2.2.1, p.2))
  p.1.1.1 ||
    ((!p.1.1.2.1 || numEq (omega, [])) &&
      (!p.1.1.2.2 || numEq (next, Bits.add (omega, widths))))

set_option maxHeartbeats 1000000 in
theorem easy_testC11 (hl : LenHyp) : Easy testC11 := by
  have hs : Easy slice := computes_slice hl
  have hw : Easy sumFields := easy_sumFields hl
  have hor : Easy (fun i : Bool × Bool => i.1 || i.2) := easy_bor
  have hand : Easy (fun i : Bool × Bool => i.1 && i.2) := Easy.finite _
  unfold testC11
  dsimp only
  fun_prop

set_option maxHeartbeats 1500000 in
theorem testC11_correct (dims : ℕ → Dims) (x u ρ : Word) :
    testC11 (setupC11 (fmtAt dims (bin x.length, ρ)), u) =
      decide (C11w dims x u (P1Batch.bval ρ)) := by
  unfold fmtAt
  rw [bval_bin]
  set D := dims x.length
  obtain ⟨hN, hA, hO, hOW, hW, hWW, _⟩ := value_wordAt_fmt D
  let y := P1Batch.bval ρ
  have hy : Bits.value ρ = y := (P1Batch.bval_eq_value _).symm
  have htrue : Bits.value ([true] : Word) = 1 := rfl
  let Ω := (wordAt 4 (fmt D), wordAt 5 (fmt D))
  have hΩ (v : Word) :
      Bits.value (slice (requestAt (Ω, v), u)) = rdOmega D u (Bits.value v) := by
    simp only [Ω, slice, requestAt, Bits.add_val, multiply_value, hO, hOW, rdOmega, readField,
      readNat, value_field]
  let q := blockRequest ((wordAt 6 (fmt D), wordAt 7 (fmt D)), (wordAt 1 (fmt D), ρ))
  have hq : Bits.value (sumFields (q.2, slice (q.1, u))) = wsOf D u y := by
    have hLen : Bits.value q.1.2 = finArcs D * Bits.value q.2 := by
      simp only [q, blockRequest, requestAt, multiply_value, hA]
    unfold slice
    rw [hLen]
    apply sumFields_block
    · simp only [q, blockRequest, requestAt_value, multiply_value, hW, hWW, hA, hy]
    · exact hWW
  let first := slice (requestAt (Ω, ρ), u)
  let v' := Bits.add (ρ, [true])
  let next := slice (requestAt (Ω, v'), u)
  let widths := sumFields (q.2, slice (q.1, u))
  let bound := wordAt 0 (fmt D)
  let isOutside := !less (ρ, bound)
  let checkFirst := !numEq (ρ, []) || numEq (first, [])
  let checkNext := !less (v', bound) || numEq (next, Bits.add (first, widths))
  have hFirst : Bits.value first = rdOmega D u y := by
    dsimp only [first]
    rw [hΩ, hy]
  have hv' : Bits.value v' = y + 1 := by simp only [v', Bits.add_val, hy, htrue]
  have hNext : Bits.value next = rdOmega D u (y + 1) := by
    dsimp only [next]
    rw [hΩ, hv']
  have hWidths : Bits.value widths = wsOf D u y := hq
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  change (isOutside || (checkFirst && checkNext)) = true ↔ _
  simp only [isOutside, checkFirst, checkNext, Bool.or_eq_true, Bool.and_eq_true, not_true_iff_false,
    less_eq, numEq_eq, Bits.value_nil, decide_eq_true_eq, decide_false_iff, hFirst, hNext, hWidths, hv',
    Bits.add_val, hy, bound, hN, C11w, C11]
  constructor
  · rintro (hout | ⟨hfirst, hstep⟩) hv
    · exact False.elim (hout hv)
    · refine ⟨fun hz => ?_, fun hs => hstep.resolve_left (fun hn => hn hs)⟩
      change y = 0 at hz
      have h := hfirst.resolve_left (fun hn => hn hz)
      rwa [hz] at h
  · intro h
    by_cases hv : y < finN D
    · obtain ⟨hfirst, hstep⟩ := h hv
      refine Or.inr ⟨?_, ?_⟩
      · by_cases hy0 : y = 0
        · exact Or.inr (hy0.symm ▸ hfirst hy0)
        · exact Or.inl hy0
      · by_cases hy1 : y + 1 < finN D
        · exact Or.inr (hstep hy1)
        · exact Or.inl hy1
    · exact Or.inl hv

/-- The family 10 program using only the format interface stated in the brief. -/
theorem progC11Fmt (dims : ℕ → Dims) (M K : ℕ → ℕ) (hb : BatchHyp) (hl : LenHyp) (hf : FmtHyp dims) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C11w dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  obtain ⟨c, T⟩ := finish (M := M) (K := K) hl (fun i => setupC11 (fmtAt dims i))
    ((poly_fmtAt dims hf).compose poly_setupC11) _ (easy_testC11 hl)
  exact ⟨c, T.conform (fun _ => rfl) (fun _ => rfl)
    (fun p => congrArg send (testC11_correct dims p.val.1 p.val.2.1 p.val.2.2))⟩

end P1ChkFinal.SolFinal

#print axioms P1ChkFinal.SolFinal.progC11Fmt
