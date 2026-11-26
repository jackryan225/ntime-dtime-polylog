import P1ChkFinal.C13linkFmtTarget
import OAI.Computability.IntegerMultiplication.Carry.Small

namespace P1ChkFinal.SolFinal.C13lFmt

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open scoped Classical

abbrev LinkDatum := (Word × Word) × Word

private theorem cut_eq_bin (w : Word) : Carry.cut w = bin (Bits.value w) := by
  rw [bin_eq_bits]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [Carry.cuts, ih, Bits.value_cons]
    by_cases h : Bits.value w = 0
    · rw [h]
      cases a <;> simp [Carry.tack]
    · have ne : (Nat.bits (Bits.value w)).isEmpty = false := by
        obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
        rw [hn, ← bin_eq_bits, bin]
        rfl
      have hd : Bits.digit a = a.toNat := by cases a <;> rfl
      rw [Carry.tack, ne, Bool.false_and, Bool.cond_false, hd, Nat.add_comm, ← Nat.bit_val,
        Nat.bits_append_bit _ _ (fun e => False.elim (h e))]

private def chainReq (p : Req × Word) : Req :=
  (Carry.cut (requestAt p).1, p.1.2)

private theorem poly_chainReq : Poly chainReq := by
  exact (poly_requestAt.fstCompose.compose Carry.polyCut).pair
    (show Easy (fun p : Req × Word => p.1.2) by fun_prop).poly

private def formatRequests (f : List Word × Word) : List Req :=
  let chain := (wordAt 8 f.1, wordAt 9 f.1)
  let bound := minus (wordAt 11 f.1, [true])
  bif less (f.2, bound) then [chainReq (chain, f.2), chainReq (chain, Bits.add (f.2, [true]))]
  else []

private theorem poly_formatRequests : Poly formatRequests := by
  let V := List Word × Word
  have e (i : ℕ) : Easy (fun f : V => wordAt i f.1) := Easy.fst.compose (easy_wordAt i)
  have chain : Easy (fun f : V => (wordAt 8 f.1, wordAt 9 f.1)) := (e 8).pair (e 9)
  have next : Easy (fun f : V => Bits.add (f.2, [true])) := Bits.easy_add (Easy.snd.pair (Easy.const _))
  have bound : Easy (fun f : V => minus (wordAt 11 f.1, [true])) :=
    ((e 11).pair (Easy.const _)).compose easy_minus
  have valid := (Easy.snd.pair bound).compose easy_less
  have r0 := (chain.pair Easy.snd).poly.compose poly_chainReq
  have r1 := (chain.pair next).poly.compose poly_chainReq
  have empty : Code.Poly (fun _ : V => ([] : List Req)) := Code.Poly.const _
  exact valid.poly.choose
    ((r0.pair ((r1.pair empty).compose Code.Poly.cons)).compose Code.Poly.cons) empty

private theorem formatRequests_correct (dims : ℕ → Dims) (z : LinkDatum) :
    formatRequests (fmtAt dims z.1) = rqLink dims z := by
  let D := dims (P1Batch.bval z.1.1)
  let o := D.off D.secChain
  let w := D.width D.secChain
  have ho : wordAt 8 (fmt D) = o.bits := rfl
  have hw : wordAt 9 (fmt D) = w.bits := rfl
  have hp : wordAt 11 (fmt D) = D.chainLen.bits := rfl
  have he (i : Word) : chainReq ((o.bits, w.bits), i) = fieldReq D D.secChain (Bits.value i) := by
    simp only [chainReq, cut_eq_bin, requestAt_value, value_bits, fieldReq, bin_eq_bits, o, w]
  have hone : Bits.value ([true] : Word) = 1 := rfl
  have hv : Bits.value z.1.2 = P1Batch.bval z.1.2 := (P1Batch.bval_eq_value _).symm
  simp only [formatRequests, fmtAt, ← show D = dims (P1Batch.bval z.1.1) from rfl, ho, hw, hp,
    less_eq, minus_eq, value_bits, hone, he, Bits.add_val, hv, rqLink, finP]
  by_cases h : P1Batch.bval z.1.2 < D.chainLen - 1
  · simp only [h, decide_true, Bool.cond_true, ite_true]
  · simp only [h, decide_false, Bool.cond_false, ite_false]

private theorem poly_requests (dims : ℕ → Dims) (hf : FmtHyp dims) :
    Poly (fun z : LinkDatum => (rqLink dims z, z)) := by
  simpa only [formatRequests_correct] using
    (((Easy.fst (X := Index) (Y := Word)).poly.compose (poly_fmtAt dims hf)).compose
      poly_formatRequests).pair Poly.identity

private def defaultAt {A : Type} (d : A) (i : ℕ) (l : List A) : A :=
  l[i]?.getD d

private theorem easy_defaultAt {A : Type} [Codec A] (d : A) (i : ℕ) :
    Easy (defaultAt d i) := by
  induction i with
  | zero =>
    convert Easy.listCase d (Easy.fst (X := A) (Y := List A)) using 1
    funext l
    cases l <;> rfl
  | succ i ih =>
    convert Easy.listCase d (Easy.snd.compose ih) using 1
    funext l
    cases l <;> rfl

private theorem easy_lengthEq {A : Type} [Codec A] (n : ℕ) :
    Easy (fun l : List A => decide (l.length = n)) := by
  induction n with
  | zero =>
    convert Carry.vacant A using 1
    funext l
    cases l <;> rfl
  | succ n ih =>
    convert Easy.listCase false (Easy.snd.compose ih) using 1
    funext l
    cases l with
    | nil => exact decide_eq_false (Nat.succ_ne_zero n).symm
    | cons a l => simp only [List.length_cons, Nat.succ.injEq]

variable {F : Type} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

private theorem decide_add_zmod2 (v w : ZMod 2) :
    decide (v + w = 1) = (decide (v = 1) ^^ decide (w = 1)) := by
  revert v w
  decide

private theorem easy_linkVal (b : Basis (Fin Dd) (ZMod 2) F) (j j' : Fin Dd) :
    Easy (fun cw : Word => decide (linkVal b cw j j' = 1)) := by
  let term (cw : Word) (m : Fin Dd) : ZMod 2 :=
    (if cw.getD m false then 1 else 0) * P1Count.mulEntry b (b j) m j'
  have hterm (m : Fin Dd) : Easy (fun cw : Word => decide (term cw m = 1)) := by
    have hbit : Easy (fun cw : Word => cw.getD m false) := by
      refine Task.conform (easy_defaultAt false m.val) (fun _ => rfl) (fun _ => rfl)
        (fun cw => congrArg send ?_)
      simp only [defaultAt, List.getD_eq_getElem?_getD]
    exact hbit.compose (Easy.finite (fun bit : Bool =>
      decide ((if bit then 1 else 0) * P1Count.mulEntry b (b j) m j' = 1)))
  have hsum (s : Finset (Fin Dd)) :
      Easy (fun cw : Word => decide ((∑ m ∈ s, term cw m) = 1)) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun cw : Word => decide ((∑ m ∈ (∅ : Finset (Fin Dd)), term cw m) = 1)) =
          (fun _ => false) := by
        funext cw
        rw [Finset.sum_empty]
        exact decide_eq_false (by decide)
      rw [he]
      exact Easy.const false
    | insert m s hm ih =>
      simpa only [Finset.sum_insert hm, decide_add_zmod2] using
        ((hterm m).pair ih).compose (Easy.finite (fun p : Bool × Bool => p.1 ^^ p.2))
  have he : (fun cw : Word => decide (linkVal b cw j j' = 1)) =
      (fun cw => decide ((∑ m ∈ (Finset.univ : Finset (Fin Dd)), term cw m) = 1)) := by
    funext cw
    rw [decide_eq_decide]
    exact Iff.rfl
  rw [he]
  exact hsum Finset.univ

private noncomputable def testFields (b : Basis (Fin Dd) (ZMod 2) F) (p : Word × Word × Word) : Bool :=
  (Finset.univ.toList : List (Fin Dd)).any fun j =>
    numEq (p.1, bin j.val) &&
      (Finset.univ.toList : List (Fin Dd)).any fun j' =>
        numEq (p.2.1, bin j'.val) && decide (linkVal b p.2.2 j j' = 1)

private theorem easy_testFields (b : Basis (Fin Dd) (ZMod 2) F) : Easy (testFields b) := by
  apply easy_any_fixed
  intro j
  have e0 : Easy (fun p : Word × Word × Word => numEq (p.1, bin j.val)) :=
    (Easy.fst.pair (Easy.const _)).compose easy_numEq
  apply (e0.pair ?_).compose easy_band
  apply easy_any_fixed
  intro j'
  have e1 : Easy (fun p : Word × Word × Word => numEq (p.2.1, bin j'.val)) :=
    ((Easy.snd.compose Easy.fst).pair (Easy.const _)).compose easy_numEq
  exact (e1.pair ((Easy.snd.compose Easy.snd).compose (easy_linkVal b j j'))).compose easy_band

private theorem testFields_correct (b : Basis (Fin Dd) (ZMod 2) F) (f g cw : Word) :
    testFields b (f, g, cw) = decide (∃ (h : bitsVal f < Dd) (h' : bitsVal g < Dd),
      linkVal b cw ⟨bitsVal f, h⟩ ⟨bitsVal g, h'⟩ = 1) := by
  rw [Bool.eq_iff_iff]
  simp only [testFields, List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and,
    Bool.and_eq_true, numEq_eq, decide_eq_true_eq, value_bin, value_field]
  constructor
  · rintro ⟨⟨j, hj⟩, h0, ⟨j', hj'⟩, h1, hval⟩
    change Bits.value f = j at h0
    change Bits.value g = j' at h1
    subst j
    subst j'
    exact ⟨hj, hj', hval⟩
  · rintro ⟨h, h', hval⟩
    exact ⟨⟨Bits.value f, h⟩, rfl, ⟨Bits.value g, h'⟩, rfl, hval⟩

private theorem easy_decLink (b : Basis (Fin Dd) (ZMod 2) F) : Easy (decLink b) := by
  let X := LinkDatum × List Word
  have good : Easy (fun q : X => decide (q.2.length = 2)) := Easy.snd.compose (easy_lengthEq 2)
  have f (i : ℕ) : Easy (fun q : X => wordAt i q.2) := Easy.snd.compose (easy_wordAt i)
  have coord : Easy (fun q : X => q.1.2) := by fun_prop
  have E := easy_choose good (((f 0).pair ((f 1).pair coord)).compose (easy_testFields b)) (Easy.const true)
  refine Task.conform E (fun _ => rfl) (fun _ => rfl) (fun ⟨z, fs⟩ => congrArg send ?_)
  rcases fs with _ | ⟨f, _ | ⟨g, _ | ⟨h, fs⟩⟩⟩
  · rfl
  · rfl
  · exact testFields_correct b f g z.2
  · simp only [List.length_cons, Nat.succ.injEq, Nat.succ_ne_zero, decide_false, Bool.cond_false, decLink]

/-- The request list has zero or two entries. Each slice clips to the available witness bits. -/
private def fetchLink (i : List Req × Word) : List Word :=
  bif i.1.isEmpty then [] else
    [slice (defaultAt ([], []) 0 i.1, i.2), slice (defaultAt ([], []) 1 i.1, i.2)]

private theorem easy_fetchLink (hl : SolFinal.LenHyp) : Easy fetchLink := by
  have req (n : ℕ) : Easy (fun i : List Req × Word => (defaultAt ([], []) n i.1, i.2)) :=
    (Easy.fst.compose (easy_defaultAt ([], []) n)).pair Easy.snd
  have field (n : ℕ) := (req n).compose (computes_slice hl)
  exact easy_choose (Easy.fst.compose (Carry.vacant Req)) (Easy.const [])
    (((field 0).pair (((field 1).pair (Easy.const [])).compose Easy.cons)).compose Easy.cons)

private theorem fetchLink_correct (dims : ℕ → Dims) (z : LinkDatum) (u : Word) :
    fetchLink (rqLink dims z, u) = (rqLink dims z).map (P1Batch.fetch u) := by
  unfold rqLink
  split_ifs
  · simp only [fetchLink, List.isEmpty_cons, Bool.cond_false, defaultAt, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.map_cons, List.map_nil, slice, P1Batch.fetch,
      P1Batch.bval_eq_value]
  · rfl

private theorem cost_bound (X U R B D E t a C P : ℕ) (hB : B ≤ P) (ht : t + a ≤ C * P) :
    (2 * X + 1 + (2 * U + 1 + (2 * R + 1) + 1) + 1) + E + (2 * D + 1 + X) +
      (2 * D + 1 + (2 * B + 1 + (2 * U + 1 + (2 * R + 1) + 1) + 1) + 1) +
      t + (a + (2 * U + 1) + 1) + 1 ≤ (C + 4 * D + 25) * (X + U + R + P + E + 1) := by
  have hC : C * P ≤ C * (X + U + R + P + E + 1) := Nat.mul_le_mul_left _ (by omega)
  have hD : 4 * D ≤ 4 * D * (X + U + R + P + E + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [Nat.add_mul, Nat.add_mul]
  omega

set_option maxHeartbeats 1200000 in
private theorem program : C13linkFmtTarget := by
  intro F _ _ Dd b dims Wof M K βW _ hl hf hW
  let cw (p : QDom M K) := coords b (Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))
  let datum (p : QDom M K) : LinkDatum := ((bin p.val.1.length, p.val.2.2), cw p)
  let requests (p : QDom M K) := (rqLink dims (datum p), datum p)
  have hcw (p : QDom M K) : (cw p).length = Dd := by simp only [cw, coords, List.length_ofFn]
  have hlog (p : QDom M K) : (bin p.val.1.length).length ≤ Nat.log 2 (p.val.1.length + 1) + 1 :=
    (length_bin_log _).trans (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 1)
  have hdatum : Dom smallSize (fun p => size (datum p)) := by
    refine ⟨1, 2 * Dd + 10, fun p => ?_⟩
    simp only [size_prod, size_listBool, datum, hcw, smallSize, pow_one]
    have h := hlog p
    nlinarith
  have T0 := (Easy.clone (X := Qry)).on (fun p : QDom M K => p.val)
  have TW := hW.left (fun p : QDom M K => send p.val)
  have TL := (((lenHyp_bin hl).on (fun p : QDom M K => p.val.1)).left (fun p => send p.val.2)).right
    (fun p => send (cw p))
  have E1 : Easy (fun w : Word × (Word × (Word × Word)) => (((w.2.1, w.2.2.2), w.1), w.2.2.1)) := by
    fun_prop
  have TR := E1.on (fun p : QDom M K => (cw p, (bin p.val.1.length, p.val.2)))
  obtain ⟨t, ht, TQ⟩ := (poly_requests dims hf).on (q := datum) hdatum
  have hrequests : Dom smallSize (fun p => size (requests p)) :=
    ((poly_requests dims hf).length.map datum).sub hdatum
  have EF : Easy (fun i : (List Req × LinkDatum) × Word => (i.1.2, fetchLink (i.1.1, i.2))) :=
    (show Easy (fun i : (List Req × LinkDatum) × Word => i.1.2) by fun_prop).pair
      ((show Easy (fun i : (List Req × LinkDatum) × Word => (i.1.1, i.2)) by fun_prop).compose
        (easy_fetchLink (lenHyp_bin hl)))
  have TD := (EF.compose (easy_decLink b)).on (fun p : QDom M K => (requests p, p.val.2.1))
  have T := ((((T0.compose TW).compose TL).compose TR).compose (TQ.left (fun p => send p.val.2.1))).compose TD
  obtain ⟨k, C, hC⟩ := ht.add hrequests
  refine ⟨k + 1, (T.bound (C + 4 * Dd + 25) (fun p => ?_)).conform (fun _ => rfl) (fun _ => rfl)
    (fun p => congrArg send ?_)⟩
  · have h := hC p
    have hB := hlog p
    let L := p.val.1.length + p.val.2.1.length + p.val.2.2.length
    let S := Nat.log 2 (p.val.1.length + 1) + p.val.2.2.length + 1
    have hS : 1 ≤ S := by dsimp only [S]; omega
    have hS1 : S ≤ S ^ (k + 1) := by
      calc S = S ^ 1 := (pow_one S).symm
        _ ≤ S ^ (k + 1) := Nat.pow_le_pow_right hS (by omega)
    have hS2 : S ^ k ≤ S ^ (k + 1) := Nat.pow_le_pow_right hS (by omega)
    have hT : t p + size (requests p) ≤ C * S ^ (k + 1) := h.trans (Nat.mul_le_mul_left _ hS2)
    have hD : (bin p.val.1.length).length ≤ S ^ (k + 1) := by dsimp only [S] at *; omega
    change _ ≤ (C + 4 * Dd + 25) * (L + S ^ (k + 1) + βW p + 1)
    have hc : (send (cw p)).count = 2 * Dd + 1 := by rw [← hcw p]; exact size_listBool (cw p)
    simp only [size_prod (requests p, p.val.2.1), size_prod p.val, size_prod p.val.2,
      size_prod (cw p, (bin p.val.1.length, p.val.2)), size_prod (bin p.val.1.length, p.val.2),
      size_listBool, hcw, hc]
    exact cost_bound _ _ _ _ _ _ _ _ _ _ hD hT
  · change decLink b (datum p, fetchLink ((requests p).1, p.val.2.1)) = _
    rw [show (requests p).1 = rqLink dims (datum p) from rfl, fetchLink_correct]
    exact (hckLink b dims Wof p.val.1 p.val.2.1 p.val.2.2).symm

end P1ChkFinal.SolFinal.C13lFmt

theorem P1ChkFinal.SolFinal.progC13linkFmt : P1ChkFinal.C13linkFmtTarget :=
  P1ChkFinal.SolFinal.C13lFmt.program

example : P1ChkFinal.C13linkFmtTarget := P1ChkFinal.SolFinal.progC13linkFmt

#print axioms P1ChkFinal.SolFinal.progC13linkFmt
