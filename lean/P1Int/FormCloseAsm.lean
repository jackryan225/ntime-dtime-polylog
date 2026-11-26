import P1Int.FormCloseDefs
import P1Int.FormLev

noncomputable section

namespace P1Int.P11.SolFormClose

open P1Wit P1Wit.SolWitfill P1ChkFinal

private def unflatten {n : ℕ} (w : Fin n → ℕ) (bits : List Bool) :
    (i : Fin n) → Fin (w i) → Bool :=
  fun i j => bits.getD (widthPrefix (atIndex w) i.val + j.val) false

private theorem cat_unflatten {n : ℕ} (w : Fin n → ℕ) (bits : List Bool) (k : ℕ)
    (hk : k ≤ n) (hlen : widthPrefix (atIndex w) k ≤ bits.length) :
    P1Wit.cat (arcBits (unflatten w bits)) k = bits.take (widthPrefix (atIndex w) k) := by
  induction k with
  | zero =>
    simp only [P1Wit.cat, widthPrefix, Finset.range_zero, Finset.sum_empty, List.take_zero]
  | succ k ih =>
    let i : Fin n := ⟨k, hk⟩
    have hs : widthPrefix (atIndex w) (k + 1) = widthPrefix (atIndex w) k + w i := by
      exact (Finset.sum_range_succ (atIndex w) k).trans
        (congrArg (widthPrefix (atIndex w) k + ·) (atIndex_fin w i))
    have hslice : arcBits (unflatten w bits) k =
        (bits.drop (widthPrefix (atIndex w) k)).take (w i) := by
      change arcBits (unflatten w bits) i.val = _
      rw [arcBits_fin]
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_take, List.length_drop]
        have hsize : w i ≤ bits.length - widthPrefix (atIndex w) k := by omega
        exact (Nat.min_eq_left hsize).symm
      · intro j hj₁ hj₂
        have hj : j < w i := by simpa only [List.length_ofFn] using hj₁
        have hj' : widthPrefix (atIndex w) i.val + j < bits.length := by
          change widthPrefix (atIndex w) k + j < bits.length
          omega
        rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
        exact getD_false_eq _ _ hj'
    rw [P1Wit.cat, ih (by omega) (by omega), hslice, hs, List.take_add]

private theorem flatten_unflatten {n : ℕ} (w : Fin n → ℕ) (bits : List Bool)
    (hlen : bits.length = widthPrefix (atIndex w) n) :
    flatten (unflatten w bits) = bits := by
  rw [flatten, cat_unflatten w bits n le_rfl hlen.ge, ← hlen, List.take_length]

private theorem widthPrefix_blocks (w : ℕ → ℕ) (A y : ℕ) :
    widthPrefix w (y * A) = pre (fun b => pre (fun t => w (b * A + t)) A) y := by
  induction y with
  | zero => simp only [Nat.zero_mul, widthPrefix, Finset.range_zero, Finset.sum_empty, pre_zero]
  | succ y ih =>
    rw [Nat.succ_mul, pre_succ, ← ih]
    exact Finset.sum_range_add w (y * A) A

private theorem tuplePayload_length_of_width {F : Type*} {D : Dims} {C : P1Count.CountData F}
    {d : ℕ} (R : TupleRecords D C d) (t : C.Tup d) (bits : List Bool)
    (hw : ∀ i < D.count (secLev D.top .width),
      readField D bits (secLev D.top .width) i = (ofTuple R t).val D (secLev D.top .width) i) :
    (tuplePayload R t).length = pre (wsOf D bits) (finN D) := by
  have hArcs : FinalArcs D = finN D * finArcs D := Nat.mul_assoc _ _ _
  have hread : pre (wsOf D bits) (finN D) =
      widthPrefix (readField D bits (secLev D.top .width)) (FinalArcs D) := by
    rw [hArcs, widthPrefix_blocks]
    unfold pre
    apply Finset.sum_congr rfl
    intro y _
    unfold wsOf pre
    apply Finset.sum_congr rfl
    intro j _
    unfold arcW rdWidth finArcs
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, div_mul_add_mod]
  rw [tuplePayload_length, hread, widthPrefix, widthPrefix]
  apply Finset.sum_congr rfl
  intro i hi
  have hcount : i < (D.lv D.top).count .width := Finset.mem_range.mp hi
  have hsec : i < D.count (secLev D.top .width) := by
    rw [D.count_secLev .width le_rfl]
    exact hcount
  rw [hw i hsec]
  simp only [Fields.val, D.kind_secLev .width le_rfl, ofTuple_levVal R t _ _ _ hcount,
    levelAt, dite_eq_left (Nat.lt_succ_self D.top), LevelRecords.code, finalLevel, Fin.last]

private theorem ofTuple_val_replace {F : Type*} {D : Dims} {C : P1Count.CountData F}
    {d : ℕ} (R : TupleRecords D C d) (t : C.Tup d)
    (z : C.Pay t.1 t.2.1) (j : Fin (C.P t.1 t.2.1 + 1) → Fin d)
    {s : ℕ} (hs : s ≠ D.secChain) (i : ℕ) :
    (ofTuple R t).val D s i = (ofTuple R ⟨t.1, t.2.1, z, j⟩).val D s i := by
  cases hk : D.kind s
  case chain => exact (hs (D.eq_of_kind_chain hk)).elim
  case lev ℓ kk =>
    cases kk <;> simp only [Fields.val, hk, Fields.levVal, ofTuple]
  all_goals simp only [Fields.val, hk, ofTuple]

private theorem payload_tail_false (D : Dims) {m n : ℕ} (u : Fin m → Bool)
    (hz : ∀ c ∈ (rdPayload D (List.ofFn u)).drop n, c = false)
    (i : Fin m) (hi : D.fixedLen + n ≤ i.val) : u i = false := by
  let j := i.val - (D.fixedLen + n)
  have hj : D.fixedLen + n + j = i.val := Nat.add_sub_of_le hi
  have hdrop : j < ((List.ofFn u).drop (D.fixedLen + n)).length := by
    simp only [List.length_drop, List.length_ofFn]
    have hi' := i.isLt
    omega
  simp only [rdPayload, List.drop_drop] at hz
  have h := hz _ (List.getElem_mem hdrop)
  rw [List.getElem_drop, List.getElem_ofFn] at h
  exact Eq.subst (motive := fun q => u q = false) (Fin.ext hj) h

private def castChain {p q d : ℕ} (h : p = q) (j : Fin (p + 1) → Fin d) :
    Fin (q + 1) → Fin d :=
  fun i => j (Fin.cast (congrArg (· + 1) h.symm) i)

private theorem chainOK_cast {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {p q d : ℕ}
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
    (h : p = q) (W : ℕ → F) (W' : Fin q → F) (j : Fin (p + 1) → Fin d)
    (hw : ∀ i : Fin q, W i = W' i)
    (hj : P1Count.ChainOK bs l (fun i : Fin p => W i) j) :
    P1Count.ChainOK bs l W' (castChain h j) := by
  subst q
  rw [← funext hw]
  exact hj

private theorem chain_count (D : Dims) {q : ℕ} (hq : q + 1 ≤ D.chainLen)
    (hp : finP D = q) : D.count D.secChain = q + 1 := by
  simp only [Dims.count, D.kind_chain]
  unfold finP at hp
  omega

private theorem chain_val {F : Type*} {D : Dims} {C : P1Count.CountData F}
    {d : ℕ} (R : TupleRecords D C d) (t : C.Tup d) (z : C.Pay t.1 t.2.1)
    (hp : finP D = C.P t.1 t.2.1) (j : Fin (finP D + 1) → Fin d)
    (bits : List Bool) (hj : ∀ v : Fin (finP D + 1), (j v : ℕ) = rdChain D bits v)
    (i : ℕ) (hi : i < D.count D.secChain) :
    (dec D bits).val D D.secChain i = (ofTuple R ⟨t.1, t.2.1, z, castChain hp j⟩).val D D.secChain i := by
  have hi' : i < C.P t.1 t.2.1 + 1 :=
    (chain_count D (R.chain_fits_len t.1 t.2.1) hp) ▸ hi
  let v : Fin (C.P t.1 t.2.1 + 1) := ⟨i, hi'⟩
  rw [dec_val D bits hi]
  simp only [Fields.val, D.kind_chain, ofTuple]
  change rdChain D bits i = finValue (castChain hp j) v.val
  rw [finValue_fin]
  exact (hj (Fin.cast (congrArg (· + 1) hp.symm) v)).symm

private theorem tuplePayload_replace {F : Type*} {D : Dims} {C : P1Count.CountData F}
    {d : ℕ} (R : TupleRecords D C d) (t : C.Tup d) (bits : List Bool)
    (hlen : bits.length = (tuplePayload R t).length)
    (j : Fin (C.P t.1 t.2.1 + 1) → Fin d) :
    tuplePayload R
      ⟨t.1, t.2.1, (R.payload t.1 t.2.1).symm
        (unflatten (fun i => ((R.level t.1 t.2.1 (finalLevel D)).width i).val) bits), j⟩ = bits := by
  let z := unflatten (fun i => ((R.level t.1 t.2.1 (finalLevel D)).width i).val) bits
  change flatten ((R.payload t.1 t.2.1) ((R.payload t.1 t.2.1).symm z)) = bits
  exact (congrArg flatten ((R.payload t.1 t.2.1).apply_symm_apply z)).trans
    (flatten_unflatten _ bits (hlen.trans (tuplePayload_length R t)))

end P1Int.P11.SolFormClose

open P1Int.P11 P1Int.P11.SolFormClose
open P1Wit P1Wit.SolWitfill P1ChkFinal
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.formClose_asm {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.FormCloseAsmTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit hC14Close bs l Wof hW hP cnt u t hu ht
  let D := fixedDims Bt V a b x d bigBias termBias
  let C := fixedCD Bt κ hκ V a b x
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let G := fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof
  let w := List.ofFn u
  change ∀ j < 7 + 2 * D.top, G.P D.top j u at hu
  have hDir : G.dir u := Eq.mp (G.P_one D.top u) (hu 1 (by omega))
  have hC14 : G.c14 u := Eq.mp (G.P_two D.top u) (hu 2 (by omega))
  have hC12 : G.c12 u := Eq.mp (G.P_c12 D.top u) (hu (5 + 2 * D.top) (by omega))
  have hC13 : G.c13 u := Eq.mp (G.P_c13 D.top u) (hu (6 + 2 * D.top) (by omega))
  have hTrit : P1Wit.secTrit < D.nSec := by
    change 0 < 7 + 12 * (D.top + 1)
    omega
  have hTritChain : P1Wit.secTrit ≠ D.secChain := by
    change 0 ≠ 6 + 12 * (D.top + 1)
    omega
  have hUnowned : C.unowned t.1 = 0 := hC14Close u t hDir hC14 (ht _ hTrit hTritChain)
  have hWidthChain : secLev D.top .width ≠ D.secChain := by
    intro h
    have hKind := congrArg D.kind h
    rw [D.kind_secLev .width le_rfl, D.kind_chain] at hKind
    cases hKind
  have hWidths : ∀ i < D.count (secLev D.top .width),
      readField D w (secLev D.top .width) i = (ofTuple R t).val D (secLev D.top .width) i :=
    fun i hi => (dec_val D w hi).symm.trans (ht _ (D.secLev_lt_nSec .width le_rfl) hWidthChain i hi)
  let n := (tuplePayload R t).length
  have hLen : n = pre (wsOf D w) (finN D) := tuplePayload_length_of_width R t w hWidths
  have hEnough : n ≤ (rdPayload D w).length := hLen.trans_le hC12.1
  have hTail : ∀ c ∈ (rdPayload D w).drop n, c = false :=
    Eq.subst (motive := fun len => ∀ c ∈ (rdPayload D w).drop len, c = false) hLen.symm hC12.2
  have hp : finP D = C.P t.1 t.2.1 := hP t.1 t.2.1
  let bits := (rdPayload D w).take n
  have hBits : bits.length = n := by
    change ((rdPayload D w).take n).length = n
    rw [List.length_take, Nat.min_eq_left hEnough]
  change ∃ j : Fin (finP D + 1) → Fin d,
    (∀ v : Fin (finP D + 1), (j v : ℕ) = rdChain D w v) ∧
      P1Count.ChainOK bs l (fun i : Fin (finP D) => Wof x w i) j at hC13
  exact Exists.elim hC13 fun j hj => by
    let z := (R.payload t.1 t.2.1).symm
      (unflatten (fun i => ((R.level t.1 t.2.1 (finalLevel D)).width i).val) bits)
    let t' : C.Tup d := ⟨t.1, t.2.1, z, castChain hp j⟩
    have hPayload : tuplePayload R t' = bits := tuplePayload_replace R t bits hBits (castChain hp j)
    have hn' : (tuplePayload R t').length = n := (congrArg List.length hPayload).trans hBits
    have hSections : ∀ s < D.nSec, ∀ i < D.count s,
        (dec D w).val D s i = (ofTuple R t').val D s i := by
      intro s hs i hi
      by_cases h : s = D.secChain
      · subst s
        exact chain_val R t z hp j w hj.1 i hi
      · exact (ht s hs h i hi).trans (ofTuple_val_replace R t z (castChain hp j) h i)
    have hTake : (rdPayload D w).take (tuplePayload R t').length = tuplePayload R t' :=
      (congrArg ((rdPayload D w).take) hn').trans hPayload.symm
    have hZeros : ∀ i : Fin (fixedM Bt a b x), D.fixedLen + (tuplePayload R t').length ≤ i.val → u i = false :=
      Eq.subst (motive := fun len => ∀ i : Fin (fixedM Bt a b x), D.fixedLen + len ≤ i.val → u i = false)
        hn'.symm (payload_tail_false D u hTail)
    let enc := fixedEnc Bt κ hκ V a b x d bigBias termBias H
    have hEnc : enc t' = u :=
      encOfAgree Bt κ hκ V a b x d bigBias termBias H hfit u t' hSections hTake hZeros
    have hEval (i : Fin (C.P t.1 t.2.1)) : Wof x w i = C.W t.1 t.2.1 z i :=
      (congrArg (fun v => Wof x (List.ofFn v) i) hEnc.symm).trans (hW t' i)
    have hChain : P1Count.ChainOK bs l (C.W t.1 t.2.1 z) (castChain hp j) :=
      chainOK_cast bs l hp (Wof x w) (C.W t.1 t.2.1 z) j hEval hj.2
    exact ⟨t', ⟨hUnowned, hChain⟩, hEnc⟩

#print axioms P1Int.P11.formClose_asm
