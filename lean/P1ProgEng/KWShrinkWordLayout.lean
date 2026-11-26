import P1ProgEng.KWShrinkWords
import P1ProgEng.KWShrinkC10Primitives
import P1P5.Generic

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code Carry Staff
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.NetworkKernel
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

private def addWords (p : Unit × Bits.Word × Bits.Word) : Bits.Word := Bits.add p.2

private def sumWords (xs : List Bits.Word) : Bits.Word := trek addWords (xs,(),[])

private theorem sumWords_poly : Poly sumWords := by
  have ha : Poly addWords := Easy.snd.poly.compose swift
  unfold sumWords
  apply Code.Poly.compose (show Poly (fun xs : List Bits.Word => (xs,(),([] : Bits.Word))) from by fun_prop)
  refine polyTrek _ ha 2 ?_
  intro _ x y
  simp only [addWords, Bits.size_word, Bits.add_length]
  omega

private theorem sumWords_value (xs : List Bits.Word) :
    Bits.value (sumWords xs) = (xs.map Bits.value).sum := by
  have aux : ∀ (xs : List Bits.Word) (a : Bits.Word),
      Bits.value (trek addWords (xs,(),a)) = Bits.value a + (xs.map Bits.value).sum := by
    intro xs a
    induction xs generalizing a with
    | nil => simp [trek]
    | cons x xs ih =>
      change Bits.value (trek addWords (xs,(),Bits.add (a,x))) = _
      rw [ih, Bits.add_val]
      simp only [List.map_cons, List.sum_cons, Nat.add_assoc]
  simpa only [sumWords, Bits.value_nil, Nat.zero_add] using aux xs []

/-- Binary accumulation of widths. Intermediate numbers are represented in
binary even when a malformed table contains arbitrarily large widths. -/
@[fun_prop] theorem sum_poly : Poly (List.sum : List ℕ → ℕ) := by
  let rg : Strip.Regime (List ℕ) := ⟨size, send, Dom.base _⟩
  have hword : Poly (fun xs : List ℕ => sumWords (xs.map binary)) :=
    (Code.Poly.maps binary (Code.Poly.identity : Poly (id : ℕ → ℕ))).compose sumWords_poly
  have hf : Figure rg List.sum := ⟨_, hword, fun xs => by
    rw [sumWords_value, List.map_map]
    have he : Bits.value ∘ binary = id := funext value_binary
    rw [he, List.map_id]⟩
  exact hf.write ((hf.added (Figure.natural 1)).short_log)

def widthPrefix (p : List ℕ × ℕ) : ℕ := (p.1.take p.2).sum

@[fun_prop] theorem widthPrefix_poly : Poly widthPrefix :=
  (P1ProgEng.SolKWR.poly_take Easy.snd.poly Easy.fst.poly).compose sum_poly

theorem widthPrefix_ofFn {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    widthPrefix (List.ofFn w, i.val) = ∑ j : Fin i.val, w (Fin.castLE i.isLt.le j) := by
  unfold widthPrefix
  rw [← Fin.ofFn_take_eq_take_ofFn i.isLt.le, List.sum_ofFn]
  rfl

theorem read_flatten_at {A : Type} (fallback : A) (rows : List (List A))
    (i : Fin rows.length) (j : Fin rows[i.val].length) :
    C10.read fallback rows.flatten ((rows.take i.val).flatten.length + j.val) = rows[i.val][j.val] := by
  have ht := List.take_append_drop (i.val + 1) rows
  rw [List.take_succ_eq_append_getElem i.isLt] at ht
  have he := congrArg List.flatten ht
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc] at he
  unfold C10.read
  rw [← he, List.getElem?_append_right (by omega)]
  rw [Nat.add_sub_cancel_left, List.getElem?_append_left j.isLt, List.getElem?_eq_getElem j.isLt]
  rfl

theorem flatten_ofFn_lengths {n : ℕ} {A : Type} (rows : Fin n → List A) :
    (List.ofFn rows).flatten.length = ∑ i, (rows i).length := by
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem read_flatten_ofFn_at {n : ℕ} {A : Type} (fallback : A) (rows : Fin n → List A)
    (i : Fin n) (j : Fin (rows i).length) :
    C10.read fallback (List.ofFn rows).flatten
      ((∑ k : Fin i.val, (rows (Fin.castLE i.isLt.le k)).length) + j.val) =
        (rows i)[j.val] := by
  let P := List.ofFn rows
  have ii : i.val < P.length := by simpa [P] using i.isLt
  have hj : j.val < P[i.val].length := by simpa [P] using j.isLt
  have hout := read_flatten_at fallback P ⟨i.val,ii⟩ ⟨j.val,hj⟩
  have hlen : (P.take i.val).flatten.length =
      ∑ k : Fin i.val, (rows (Fin.castLE i.isLt.le k)).length := by
    dsimp only [P]
    rw [← Fin.ofFn_take_eq_take_ofFn i.isLt.le, flatten_ofFn_lengths]
    rfl
  rw [hlen] at hout
  simpa only [P, List.getElem_ofFn, Fin.eta] using hout

theorem read_ofFn {A : Type} (d : A) {n : ℕ} (f : Fin n → A) (i : Fin n) :
    C10.read d (List.ofFn f) i.val = f i := by
  simp only [C10.read, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

theorem slice_of_reads {A : Type} (d : A) (xs : List A) (off n : ℕ)
    (f : Fin n → A) (hbound : off + n ≤ xs.length)
    (hread : ∀ i : Fin n, C10.read d xs (off + i.val) = f i) :
    (xs.drop off).take n = List.ofFn f := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn, min_eq_left (by omega : n ≤ xs.length - off)]
  · intro i hi hj
    have h : i < n := by simpa only [List.length_ofFn] using hj
    have hi' : off + i < xs.length := by omega
    have hr := hread ⟨i,h⟩
    simp only [C10.read, List.getElem?_eq_getElem hi', Option.getD_some] at hr
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    exact hr

theorem sum_prefix {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    (∑ j : Fin i.val, w (Fin.castLE i.isLt.le j)) =
      ∑ j : Fin n, if j.val < i.val then w j else 0 := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => Fin.castLE i.isLt.le j)
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j _ k _ h
    exact Fin.ext (congrArg (fun q : Fin n => q.val) h)
  · intro j hj
    exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · exact fun _ _ => rfl

theorem read_flatten_point {A : Type} {n w : ℕ} (d : A) (rows : Fin n → List A)
    (i : Fin n) (f : Fin w → A) (hf : rows i = List.ofFn f) (j : Fin w) :
    C10.read d (List.ofFn rows).flatten
      ((∑ k : Fin n, if k.val < i.val then (rows k).length else 0) + j.val) = f j := by
  rw [← sum_prefix (fun k => (rows k).length) i]
  have hj : j.val < (rows i).length := by rw [hf, List.length_ofFn]; exact j.isLt
  have h := read_flatten_ofFn_at d rows i ⟨j.val,hj⟩
  simpa only [hf,List.getElem_ofFn,Fin.eta] using h

theorem widthPrefix_equiv {A : Type} [Fintype A] {n : ℕ} (e : A ≃ Fin n)
    (w : A → ℕ) (f : Fin n → ℕ) (he : ∀ a, f (e a) = w a) (x : A) :
    widthPrefix (List.ofFn f, (e x).val) = ∑ a, if e a < e x then w a else 0 := by
  rw [widthPrefix_ofFn]
  refine (sum_prefix f (e x)).trans ?_
  exact Fintype.sum_equiv e.symm _ _ (fun i => by
    have hi := he (e.symm i)
    rw [e.apply_symm_apply] at hi
    simp only [e.apply_symm_apply, hi]
    rfl)

theorem sum_by_injective {A D : Type} [Fintype A] [Fintype D] (f : A → D)
    (hf : Function.Injective f) (w : D → ℕ) (hz : ∀ j, (∀ i, f i ≠ j) → w j = 0) :
    (∑ j, w j) = ∑ i, w (f i) := by
  classical
  rw [← Finset.sum_image (f := w) (g := f) (fun _ _ _ _ h => hf h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ h
  exact hz j fun i hi => h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)

/-- Lookup the ordinal of an encoded row. The list clock guarantees a
polynomial output on arbitrary data. -/
def rowOrdinal {A : Type} [DecidableEq A] (p : List A × A) : ℕ :=
  (List.zipIdx p.1 |>.filter fun r => decide (r.1 = p.2)).headD (p.2,0) |>.2

theorem rowOrdinal_eq {A : Type} [DecidableEq A] {xs : List A} (hn : xs.Nodup)
    (i : Fin xs.length) : rowOrdinal (xs,xs[i.val]) = i.val := by
  unfold rowOrdinal
  let records := xs.zipIdx
  have hget (j : Fin records.length) : records[j.val] =
      (xs[j.val]'(by simpa [records] using j.isLt),j.val) := by
    simp [records]
  let v : A × ℕ := (xs[i.val],i.val)
  have hmem : v ∈ records.filter (fun r => decide (r.1 = xs[i.val])) := by
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true rfl⟩
    let q : Fin records.length := ⟨i.val, by simpa [records] using i.isLt⟩
    have hq : records[q.val] = v := hget q
    rw [← hq]
    exact List.getElem_mem _
  have eq (z : A × ℕ) (hz : z ∈ records.filter (fun r => decide (r.1 = xs[i.val]))) :
      z = v := by
    obtain ⟨hr, hv⟩ := List.mem_filter.mp hz
    obtain ⟨j,hj,hz'⟩ := List.mem_iff_getElem.mp hr
    rw [hget ⟨j,hj⟩] at hz'
    have hj' : j < xs.length := by simpa [records] using hj
    have same : xs[j]'hj' = xs[i.val] := by
      exact (congrArg Prod.fst hz').trans (of_decide_eq_true hv)
    have hij := (List.Nodup.getElem_inj hn).mp same
    subst j
    exact hz'.symm
  cases h : records.filter (fun r => decide (r.1 = xs[i.val])) with
  | nil => rw [h] at hmem; cases hmem
  | cons z zs => exact congrArg Prod.snd (eq z (h.symm ▸ List.mem_cons_self))

theorem rowOrdinal_poly {A : Type} [Codec A] [DecidableEq A] [Inhabited A]
    (heq : Poly (fun p : A × A => decide (p.1 = p.2))) :
    Poly (rowOrdinal : List A × A → ℕ) := by
  let zipped := tabLike (fun xs : List A => xs) (fun q : List A × ℕ => (C10.read default q.1 q.2,q.2))
  have hz : Poly zipped := poly_tabLike Code.Poly.identity (by fun_prop)
  have hzEq (xs : List A) : zipped xs = xs.zipIdx := by
    apply List.ext_getElem
    · simp [zipped, tabLike]
    · intro i hi hj
      have h : i < xs.length := by simpa using hj
      simp [zipped, tabLike, C10.read, h]
  have hkeep : Poly (fun q : A × (A × ℕ) => decide (q.2.1 = q.1)) :=
    (Easy.snd.fstCompose.poly.pair Easy.fst.poly).compose heq
  have hp : Poly (fun p : List A × A =>
      ((zipped p.1).filter (fun r => decide (r.1 = p.2))).headD (default : A × ℕ) |>.2) :=
    ((Easy.snd.poly.pair (Easy.fst.poly.compose hz)).compose
      ((C10.filterWith_poly _ hkeep).compose (C10.head_poly default))).sndCompose
  convert hp using 1
  funext p
  unfold rowOrdinal
  rw [hzEq p.1]
  cases (p.1.zipIdx.filter fun r => decide (r.1 = p.2)) <;> rfl

/-- A complete, duplicate-free list of encoded rows implements the
enumeration of the corresponding dependent index type. -/
noncomputable def rowEquiv {A T : Type} {xs : List A} {encode : T → A}
    (hn : xs.Nodup) (he : Function.Injective encode)
    (hm : ∀ row, row ∈ xs ↔ ∃ t, encode t = row) :
    Fin xs.length ≃ T :=
  Equiv.ofBijective
    (fun i => Classical.choose ((hm _).mp (List.getElem_mem i.isLt))) (by
      constructor
      · intro i j hh
        have hi := Classical.choose_spec ((hm _).mp (List.getElem_mem i.isLt))
        have hj := Classical.choose_spec ((hm _).mp (List.getElem_mem j.isLt))
        dsimp only at hh
        rw [hh] at hi
        exact Fin.ext ((List.Nodup.getElem_inj hn).mp (hi.symm.trans hj))
      · intro t
        obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp ((hm _).mpr ⟨t,rfl⟩)
        refine ⟨⟨i,hi⟩,he ?_⟩
        exact (Classical.choose_spec ((hm _).mp (List.getElem_mem hi))).trans heq)

theorem rowEquiv_encode {A T : Type} {xs : List A} {encode : T → A}
    (hn : xs.Nodup) (he : Function.Injective encode)
    (hm : ∀ row, row ∈ xs ↔ ∃ t, encode t = row) (i : Fin xs.length) :
    encode (rowEquiv hn he hm i) = xs[i.val] :=
  Classical.choose_spec ((hm _).mp (List.getElem_mem i.isLt))

/-- Concatenating the selected words in list order is an equivalence. -/
noncomputable def internalEquiv {U V : Type} {p : U → V} {v : V}
    {n : ℕ} (e : Fin n ≃ {u : U // v = p u}) (w : U → ℕ) :
    Placed p (fun u => Fin (2 ^ w u)) v ≃ Fin (2 ^ (∑ i, w (e i).val)) :=
  (P1P5.placedEquiv p _ v).trans
    ((Equiv.piCongrLeft' _ e.symm).trans
      ((Equiv.piCongrRight (fun i => RAMSerialization.wordBits (w (e i).val))).trans
        (((Equiv.piCurry (fun (i : Fin n) (_ : Fin (w (e i).val)) => Bool)).symm.trans
          ((finSigmaFinEquiv (n := fun i => w (e i).val)).arrowCongr (Equiv.refl _))).trans
          (RAMSerialization.wordBits _).symm)))

theorem internalEquiv_card {U V : Type} {p : U → V} {v : V}
    {n : ℕ} (e : Fin n ≃ {u : U // v = p u}) (w : U → ℕ) :
    Nat.card (Placed p (fun u => Fin (2 ^ w u)) v) = 2 ^ (∑ i, w (e i).val) := by
  rw [Nat.card_congr (internalEquiv e w), Nat.card_fin]

theorem internalEquiv_bit {U V : Type} {p : U → V} {v : V}
    {n : ℕ} (e : Fin n ≃ {u : U // v = p u}) (w : U → ℕ)
    (h : Placed p (fun u => Fin (2 ^ w u)) v) (i : Fin n) (j : Fin (w (e i).val)) :
    RAMSerialization.wordBits _ (internalEquiv e w h) (finSigmaFinEquiv ⟨i,j⟩) =
      RAMSerialization.wordBits _ (h (e i).val (e i).property) j := by
  simp only [internalEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply,
    Equiv.piCongrLeft'_apply]
  rfl

theorem listSlice_internal {U V : Type} {p : U → V} {v : V}
    {n : ℕ} (e : Fin n ≃ {u : U // v = p u}) (w : U → ℕ)
    (h : Placed p (fun u => Fin (2 ^ w u)) v) (i : Fin n) :
    P1ProgEng.SolKWR.listSlice (fun i => w (e i).val) i
      (List.ofFn (RAMSerialization.wordBits _ (internalEquiv e w h))) =
        List.ofFn (RAMSerialization.wordBits _ (h (e i).val (e i).property)) := by
  rw [P1ProgEng.SolKWR.listSlice_ofFn]
  congr 1
  funext j
  exact internalEquiv_bit e w h i j

theorem short_of_wordBits {n : ℕ} (i : Fin (2 ^ n)) :
    Bits.short n i.val = List.ofFn (RAMSerialization.wordBits n i) := by
  apply Bits.word_inject
  · rw [Bits.short_length, List.length_ofFn]
  · have hbit (q : Fin n) : RAMSerialization.wordBits n i q = i.val.testBit q.val := by
      exact CursorNetwork.addressWord_bit i q
    rw [Bits.value_short, Nat.mod_eq_of_lt i.isLt]
    rw [show RAMSerialization.wordBits n i = (fun q : Fin n => i.val.testBit q.val) from funext hbit]
    have aux (d : ℕ) (v : ℕ) (h : v < 2 ^ d) :
        Bits.value (List.ofFn (fun q : Fin d => v.testBit q.val)) = v := by
      induction d generalizing v with
      | zero =>
        have hz : v = 0 := by rw [pow_zero] at h; omega
        simp only [List.ofFn_zero, Bits.value_nil,hz]
      | succ d ih =>
        have hv : v / 2 < 2 ^ d := by rw [pow_succ] at h; omega
        rw [List.ofFn_succ, Bits.value_cons]
        simp only [Fin.val_succ, Nat.testBit_succ, Fin.val_zero]
        have hb : v.testBit 0 = Carry.parity v := by
          rw [Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one]
          rfl
        rw [ih (v / 2) hv, hb, Carry.parity_d]
        omega
    exact (aux n i.val i.isLt).symm

end P1ProgEng.SolKWS
