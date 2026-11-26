import P1SolFactor.FactorContentPoly
import P1SolFactor.FactorMachinePoly

namespace P1SolFactor.SolFactor

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1SolFactor.SolHalf P1SolFactor.SolPolyWords P1SolFactor.SolMachine
open scoped Classical

noncomputable section

theorem tally_append (m n : ℕ) : tally m ++ tally n = tally (m + n) :=
  List.replicate_append_replicate

def strT (V : FiniteMultiTapeMachine) (B : Tally) : Tally :=
  mulT (B, tally (Fintype.card V.Γ)) ++
    (tally (Fintype.card V.Q) ++ mulT (tally (Fintype.card V.K), B))

@[fun_prop] theorem strT_poly (V : FiniteMultiTapeMachine) : Poly (strT V) := by
  unfold strT
  fun_prop

@[simp] theorem strT_tally (V : FiniteMultiTapeMachine) (B : ℕ) :
    strT V (tally B) = tally (strWidth V B) := by
  simp only [strT, mulT_tally, tally_append, strWidth]

def tuplePart (V : FiniteMultiTapeMachine) (c : Ext V.K) (p : Tally × List Bool) : List Bool :=
  sliceWord (p.2, (tally (extIdx V.K c).val, strT V p.1))

@[fun_prop] theorem tuplePart_poly (V : FiniteMultiTapeMachine) (c : Ext V.K) : Poly (tuplePart V c) := by
  unfold tuplePart
  fun_prop

@[simp] theorem tuplePart_tally (V : FiniteMultiTapeMachine) (B : ℕ) (c : Ext V.K)
    (f : Ext V.K → Fin (strWidth V B) → Bool) :
    tuplePart V c (tally B, List.ofFn (tupleWord V B f)) = List.ofFn (f c) := by
  rw [tuplePart, strT_tally, sliceWord_tally, segment_ofFn_slice]
  apply congrArg List.ofFn
  funext j
  simp only [P1Net.segment, tupleWord, Equiv.symm_apply_apply]

private theorem slice_asWord {w W : ℕ} (f : Fin w → Bool) (start n : ℕ)
    (hw : start + n ≤ w) (hW : start + n ≤ W) :
    ((List.ofFn (asWord W f)).drop start).take n =
      List.ofFn (fun j : Fin n => f ⟨start + j.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k hk hk'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    have hf : start + k < w := by
      have h : k < n := by simpa only [List.length_ofFn] using hk'
      omega
    exact asWord_mk W f (start + k) _ hf

def readState (V : FiniteMultiTapeMachine) (w : List Bool) : Label V.Q :=
  labelAt V.initialState (readOne (takeT (tally (Fintype.card V.Q), w)))

@[fun_prop] theorem readState_poly (V : FiniteMultiTapeMachine) : Poly (readState V) := by
  unfold readState
  fun_prop

def readOffset (V : FiniteMultiTapeMachine) (k : V.K) (p : Tally × List Bool) : Tally :=
  let start := tally (Fintype.card V.Q) ++ mulT (tally (kIdx V.K k).val, p.1)
  let bits := takeT (p.1, dropT (start, p.2))
  let off := readOne bits
  bif lessT (off, p.1) then off else []

@[fun_prop] theorem readOffset_poly (V : FiniteMultiTapeMachine) (k : V.K) : Poly (readOffset V k) := by
  unfold readOffset
  fun_prop

theorem readOffset_lt (V : FiniteMultiTapeMachine) (B : ℕ) (hB : 0 < B) (k : V.K) (w : List Bool) :
    (readOffset V k (tally B, w)).length < B := by
  let offset := readOne (takeT (tally B,
    dropT (tally (Fintype.card V.Q) ++ mulT (tally (kIdx V.K k).val, tally B), w)))
  change (bif lessT (offset, tally B) then offset else []).length < B
  cases h : lessT (offset, tally B)
  · exact hB
  · have ho : offset.length < B := by
      simpa only [lessT, Iter.small, tally_length, decide_eq_true_eq] using h
    simpa only [h, Bool.cond_true] using ho

section StateWord

variable (V : FiniteMultiTapeMachine) (B : ℕ) (q : V.Q) (off : V.K → Fin B)

private theorem state_code_slice :
    (List.ofFn (encS V B q off)).take (Fintype.card V.Q) = List.ofFn (oneHot q) := by
  unfold encS
  have hw : Fintype.card V.Q ≤ Fintype.card V.Q + Fintype.card V.K * B := Nat.le_add_right _ _
  have hW := hw.trans (show Fintype.card V.Q + Fintype.card V.K * B ≤ strWidth V B by
    unfold strWidth; omega)
  change ((List.ofFn (asWord _ _)).drop 0).take (Fintype.card V.Q) = _
  rw [slice_asWord _ 0 _ (by simpa only [Nat.zero_add] using hw)
    (by simpa only [Nat.zero_add] using hW)]
  congr 1
  funext i
  have h : (⟨0 + i.val, by omega⟩ : Fin (Fintype.card V.Q + Fintype.card V.K * B)) =
      Fin.castAdd (Fintype.card V.K * B) i := Fin.ext (Nat.zero_add _)
  rw [h, Fin.append_left]

@[simp] theorem readState_encS :
    readState V (List.ofFn (encS V B q off)) = ⟨q⟩ := by
  rw [readState, takeT_tally, state_code_slice, readOne_oneHot, labelAt_idx]

private theorem offset_code_slice (k : V.K) :
    ((List.ofFn (encS V B q off)).drop (Fintype.card V.Q + (kIdx V.K k).val * B)).take B =
      List.ofFn (fun j : Fin B => decide (j = off k)) := by
  unfold encS
  let m := Fintype.card V.Q
  let i := kIdx V.K k
  have hp := Nat.mul_le_mul_right B i.isLt
  rw [Nat.succ_mul] at hp
  have hw : m + i.val * B + B ≤ m + Fintype.card V.K * B := by omega
  have hW := hw.trans (show m + Fintype.card V.K * B ≤ strWidth V B by unfold strWidth m; omega)
  rw [slice_asWord _ _ _ hw hW]
  congr 1
  funext j
  have he : (⟨m + i.val * B + j.val, by have := j.isLt; omega⟩ :
      Fin (m + Fintype.card V.K * B)) = Fin.natAdd m (finProdFinEquiv (i, j)) := by
    apply Fin.ext
    simp only [Fin.val_natAdd, finProdFinEquiv_apply_val]
    ring
  rw [he, Fin.append_right]
  simp only [Equiv.symm_apply_apply, i, kIdx]

@[simp] theorem readOffset_encS (k : V.K) :
    readOffset V k (tally B, List.ofFn (encS V B q off)) = tally (off k).val := by
  simp only [readOffset, mulT_tally, tally_append, dropT_tally, takeT_tally, offset_code_slice,
    readOne_ofFn, lessT_tally, (off k).isLt, decide_true, Bool.cond_true]

private def offWord (p : Tally × Tally) : List Bool := oneWord p

def stateWord (V : FiniteMultiTapeMachine) (p : Tally × (Label V.Q × List Tally)) : List Bool :=
  let q := oneWord (tally (Fintype.card V.Q), labelIdx p.2.1)
  let off := (polyPush offWord (p.1, p.2.2)).flatten
  atWidth false (strT V p.1, q ++ off)

@[fun_prop] theorem stateWord_poly (V : FiniteMultiTapeMachine) : Poly (stateWord V) := by
  unfold stateWord
  have ho : Poly (fun p : Tally × (Label V.Q × List Tally) => (p.1, p.2.2)) := by fun_prop
  have h : Poly (fun p : Tally × (Label V.Q × List Tally) =>
      (polyPush offWord (p.1, p.2.2)).flatten) :=
    (ho.compose (Code.Poly.push [] [] oneWord_poly)).compose flatten_poly
  have hq : Poly (fun p : Tally × (Label V.Q × List Tally) =>
      oneWord (tally (Fintype.card V.Q), labelIdx p.2.1)) := by fun_prop
  have hs : Poly (fun p : Tally × (Label V.Q × List Tally) => strT V p.1) := by fun_prop
  exact (hs.pair (hq.app h)).compose (atWidth_poly false)

theorem stateWord_encS :
    stateWord V (tally B, (⟨q⟩, List.ofFn (fun i => tally (off ((kIdx V.K).symm i)).val))) =
      List.ofFn (encS V B q off) := by
  let w (j : Fin (Fintype.card V.K * B)) :=
    decide ((finProdFinEquiv.symm j).2 = off ((kIdx V.K).symm (finProdFinEquiv.symm j).1))
  have hw : (List.ofFn (fun i : Fin (Fintype.card V.K) => List.ofFn
        (fun j : Fin B => decide ((off ((kIdx V.K).symm i)).val = j.val)))).flatten = List.ofFn w := by
    rw [ofFn_prod]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    simp only [w, Equiv.symm_apply_apply]
    exact decide_eq_decide.mpr (eq_comm.trans Fin.ext_iff.symm)
  have he : List.ofFn (Fin.append (oneHot q) w) =
      List.ofFn (oneHot q) ++ List.ofFn w := by
    rw [List.ofFn_add]
    simp only [Fin.append_right]
    congr 1
    apply congrArg List.ofFn
    funext i
    change Fin.append (oneHot q) w (Fin.castAdd _ i) = oneHot q i
    exact Fin.append_left _ _ _
  simp only [stateWord, strT_tally, labelIdx]
  rw [oneWord_oneHot]
  simp only [polyPush, List.map_ofFn, Function.comp_def, offWord, oneWord_tally,
    hw, ← he, atWidth_tally]
  exact wordAtWidth_ofFn _ (Fin.append (oneHot q) w)

end StateWord

def inputBlock (V : FiniteMultiTapeMachine) (k : V.K) (d : Fin 3) (p : Tally × List Bool) :
    List (Label V.Γ) :=
  readBlock V (tuplePart V (.cIn k d) p, p.1)

@[fun_prop] theorem inputBlock_poly (V : FiniteMultiTapeMachine) (k : V.K) (d : Fin 3) :
    Poly (inputBlock V k d) := by unfold inputBlock; fun_prop

def inputTape (V : FiniteMultiTapeMachine) (k : V.K) (p : Tally × List Bool) : Tape V :=
  (p.1 ++ readOffset V k (p.1, tuplePart V .stIn p),
    inputBlock V k 0 p ++ (inputBlock V k 1 p ++ inputBlock V k 2 p))

@[fun_prop] theorem inputTape_poly (V : FiniteMultiTapeMachine) (k : V.K) :
    Poly (inputTape V k) := by unfold inputTape; fun_prop

def inputConfig (V : FiniteMultiTapeMachine) (p : Tally × List Bool) : Config V :=
  (readState V (tuplePart V .stIn p), List.ofFn (fun i => inputTape V ((kIdx V.K).symm i) p))

@[fun_prop] theorem inputConfig_poly (V : FiniteMultiTapeMachine) : Poly (inputConfig V) := by
  unfold inputConfig
  exact (by fun_prop : Poly (fun p => readState V (tuplePart V .stIn p))).pair
    (ofFn_poly _ (fun i => inputTape V ((kIdx V.K).symm i)) (fun _ => inputTape_poly V _))

section InputCorrectness

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]

def decodedIn (word : List Bool) : LocalIn V B :=
  let p := (tally B, word)
  ⟨(readState V (tuplePart V .stIn p)).val,
    fun k => ⟨(readOffset V k (tally B, tuplePart V .stIn p)).length,
      readOffset_lt V B (Nat.pos_of_ne_zero (NeZero.ne B)) k _⟩,
    fun k δ i => (readCell V (tuplePart V (.cIn k δ) p, tally i.val)).val⟩

@[simp] theorem decodedIn_code (d : LocalIn V B) (o : LocalOut V B) :
    decodedIn V B (List.ofFn (tupleWord V B (extData V B d o))) = d := by
  apply LocalIn.ext
  · simp only [decodedIn, tuplePart_tally, extData, readState_encS]
  · funext k
    apply Fin.ext
    simp only [decodedIn, tuplePart_tally, extData, readOffset_encS, tally_length]
  · funext k δ i
    simp only [decodedIn, tuplePart_tally, extData, readCell_encC]

theorem abs_cell (d : LocalIn V B) (k : V.K) (δ : Fin 3) (j : Fin B) :
    d.toAbs.cells k ((δ.val : ℤ) * B + j.val) = d.blocks k δ j := by
  have hB : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hjn : (0 : ℤ) ≤ j.val := by positivity
  have hj : (j.val : ℤ) < B := by exact_mod_cast j.isLt
  have hδn : (0 : ℤ) ≤ δ.val := by positivity
  have hdlt : (δ.val : ℤ) < 3 := by exact_mod_cast δ.isLt
  have hδ : (δ.val : ℤ) + 1 ≤ 3 := by omega
  let z : ℤ := (δ.val : ℤ) * B + j.val
  have hz0 : 0 ≤ z := by unfold z; positivity
  have hz1 : z < 3 * B := by
    unfold z
    nlinarith [mul_le_mul_of_nonneg_right hδ hB.le]
  have hq : z / B = δ.val := ediv_eq_of_bounds hB (by unfold z; omega) (by unfold z; omega)
  have hr : z % B = j.val := by
    have he := Int.emod_add_ediv_mul z B
    rw [hq] at he
    unfold z at he
    linarith
  change (if 0 ≤ z ∧ z < 3 * B then d.blocks k (finOfInt 3 (z / B)) (finOfInt B (z % B))
    else default) = _
  rw [ite_eq_left (And.intro hz0 hz1), hq, hr, finOfInt_coe, finOfInt_coe]

theorem inputConfig_decode (word : List Bool) :
    inputConfig V (tally B, word) = SolMachine.encode V (3 * B) (decodedIn V B word).toAbs := by
  let d := decodedIn V B word
  change inputConfig V (tally B, word) = SolMachine.encode V (3 * B) d.toAbs
  unfold inputConfig SolMachine.encode
  congr 1
  apply congrArg List.ofFn
  funext i
  let k := (kIdx V.K).symm i
  change inputTape V k (tally B, word) =
    (tally (d.toAbs.pos k).toNat, List.ofFn fun j : Fin (3 * B) => ⟨d.toAbs.cells k j.val⟩)
  unfold inputTape
  congr 1
  · have hp : (d.toAbs.pos k).toNat = B + (d.off k).val := by
      change ((B : ℤ) + ((d.off k).val : ℤ)).toNat = _
      omega
    rw [hp, ← tally_append]
    change tally B ++ readOffset V k (tally B, tuplePart V .stIn (tally B, word)) =
      tally B ++ tally (readOffset V k (tally B, tuplePart V .stIn (tally B, word))).length
    rw [recover_tally]
  · simp only [inputBlock, readBlock_tally]
    change (List.ofFn fun j => (⟨d.blocks k 0 j⟩ : Label V.Γ)) ++
        ((List.ofFn fun j => (⟨d.blocks k 1 j⟩ : Label V.Γ)) ++
          (List.ofFn fun j => (⟨d.blocks k 2 j⟩ : Label V.Γ))) = _
    rw [ofFn_prod]
    have hprod (δ : Fin 3) (j : Fin B) :
        ((finProdFinEquiv (δ, j)).val : ℤ) = (δ.val : ℤ) * B + j.val := by
      simp only [finProdFinEquiv_apply_val, Nat.cast_add, Nat.cast_mul]
      ring
    have hs :
        (List.ofFn (fun δ : Fin 3 => List.ofFn
          (fun j : Fin B => (⟨d.toAbs.cells k (finProdFinEquiv (δ, j)).val⟩ : Label V.Γ)))).flatten =
        (List.ofFn (fun δ : Fin 3 => List.ofFn (fun j : Fin B => (⟨d.blocks k δ j⟩ : Label V.Γ)))).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext δ
      apply congrArg List.ofFn
      funext j
      rw [hprod, abs_cell V B d k δ j]
    rw [hs]
    simp only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

end InputCorrectness

end

end P1SolFactor.SolFactor
