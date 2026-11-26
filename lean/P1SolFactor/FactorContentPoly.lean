import P1SolFactor.FactorFieldsPoly
import P1SolFactor.PolyLabels

namespace P1SolFactor.SolFactor

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1SolFactor.Owner P1SolFactor.SolHalf P1SolFactor.SolPolyWords
open scoped Classical

noncomputable section

def readCell (V : FiniteMultiTapeMachine) (p : List Bool × Tally) : Label V.Γ :=
  labelAt default (readOne (sliceWord (p.1, (p.2, tally (Fintype.card V.Γ)))))

@[fun_prop] theorem readCell_poly (V : FiniteMultiTapeMachine) : Poly (readCell V) := by
  unfold readCell
  fun_prop

def readBlock (V : FiniteMultiTapeMachine) (p : List Bool × Tally) : List (Label V.Γ) :=
  polyPush (readCell V) (p.1, Iter.lineup p.2)

@[fun_prop] theorem readBlock_poly (V : FiniteMultiTapeMachine) : Poly (readBlock V) := by
  unfold readBlock
  have h : Poly (fun p : List Bool × Tally => (p.1, Iter.lineup p.2)) := by fun_prop
  exact h.compose (Code.Poly.push [] [] (readCell_poly V))

theorem readBlock_tally (V : FiniteMultiTapeMachine) (B : ℕ) (w : List Bool) :
    readBlock V (w, tally B) =
      List.ofFn (fun i : Fin B => readCell V (w, tally i.val)) := by
  simp only [readBlock, polyPush, Iter.lined, List.map_ofFn, Function.comp_def]

def cellWord (V : FiniteMultiTapeMachine) (c : Label V.Γ) : List Bool :=
  oneWord (tally (Fintype.card V.Γ), labelIdx c)

@[fun_prop] theorem cellWord_poly (V : FiniteMultiTapeMachine) : Poly (cellWord V) := by
  unfold cellWord
  fun_prop

def blockWord (V : FiniteMultiTapeMachine) (p : Tally × List (Label V.Γ)) : List Bool :=
  atWidth false (p.1, (p.2.map (cellWord V)).flatten)

@[fun_prop] theorem blockWord_poly (V : FiniteMultiTapeMachine) : Poly (blockWord V) := by
  unfold blockWord
  apply Code.Poly.compose _ (atWidth_poly false)
  exact Easy.fst.poly.pair
    (Easy.snd.poly.compose ((Code.Poly.maps _ (cellWord_poly V)).compose flatten_poly))

theorem blockWord_encC (V : FiniteMultiTapeMachine) (B : ℕ) (p : Fin B → V.Γ) :
    blockWord V (tally (strWidth V B), List.ofFn (fun i => ⟨p i⟩)) = List.ofFn (encC V B p) := by
  let f (j : Fin (B * Fintype.card V.Γ)) := oneHot (p (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2
  have h :
      (List.ofFn (fun i : Fin B => List.ofFn (oneHot (p i)))).flatten = List.ofFn f := by
    rw [ofFn_prod]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    simp only [f, Equiv.symm_apply_apply]
  simp only [blockWord, List.map_ofFn, Function.comp_def, cellWord, labelIdx, oneWord_oneHot,
    h, atWidth_tally]
  exact wordAtWidth_ofFn _ f

theorem readCell_encC (V : FiniteMultiTapeMachine) (B : ℕ) (p : Fin B → V.Γ) (i : Fin B) :
    readCell V (List.ofFn (encC V B p), tally i.val) = ⟨p i⟩ := by
  have hcap : (i.val + 1) * Fintype.card V.Γ ≤ strWidth V B := by
    exact (Nat.mul_le_mul_right _ i.isLt).trans (Nat.le_add_right _ _)
  have hs : sliceWord (List.ofFn (encC V B p), (tally i.val, tally (Fintype.card V.Γ))) =
      List.ofFn (oneHot (p i)) := by
    rw [sliceWord_tally]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_ofFn]
      have h := hcap
      rw [Nat.add_mul, Nat.one_mul] at h
      omega
    · intro k hk hj
      rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
      have hfit : i.val * Fintype.card V.Γ + k < B * Fintype.card V.Γ := by
        have h1 := Nat.mul_le_mul_right (Fintype.card V.Γ) i.isLt
        rw [Nat.succ_mul] at h1
        have h2 : k < Fintype.card V.Γ := by simpa only [List.length_ofFn] using hj
        omega
      unfold encC
      rw [asWord_mk _ _ _ _ hfit]
      have he : (⟨i.val * Fintype.card V.Γ + k, hfit⟩ : Fin (B * Fintype.card V.Γ)) =
          finProdFinEquiv (i, (⟨k, by simpa only [List.length_ofFn] using hj⟩ : Fin (Fintype.card V.Γ))) := by
        apply Fin.ext
        simp only [finProdFinEquiv_apply_val]
        ring
      rw [he, Equiv.symm_apply_apply]
  simp only [readCell, hs, readOne_oneHot, labelAt_idx]

theorem readBlock_encC (V : FiniteMultiTapeMachine) (B : ℕ) (p : Fin B → V.Γ) :
    readBlock V (List.ofFn (encC V B p), tally B) = List.ofFn (fun i => ⟨p i⟩) := by
  simp only [readBlock_tally, readCell_encC]

def pinAllowed (V : FiniteMultiTapeMachine) (p : Label V.Γ × Tally) : Bool :=
  bif eqT (p.2, tally 0) then
    (fun c : Label V.Γ => decide (∃ b, c.val = V.inputSymbol b)) p.1
  else eqT (p.2, () :: labelIdx p.1)

private theorem inputSymbol_poly (V : FiniteMultiTapeMachine) :
    Poly (fun c : Label V.Γ => decide (∃ b, c.val = V.inputSymbol b)) :=
  (Easy.finite _).poly

@[fun_prop] theorem pinAllowed_poly (V : FiniteMultiTapeMachine) : Poly (pinAllowed V) := by
  unfold pinAllowed
  apply Code.Poly.choose
  · fun_prop
  · exact Easy.fst.poly.compose (inputSymbol_poly V)
  · fun_prop

def pinRow (V : FiniteMultiTapeMachine) (p : (List Tally × List (Label V.Γ)) × Tally) : Bool :=
  pinAllowed V (Iter.pick ⟨default⟩ (p.1.2, p.2), Iter.pick [] (p.1.1, p.2))

@[fun_prop] theorem pinRow_poly (V : FiniteMultiTapeMachine) : Poly (pinRow V) := by
  unfold pinRow
  fun_prop

def pinsCheck (V : FiniteMultiTapeMachine) (p : List Tally × List (Label V.Γ)) : Bool :=
  allBits (polyPush (pinRow V) (p, Iter.lineup (ruler p.1)))

@[fun_prop] theorem pinsCheck_poly (V : FiniteMultiTapeMachine) : Poly (pinsCheck V) := by
  unfold pinsCheck
  have hp : Poly (fun p : List Tally × List (Label V.Γ) => (p, Iter.lineup (ruler p.1))) := by
    fun_prop
  exact (hp.compose (Code.Poly.push ([], []) [] (pinRow_poly V))).compose allBits_poly

def pinTest (V : FiniteMultiTapeMachine) (p : Query) : Bool :=
  let pins := dropT (tally 1, p.1)
  let word := outSlot (p.2, tally 0)
  let cells := readBlock V (word, ruler pins)
  andB (exactEq (word, blockWord V (ruler word, cells)), pinsCheck V (pins, cells))

@[fun_prop] theorem pinTest_poly (V : FiniteMultiTapeMachine) : Poly (pinTest V) := by
  unfold pinTest
  fun_prop

def pinCode (V : FiniteMultiTapeMachine) (o : Option V.Γ) : Tally :=
  tally (o.elim 0 fun t => (Fintype.equivFin V.Γ t).val + 1)

def pinValue (V : FiniteMultiTapeMachine) (o : Option V.Γ) (x : V.Γ) : Prop :=
  match o with
  | none => ∃ b, x = V.inputSymbol b
  | some t => x = t

theorem pinAllowed_correct (V : FiniteMultiTapeMachine) (o : Option V.Γ) (x : V.Γ) :
    pinAllowed V (⟨x⟩, pinCode V o) = true ↔ pinValue V o x := by
  cases o with
  | none => simp [pinAllowed, pinCode, pinValue, eqT_tally]
  | some t =>
    have hn : (Fintype.equivFin V.Γ t).val + 1 ≠ 0 := Nat.succ_ne_zero _
    simp only [pinAllowed, pinCode, pinValue, Option.elim_some, eqT_tally, hn, decide_false,
      Bool.cond_false, labelIdx, ← tally_succ, decide_eq_true_eq, Nat.add_right_cancel_iff]
    exact ⟨fun h => (Fintype.equivFin V.Γ).injective (Fin.ext h.symm), fun h => h ▸ rfl⟩

theorem pinsCheck_correct (V : FiniteMultiTapeMachine) (B : ℕ) (o : Fin B → Option V.Γ)
    (p : Fin B → V.Γ) :
    pinsCheck V (List.ofFn (fun i => pinCode V (o i)), List.ofFn (fun i => ⟨p i⟩)) = true ↔
      ∀ i, pinValue V (o i) (p i) := by
  have h : ruler (List.ofFn (fun i => pinCode V (o i))) = tally B := by
    rw [← recover_tally (ruler _), ruler_length, List.length_ofFn]
  unfold pinsCheck
  rw [allBits_true]
  change (∀ b ∈ polyPush (pinRow V) ((List.ofFn _, List.ofFn _), Iter.lineup
    (ruler (List.ofFn (fun i => pinCode V (o i))))), b = true) ↔ _
  rw [h]
  simp only [polyPush, Iter.lined, List.map_ofFn, Function.comp_def]
  have hi (i : Fin B) : pinRow V ((List.ofFn (fun i => pinCode V (o i)),
      List.ofFn (fun i => ⟨p i⟩)), tally i.val) = true ↔ pinValue V (o i) (p i) := by
    rw [pinRow, Iter.entry, Iter.entry, pinAllowed_correct]
  constructor
  · exact fun h i => (hi i).1 (h _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro h b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact (hi i).2 (h i)

theorem pinTest_word (V : FiniteMultiTapeMachine) (B : ℕ) (o : Fin B → Option V.Γ)
    (word : List Bool) (hw : word.length = strWidth V B) (p : Query)
    (hPins : dropT (tally 1, p.1) = List.ofFn (fun i => pinCode V (o i)))
    (hWord : outSlot (p.2, tally 0) = word) :
    pinTest V p = true ↔
      ∃ x : Fin B → V.Γ, (∀ i, pinValue V (o i) (x i)) ∧ word = List.ofFn (encC V B x) := by
  have hB : ruler (List.ofFn (fun i => pinCode V (o i))) = tally B := by
    rw [← recover_tally (ruler _), ruler_length, List.length_ofFn]
  have hW : ruler word = tally (strWidth V B) := by
    rw [← recover_tally (ruler word), ruler_length, hw]
  dsimp only [pinTest, andB]
  rw [hPins, hWord, hB, hW, Bool.and_eq_true, exactEq_true]
  constructor
  · let x (i : Fin B) : V.Γ := (readCell V (word, tally i.val)).val
    intro ⟨he, hp⟩
    rw [readBlock_tally] at he hp
    change word = blockWord V (tally (strWidth V B), List.ofFn fun i => ⟨x i⟩) at he
    change pinsCheck V (_, List.ofFn fun i => ⟨x i⟩) = true at hp
    rw [blockWord_encC] at he
    exact ⟨x, (pinsCheck_correct V B o x).1 hp, he⟩
  · rintro ⟨x, hx, rfl⟩
    rw [readBlock_encC, blockWord_encC]
    exact ⟨rfl, (pinsCheck_correct V B o x).2 hx⟩

theorem pinValue_iff (V : FiniteMultiTapeMachine) {J : Type} (guess : Option J) (base x : V.Γ) :
    pinValue V (if guess.isSome then none else some base) x ↔
      (∀ j, guess = some j → ∃ b, x = V.inputSymbol b) ∧ (guess = none → x = base) := by
  cases guess with
  | none => simp [pinValue]
  | some j => simp [pinValue]


end

end P1SolFactor.SolFactor
