import P1SolFactor.PolyLists
import P1Net.Factors

namespace P1SolFactor.SolPolyWords

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open scoped Classical

noncomputable section

@[ext] structure Label (A : Type) where
  val : A

instance {A : Type} [Fintype A] : Codec (Label A) :=
  ⟨fun a => send (tally (Fintype.equivFin A a.val).val)⟩

instance {A : Type} [Fintype A] : FiniteState (Label A) where
  finite := Finite.of_injective Label.val (fun _ _ => Label.ext)
  identify := by
    intro a b h
    have e : size (tally (Fintype.equivFin A a.val).val) =
        size (tally (Fintype.equivFin A b.val).val) := congrArg Tree.count h
    simp only [size_tally, tally_length] at e
    exact Label.ext ((Fintype.equivFin A).injective (Fin.ext (by omega)))

theorem label_size {A : Type} [Fintype A] (q : A) :
    size (Label.mk q) ≤ 2 * Fintype.card A + 1 := by
  change size (tally (Fintype.equivFin A q).val) ≤ _
  rw [size_tally, tally_length]
  have h := (Fintype.equivFin A q).isLt
  omega

theorem select_poly {A X Y : Type} [Fintype A] [Codec X] [Codec Y]
    (tag : X → Label A) (ht : Poly tag) (f : A → X → Y) (each : ∀ a, Poly (f a))
    (default : X → Y) (hd : Poly default) :
    Poly (fun x => f (tag x).val x) := by
  have loop (labels : List A) :
      Poly (fun x => if (tag x).val ∈ labels then f (tag x).val x else default x) := by
    induction labels with
    | nil => simpa only [List.not_mem_nil, ite_false] using hd
    | cons a labels ih =>
      let test (z : Label A) := decide (z.val = a)
      have h := Code.Poly.choose (ht.compose (Easy.finite test).poly) (each a) ih
      convert h using 1
      funext x
      by_cases e : (tag x).val = a <;> simp [test, e]
  simpa using loop Finset.univ.toList

theorem ofFn_prod {A : Type} {m n : ℕ} (f : Fin (m * n) → A) :
    List.ofFn f =
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f (finProdFinEquiv (i, j))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  simp only [finProdFinEquiv_apply_val]
  ring

theorem ofFn_poly {X Y : Type} [Codec X] [Codec Y] (n : ℕ)
    (f : Fin n → X → Y) (hf : ∀ i, Poly (f i)) :
    Poly (fun x => List.ofFn (fun i => f i x)) := by
  induction n with
  | zero => simpa only [List.ofFn_zero] using (Code.Poly.const (X := X) ([] : List Y))
  | succ n ih =>
    simp only [List.ofFn_succ]
    exact ((hf 0).pair (ih (fun i => f i.succ) (fun i => hf i.succ))).compose Code.Poly.cons

theorem labelPi_poly {X A : Type} [Codec X] [Fintype A] (n : ℕ)
    (f : Fin n → X → Label A) (hf : ∀ i, Poly (f i)) :
    Poly (fun x => (⟨fun i => (f i x).val⟩ : Label (Fin n → A))) := by
  induction n with
  | zero =>
    have he : (fun x => (⟨fun i => (f i x).val⟩ : Label (Fin 0 → A))) =
        (fun _ : X => (⟨Fin.elim0⟩ : Label (Fin 0 → A))) := by
      funext x
      apply Label.ext
      funext i
      exact Fin.elim0 i
    rw [he]
    exact Code.Poly.const _
  | succ n ih =>
    let cons (p : Label A × Label (Fin n → A)) : Label (Fin (n + 1) → A) :=
      ⟨Fin.cons p.1.val p.2.val⟩
    have h := (hf 0).pair (ih (fun i => f i.succ) (fun i => hf i.succ))
    convert h.compose (Easy.finite cons).poly using 1
    funext x
    apply Label.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def labelIdx {A : Type} [Fintype A] (q : Label A) : Tally := tally (Fintype.equivFin A q.val).val

@[fun_prop] theorem labelIdx_poly {A : Type} [Fintype A] : Poly (labelIdx (A := A)) :=
  (Easy.finite _).poly

def labelAt {A : Type} [Fintype A] (fallback : A) (i : Tally) : Label A :=
  Iter.pick ⟨fallback⟩ (List.ofFn (fun j => ⟨(Fintype.equivFin A).symm j⟩), i)

@[fun_prop] theorem labelAt_poly {A : Type} [Fintype A] (fallback : A) : Poly (labelAt fallback) := by
  unfold labelAt
  fun_prop

@[simp] theorem labelAt_idx {A : Type} [Fintype A] (fallback x : A) :
    labelAt fallback (tally (Fintype.equivFin A x).val) = ⟨x⟩ := by
  rw [labelAt, Iter.entry, Equiv.symm_apply_apply]

def oneStep (bit seen : Bool) : Bool × Tally :=
  (seen || bit, if seen || bit then [] else [()])

def readOne (w : List Bool) : Tally := (machine oneStep (w, false)).1

@[fun_prop] theorem readOne_poly : Poly readOne :=
  (Easy.machine (Easy.identity.pair (Easy.const false))).poly.fstCompose

theorem readOne_eq (xs : List Bool) (n : ℕ) (hn : n < xs.length)
    (h : ∀ k, xs.getD k false = decide (k = n)) :
    readOne xs = tally n := by
  have seen_nil (ys : List Bool) : (machine oneStep (ys, true)).1 = [] := by
    induction ys with
    | nil => rfl
    | cons b ys ih => simpa only [machine_cons, oneStep, Bool.true_or, ↓reduceIte,
        List.nil_append] using ih
  induction xs generalizing n with
  | nil => simp at hn
  | cons b xs ih =>
    cases n with
    | zero =>
      have hb : b = true := by simpa using h 0
      subst b
      simp only [readOne, machine_cons, oneStep, Bool.false_or, ↓reduceIte,
        List.nil_append, seen_nil]
      rfl
    | succ n =>
      have hb : b = false := by simpa using h 0
      subst b
      have hn' : n < xs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      have h' (i : ℕ) : xs.getD i false = decide (i = n) := by
        simpa only [List.getD_cons_succ, Nat.succ_inj] using h (i + 1)
      simp only [readOne, machine_cons, oneStep, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
        List.singleton_append, tally_succ]
      exact congrArg (List.cons ()) (ih n hn' h')

theorem readOne_ofFn {w : ℕ} (i : Fin w) :
    readOne (List.ofFn (fun j : Fin w => decide (j = i))) = tally i.val := by
  apply readOne_eq _ _ (by simpa only [List.length_ofFn] using i.isLt)
  intro k
  by_cases hk : k < w
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hk), List.getElem_ofFn]
    exact decide_eq_decide.mpr Fin.ext_iff
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hk)]
    have h : k ≠ i.val := fun e => hk (e.symm ▸ i.isLt)
    simp only [Option.getD_none, h, decide_false]

def oneWord (p : Tally × Tally) : List Bool :=
  polyPush eqT (p.2, Iter.lineup p.1)

@[fun_prop] theorem oneWord_poly : Poly oneWord := by
  unfold oneWord
  exact ((by fun_prop : Poly (fun p : Tally × Tally => (p.2, Iter.lineup p.1)))).compose
    (Code.Poly.push [] [] eqT_poly)

@[simp] theorem oneWord_tally (w i : ℕ) :
    oneWord (tally w, tally i) = List.ofFn (fun j : Fin w => decide (i = j.val)) := by
  simp only [oneWord, Iter.lined, polyPush, List.map_ofFn, Function.comp_def, eqT_tally]

theorem oneWord_oneHot {A : Type} [Fintype A] (x : A) :
    oneWord (tally (Fintype.card A), tally (Fintype.equivFin A x).val) = List.ofFn (P1Net.oneHot x) := by
  rw [oneWord_tally]
  congr 1
  funext j
  unfold P1Net.oneHot
  apply decide_eq_decide.mpr
  exact (eq_comm.trans Fin.ext_iff.symm)

theorem readOne_oneHot {A : Type} [Fintype A] (x : A) :
    readOne (List.ofFn (P1Net.oneHot x)) = tally (Fintype.equivFin A x).val := by
  have he : P1Net.oneHot x = (fun j => decide (j = Fintype.equivFin A x)) := by
    funext j
    unfold P1Net.oneHot
    exact decide_eq_decide.mpr Iff.rfl
  rw [he]
  exact readOne_ofFn (Fintype.equivFin A x)

end

end P1SolFactor.SolPolyWords
