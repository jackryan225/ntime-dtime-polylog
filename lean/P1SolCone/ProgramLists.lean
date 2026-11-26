import P1SolCone.BoundedWords
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

section Arithmetic

variable {X : Type} [Codec X]

theorem bval_eq_value (w : List Bool) : P1Batch.bval w = Bits.value w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [P1Batch.bval, Bits.value, ih] <;> rfl

theorem binary_eq_coneBin (n : ℕ) : binary n = P1ChkFinal.bin n := by
  apply Bits.word_inject
  · rw [binary, Bits.short_length]
    have hv : Bits.value (P1ChkFinal.bin n) = n :=
      (bval_eq_value _).symm.trans (P1ChkFinal.bval_bin n)
    have hc := Bits.value_lt (P1ChkFinal.bin n)
    rw [hv] at hc
    apply le_antisymm
    · exact (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
    · exact P1ChkFinal.length_bin_le _ _ (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))
  · rw [value_binary, ← bval_eq_value, P1ChkFinal.bval_bin]

@[fun_prop] theorem poly_bval {f : X → List Bool} (hf : Poly f) :
    Poly (fun x => P1Batch.bval (f x)) := by
  let r : Strip.Regime X := ⟨size, send, Dom.base _⟩
  have h : Carry.Figure r (fun x => P1Batch.bval (f x)) :=
    ⟨f, hf, fun x => (bval_eq_value (f x)).symm⟩
  exact h.write ((h.added (Carry.Figure.natural 1)).short_log)

@[fun_prop] theorem poly_bin {f : X → ℕ} (hf : Poly f) : Poly (fun x => P1ChkFinal.bin (f x)) := by
  simpa only [← binary_eq_coneBin] using (show Poly (fun x => binary (f x)) from hf)

@[fun_prop] theorem poly_lt {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := by
  have h : Poly (fun x => (binary (f x), binary (g x))) := hf.pair hg
  simpa only [Carry.lt_r, value_binary] using h.compose Carry.ltPoly

@[fun_prop] theorem poly_eqNat {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := by
  let op (b : Bool × Bool) := !(b.1 || b.2)
  have h := ((poly_lt hf hg).pair (poly_lt hg hf)).compose (Easy.finite op).poly
  convert h using 1
  funext x
  by_cases he : f x = g x
  · simp only [op, he, lt_self_iff_false, decide_false, Bool.or_false, Bool.not_false, decide_true]
  · rcases lt_or_gt_of_ne he with hl | hl
    · simp only [op, he, hl, decide_true, Bool.true_or, Bool.not_true, decide_false]
    · simp only [op, he, hl, decide_true, Bool.or_true, Bool.not_true, decide_false]

@[fun_prop] theorem poly_min {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => min (f x) (g x)) := by
  have h := Code.Poly.choose (poly_lt hf hg) hf hg
  convert h using 1
  funext x
  by_cases e : f x < g x
  · simp only [e, decide_true, Bool.cond_true, min_eq_left e.le]
  · simp only [e, decide_false, Bool.cond_false, min_eq_right (Nat.le_of_not_lt e)]

end Arithmetic

variable {A : Type} [Codec A]

/-- Compose equality tests for the components of a pair. -/
theorem poly_eqProd {B : Type} [Codec B] [DecidableEq A] [DecidableEq B]
    (ha : Poly (fun p : A × A => decide (p.1 = p.2)))
    (hb : Poly (fun p : B × B => decide (p.1 = p.2))) :
    Poly (fun p : (A × B) × (A × B) => decide (p.1 = p.2)) := by
  have pa : Poly (fun p : (A × B) × (A × B) => (p.1.1, p.2.1)) := by fun_prop
  have pb : Poly (fun p : (A × B) × (A × B) => (p.1.2, p.2.2)) := by fun_prop
  have q := ((pa.compose ha).pair (pb.compose hb)).compose
    (Easy.finite (fun b : Bool × Bool => b.1 && b.2)).poly
  convert q using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff]

/-- Universal test on a list using a Boolean accumulator. -/
theorem poly_allList {p : A → Bool} (hp : Poly p) : Poly (fun xs : List A => xs.all p) := by
  let op (q : Bool × Bool) := q.1 && q.2
  have fold := Poly.fold_left (f := op) (Easy.finite op).poly 1 0 (fun _ _ _ => by
    change 1 ≤ 1 * _ ^ 0
    simp only [pow_zero, Nat.mul_one, le_refl])
  have h := ((Code.Poly.maps _ hp).pair (Code.Poly.const true)).compose fold
  convert h using 1
  funext xs
  have step : ∀ (l : List A) (b : Bool),
      (l.map p).foldl (fun a v => op (a, v)) b = (b && l.all p) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro b
      simp only [List.map_cons, List.foldl_cons, List.all_cons, ih, op, Bool.and_assoc]
  simpa only [Bool.true_and] using (step xs true).symm

theorem poly_anyList {p : A → Bool} (hp : Poly p) : Poly (fun xs : List A => xs.any p) := by
  have h := (poly_allList (hp.compose (Easy.finite Bool.not).poly)).compose (Easy.finite Bool.not).poly
  convert h using 1
  funext xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.any_cons, List.all_cons, Bool.not_and, Bool.not_not, ← ih]

private def listEqual [Inhabited A] (cmp : A × A → Bool) (p : List A × List A) : Bool :=
  decide (p.1.length = p.2.length) &&
    (List.ofFn (fun i : Fin p.1.length =>
      (readAt default p.1 i.val, readAt default p.2 i.val))).all cmp

theorem poly_eqList [Inhabited A] [DecidableEq A]
    (cmp : Poly (fun p : A × A => decide (p.1 = p.2))) :
    Poly (fun p : List A × List A => decide (p.1 = p.2)) := by
  have p : Poly (fun p : List A × List A => p.1) := Easy.fst.poly
  have q : Poly (fun p : List A × List A => p.2) := Easy.snd.poly
  have rows : Poly (fun z : List A × List A =>
      List.ofFn fun i : Fin z.1.length => (readAt default z.1 i.val, readAt default z.2 i.val)) :=
    poly_tabLike (l := Prod.fst) (f := fun z : (List A × List A) × ℕ =>
      (readAt default z.1.1 z.2, readAt default z.1.2 z.2)) p (by fun_prop)
  have h := ((poly_eqNat (poly_lengthNat p) (poly_lengthNat q)).pair
    (rows.compose (poly_allList cmp))).compose (Easy.finite (fun b : Bool × Bool => b.1 && b.2)).poly
  change Poly (listEqual (fun p : A × A => decide (p.1 = p.2))) at h
  convert h using 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [listEqual, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_ofFn]
  constructor
  · rintro he
    refine ⟨congrArg List.length he, fun q ⟨i, hq⟩ => ?_⟩
    rw [← hq]
    exact congrArg (fun xs => readAt default xs i.val) he
  · rintro ⟨hl, he⟩
    apply List.ext_getElem hl
    intro i hi hj
    have hh := he _ ⟨⟨i, hi⟩, rfl⟩
    simpa only [readAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using hh

theorem poly_eqPosition : Poly (fun p : PositionCode × PositionCode => decide (p.1 = p.2)) :=
  poly_eqProd (poly_eqNat Easy.fst.poly Easy.snd.poly) (poly_eqNat Easy.fst.poly Easy.snd.poly)

theorem poly_eqKey : Poly (fun p : KeyCode × KeyCode => decide (p.1 = p.2)) :=
  poly_eqProd poly_eqPosition (poly_eqProd half half)
where
  half := poly_eqList (poly_eqList (A := Bool) (Easy.finite _).poly)

/-- Index of the first match, written with one tally element per preceding nonmatch. -/
def firstIndex (flags : List Bool) : Tally :=
  flags.reverse.foldl (fun q b => bif b then [] else () :: q) []

theorem firstIndex_poly : Poly firstIndex := by
  let op (p : Tally × Bool) : Tally := bif p.2 then [] else () :: p.1
  have hop : Poly op := by
    exact Poly.choose Easy.snd.poly (Code.Poly.const ([] : Tally)) (show Poly (fun p : Tally × Bool => () :: p.1) from by fun_prop)
  have hfold := Poly.fold_left hop 3 1 (fun s l h => by
    have small (xs : List Bool) (q : Tally) :
        (xs.foldl (fun p b => op (p, b)) q).length ≤ q.length + xs.length := by
      induction xs generalizing q with
      | nil => simp
      | cons b xs ih =>
        simp only [List.foldl_cons, List.length_cons]
        apply (ih _).trans
        cases b <;> simp [op] <;> omega
    have hb := (small l s.2).trans (Nat.add_le_add_left h.length_le _)
    change size (l.foldl (fun p b => op (p, b)) s.2) ≤ _
    rw [size_tally, size_prod, P1ChkFinal.size_listBool, size_tally, pow_one]
    omega)
  exact ((show Poly (fun x : List Bool => x.reverse) from by fun_prop).pair
    (Code.Poly.const ([] : Tally))).compose hfold

theorem firstIndex_idxOf [DecidableEq A] [BEq A] [LawfulBEq A] (xs : List A) (x : A) :
    firstIndex (xs.map fun a => decide (x = a)) = tally (xs.idxOf x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [firstIndex, List.map_cons, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]
    by_cases h : x = a
    · subst a
      simp only [decide_true, Bool.cond_true, List.idxOf_cons_self]
      rfl
    · rw [List.idxOf_cons_ne _ (Ne.symm h)]
      simp only [h, decide_false, Bool.cond_false, tally_succ]

theorem poly_indexTally [DecidableEq A] [BEq A] [LawfulBEq A] [Inhabited A]
    (hp : Poly (fun p : A × A => decide (p.1 = p.2))) :
    Poly (fun q : List A × A => tally (q.1.idxOf q.2)) := by
  have h := Easy.exchange.poly.compose (Poly.push (default : A) default hp)
  simpa only [polyPush, Prod.swap, firstIndex_idxOf] using h.compose firstIndex_poly

/-- Remove repeated values in the same order as Mathlib's `List.dedup`. -/
theorem poly_lastDedup [DecidableEq A] [Inhabited A]
    (hp : Poly (fun p : A × A => decide (p.1 = p.2))) : Poly (List.dedup (α := A)) := by
  let add (p : List A × A) := bif p.1.any (fun x => decide (p.2 = x)) then p.1 else p.2 :: p.1
  have flags := Easy.exchange.poly.compose (Poly.push (default : A) default hp)
  have any := flags.compose (poly_anyList (p := id) Code.Poly.identity)
  have htest : Poly (fun p : List A × A => p.1.any (fun x => decide (p.2 = x))) := by
    simpa only [polyPush, Prod.swap, List.any_map, Function.comp_def, id_eq] using any
  have hstep : Poly add :=
    Poly.choose htest Easy.fst.poly (show Poly (fun p : List A × A => p.2 :: p.1) from by fun_prop)
  have fold := Poly.fold_left hstep 2 1 (fun q xs hs => by
    have bound (vs base : List A) :
        size (vs.foldl (fun s a => add (s, a)) base) ≤ size base + size vs := by
      induction vs generalizing base with
      | nil => simp only [List.foldl_nil, Nat.le_add_right]
      | cons a vs ih =>
        simp only [List.foldl_cons]
        have h : size (add (base, a)) ≤ size base + size a + 1 := by
          unfold add
          cases base.any (fun x => decide (a = x)) <;> simp only [Bool.cond_false, Bool.cond_true, size_cons] <;> omega
        rw [size_cons]
        exact (ih _).trans (by omega)
    obtain ⟨tail, htail⟩ := hs
    have h := size_append_right xs tail
    have h' := bound xs q.2
    rw [htail] at h
    rw [size_prod, pow_one]
    omega)
  have h := ((show Poly (fun xs : List A => xs.reverse) from by fun_prop).pair
    (Code.Poly.const ([] : List A))).compose fold
  convert h using 1
  funext xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← ih]
    have found : xs.dedup.any (fun y => decide (a = y)) = decide (a ∈ xs) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq, List.mem_dedup]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro ha
        exact ⟨a, ha, rfl⟩
    change (a :: xs).dedup = (bif xs.dedup.any (fun y => decide (a = y)) then xs.dedup else a :: xs.dedup)
    rw [found, List.dedup_cons]
    by_cases hh : a ∈ xs <;> simp [hh]

end P1SolCone.SolCone
