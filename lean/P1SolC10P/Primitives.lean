import P1C10.Prog
import P1ChkFinal.C10RcPoly
import P1ChkFinal.ProgC11
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolC10P.SolC10prog

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Staff
open OAI.Computability.IntegerMultiplication.Strip
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

private abbrev reg (X : Type) [Codec X] : Regime X := ⟨size, send, Dom.base _⟩

theorem asFigure {X : Type} [Codec X] {f : X → ℕ} (hf : Poly f) :
    Carry.Figure (reg X) f :=
  ⟨fun x => binary (f x), hf, fun x => value_binary (f x)⟩

theorem writeFigure {X : Type} [Codec X] {f : X → ℕ} (h : Carry.Figure (reg X) f) :
    Poly f :=
  h.write ((h.added (Carry.Figure.natural 1)).short_log)

theorem bval_eq_value (w : List Bool) : P1Batch.bval w = Bits.value w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [P1Batch.bval, Bits.value, ih] <;> rfl

theorem bitsVal_eq_bval (w : List Bool) : P1Wit.bitsVal w = P1Batch.bval w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [P1Wit.bitsVal, P1Batch.bval, ih] <;> rfl

theorem binary_eq_bin (n : ℕ) : binary n = P1ChkFinal.bin n := by
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

section Poly

variable {X A B : Type} [Codec X] [Codec A] [Codec B]

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

@[fun_prop] theorem poly_bval {f : X → List Bool} (hf : Poly f) :
    Poly (fun x => P1Batch.bval (f x)) :=
  writeFigure ⟨f, hf, fun x => (bval_eq_value (f x)).symm⟩

@[fun_prop] theorem poly_binary {f : X → ℕ} (hf : Poly f) :
    Poly (fun x => binary (f x)) := hf

@[fun_prop] theorem poly_lt {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := by
  have h : Poly (fun x => (binary (f x), binary (g x))) := hf.pair hg
  simpa only [Carry.lt_r, value_binary] using h.compose Carry.ltPoly

@[fun_prop] theorem poly_not {f : X → Bool} (hf : Poly f) :
    Poly (fun x => !(f x)) := hf.compose (Easy.finite Bool.not).poly

@[fun_prop] theorem poly_and {f g : X → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) :=
  (hf.pair hg).compose (Easy.finite (fun b : Bool × Bool => b.1 && b.2)).poly

@[fun_prop] theorem poly_or {f g : X → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x || g x) :=
  (hf.pair hg).compose (Easy.finite (fun b : Bool × Bool => b.1 || b.2)).poly

@[fun_prop] theorem poly_eqNat {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := by
  have h := poly_not (poly_or (poly_lt hf hg) (poly_lt hg hf))
  convert h using 1
  funext x
  by_cases hfg : f x = g x
  · simp only [hfg, lt_self_iff_false, decide_false, Bool.or_false, Bool.not_false, decide_true]
  · rcases lt_or_gt_of_ne hfg with hl | hl
    · simp only [hl, decide_true, Bool.true_or, Bool.not_true, hfg, decide_false]
    · simp only [hl, decide_true, Bool.or_true, Bool.not_true, hfg, decide_false]

@[fun_prop] theorem poly_if {f g : X → A} {test : X → Bool}
    (ht : Poly test) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if test x = true then f x else g x) := by
  convert Code.Poly.choose ht hf hg using 1
  funext x
  cases test x <;> simp only [ Bool.false_eq_true, ↓reduceIte, Bool.cond_false, Bool.cond_true]

@[fun_prop] theorem poly_min {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => min (f x) (g x)) := by
  have h := Code.Poly.choose (poly_lt hf hg) hf hg
  convert h using 1
  funext x
  by_cases e : f x < g x
  · simp only [e, decide_true, Bool.cond_true, min_eq_left e.le]
  · simp only [e, decide_false, Bool.cond_false, min_eq_right (Nat.le_of_not_lt e)]

@[fun_prop] theorem poly_clog {f : X → ℕ} (hf : Poly f) :
    Poly (fun x => Nat.clog 2 (f x)) :=
  writeFigure (Carry.Figure.of_spoken (asFigure hf).short_log)

theorem log_clog (n : ℕ) : Nat.log 2 n = Nat.clog 2 (n + 1) - 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have h1 := Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by decide) (n + 1)
    have h3 : Nat.log 2 (n + 1) < Nat.clog 2 (n + 1 + 1) :=
      (Nat.lt_clog_iff_pow_lt (b := 2) (by decide)).mpr (by omega)
    have h4 : Nat.clog 2 (n + 1 + 1) ≤ Nat.log 2 (n + 1) + 1 :=
      (Nat.clog_le_iff_le_pow (b := 2) (by decide)).mpr (by omega)
    change Nat.log 2 (n + 1) = Nat.clog 2 (n + 1 + 1) - 1
    omega

@[fun_prop] theorem poly_log {f : X → ℕ} (hf : Poly f) :
    Poly (fun x => Nat.log 2 (f x)) := by
  simpa only [log_clog] using
    poly_subNat (poly_clog (poly_addNat hf (poly_const 1))) (poly_const 1)

theorem poly_tally {f : X → ℕ} (hf : Poly f) (hb : Dom (size (X := X)) f) :
    Poly (fun x => tally (f x)) :=
  (asFigure hf).pay hb

/-- A binary exponent is bounded by a tally before it is used as a clock. -/
def pow2In (t : Tally) (e : ℕ) : ℕ := 2 ^ min e t.length

@[fun_prop] theorem poly_pow2In {t : X → Tally} {e : X → ℕ} (ht : Poly t) (he : Poly e) :
    Poly (fun x => pow2In (t x) (e x)) := by
  have p := (asFigure (poly_const (X := X) (2 : ℕ))).repeated
    (b := fun x => min (e x) (t x).length)
    (poly_tally (poly_min he (poly_lengthNat ht))
      (ht.length.mono (fun x => (min_le_right _ _).trans (duration (t x)).le)))
  exact writeFigure p

/-- Enumerate up to a numeric limit using an explicit upper clock. -/
def rangeIn (t : Tally) (n : ℕ) : List ℕ := List.range (min n t.length)

@[fun_prop] theorem poly_rangeIn [Inhabited X] {t : X → Tally} {n : X → ℕ}
    (ht : Poly t) (hn : Poly n) : Poly (fun x => rangeIn (t x) (n x)) := by
  have q := poly_tally (poly_min hn (poly_lengthNat ht))
    (ht.length.mono (fun x => (min_le_right _ _).trans (duration (t x)).le))
  convert poly_tabLike (f := fun z : X × ℕ => z.2) q Easy.snd.poly using 1
  funext x
  unfold tabLike rangeIn
  simp only [tally_length, Fin.val_cast]
  apply List.ext_getElem
  · simp only [List.length_range, List.length_ofFn]
  · intros
    simp only [List.getElem_range, List.getElem_ofFn]

@[fun_prop] theorem poly_flatten {f : X → List (List A)} (hf : Poly f) :
    Poly (fun x => (f x).flatten) := hf.compose Easy.flatten.poly

@[fun_prop] theorem poly_mapWith [Inhabited A] {f : X → List A} {g : X × A → B}
    (hf : Poly f) (hg : Poly g) [Inhabited X] :
    Poly (fun x => (f x).map (fun a => g (x, a))) :=
  (Code.Poly.identity.pair hf).compose (Code.Poly.push default default hg)

theorem poly_mapRight {V : Type} [Codec V] [Inhabited V] [Inhabited A]
    {f : V × A → B} (hf : Poly f) :
    Poly (fun p : V × List A => p.2.map (fun a => f (p.1, a))) :=
  Code.Poly.push default default hf

@[fun_prop] theorem poly_consVal {f : X → A} {g : X → List A}
    (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) := (hf.pair hg).compose Code.Poly.cons

@[fun_prop] theorem poly_single {f : X → A} (hf : Poly f) :
    Poly (fun x => [f x]) := (hf.pair (poly_const [])).compose Code.Poly.cons

@[fun_prop] theorem poly_all {f : X → List A} {p : A → Bool} (hf : Poly f) (hp : Poly p) :
    Poly (fun x => (f x).all p) := by
  let g : Bool × Bool → Bool := fun z => z.1 && z.2
  have hg := Code.Poly.fold_left (f := g) (Easy.finite g).poly 1 0 (by
    intro s l _
    change 1 ≤ 1 * (size s + 1) ^ 0
    simp only [pow_zero, Nat.mul_one, le_refl])
  have h := ((hf.compose (Code.Poly.maps p hp)).pair (poly_const true)).compose hg
  convert h using 1
  funext x
  suffices ∀ (l : List A) (b : Bool),
    (l.map p).foldl (fun x y => g (x, y)) b = (b && l.all p) by
    simpa only [Bool.true_and] using (this (f x) true).symm
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro b
    simp only [List.map_cons, List.foldl_cons, List.all_cons, ih, g, Bool.and_assoc]

end Poly

end P1SolC10P.SolC10prog
