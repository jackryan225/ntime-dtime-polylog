import P1ChkFinal.C10RcCodes
import OAI.Computability.MultitapeWeakETH.IncidenceProgram
import OAI.Computability.NearSquareRoot.PrecisionPlacedSlot

/-! Polynomial operations on the binary numbers and tables of a C10 ball. -/

namespace P1ChkFinal.AstraC10

open OAI.Computability.IntegerMultiplication Code Bits Carry Strip Staff
open OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
open private xorFigure from OAI.Computability.MultitapeWeakETH.IncidenceProgram

private abbrev reg (X : Type) [Codec X] : Regime X := ⟨size, send, Dom.base _⟩

variable {X A T : Type} [Codec X] [Codec A] [Codec T]

/-- `Poly.const` alone resolves to Mathlib's `_root_.Poly.const` (Dioph) here. -/
@[fun_prop] theorem poly_const (y : T) : Poly (fun _ : X => y) := Code.Poly.const y

private theorem asFigure {f : X → ℕ} (h : Poly f) : Figure (reg X) f :=
  ⟨fun x => binary (f x), h, fun x => value_binary _⟩

private theorem writeFigure {f : X → ℕ} (h : Figure (reg X) f) : Poly f :=
  h.write ((h.added (Figure.natural 1)).short_log)

@[fun_prop] theorem poly_addNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x + g x) :=
  writeFigure ((asFigure h).added (asFigure k))

@[fun_prop] theorem poly_mulNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x * g x) :=
  writeFigure ((asFigure h).multiplied (asFigure k))

@[fun_prop] theorem poly_subNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x - g x) :=
  writeFigure ((asFigure h).subtracted (asFigure k))

@[fun_prop] theorem poly_modNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x % g x) :=
  writeFigure ((asFigure h).modded (asFigure k))

@[fun_prop] theorem poly_divNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x / g x) :=
  writeFigure ((asFigure h).quotients (asFigure k))

@[fun_prop] theorem poly_xorNat {f g : X → ℕ} (h : Poly f) (k : Poly g) :
    Poly (fun x => f x ^^^ g x) :=
  writeFigure (xorFigure (asFigure h) (asFigure k))

private theorem lengthTally {l : X → List A} (h : Poly l) :
    Realizes (reg X) (fun x => (l x).length) := by
  change Poly (fun x => tally (l x).length)
  have q := h.compose (Easy.ruler (easy_id (X := List A))).poly
  convert q using 1
  funext x
  rw [← ruler_length (l x), recover_tally]

@[fun_prop] theorem poly_lengthNat {l : X → List A} (h : Poly l) :
    Poly (fun x => (l x).length) :=
  writeFigure (Figure.of_spoken (lengthTally h))

@[fun_prop] theorem poly_someValue {f : X → T} (h : Poly f) :
    Poly (fun x => some (f x)) := h.compose Easy.some.poly

@[fun_prop] theorem poly_defaultOption (d : T) {f : X → Option T} (h : Poly f) :
    Poly (fun x => (f x).elim d id) :=
  h.compose (OAI.Computability.NearSquareRoot.PhaseTable.easyOption d id Easy.identity).poly

@[fun_prop] theorem poly_readAt (d : T) {l : X → List T} {i : X → ℕ}
    (hl : Poly l) (hi : Poly i) : Poly (fun x => readAt d (l x) (i x)) := by
  let stop (x : X) := if i x < (l x).length then i x else (l x).length
  have len := lengthTally hl
  have fi := asFigure hi
  have fl := Figure.of_spoken len
  have fc : Figure (reg X) stop := fi.variant fl (fi.compare_ fl)
  have cap : Realizes (reg X) stop := fc.pay ((diameter _ len).mono (by
    intro x
    dsimp only [stop]
    split <;> omega))
  have u : Poly (fun x => tally (stop x)) := cap
  have q := (hl.pair u).compose (Iter.facile d).poly
  convert q using 1
  funext x
  by_cases good : i x < (l x).length
  · rw [show stop x = i x from if_pos good, Iter.search _ _ _ good]
    simp only [readAt, List.getElem?_eq_getElem good, Option.getD_some]
  · have le := Nat.le_of_not_lt good
    rw [show stop x = (l x).length from if_neg good]
    simp [readAt, List.getElem?_eq_none le, Iter.pick, tally_length]

/-- Tabulating polynomially many rows uses the length of an actual input list as clock. -/
def tabLike (l : X → List A) (f : X × ℕ → T) (x : X) : List T :=
  List.ofFn fun i : Fin (l x).length => f (x, i.val)

theorem poly_tabLike [Inhabited X] {l : X → List A} {f : X × ℕ → T}
    (hl : Poly l) (hf : Poly f) : Poly (tabLike l f) := by
  have cal : Poly (fun x => tally (l x).length) := lengthTally hl
  have natLen : Poly (fun t : Tally => t.length) := poly_lengthNat Poly.identity
  have indices := (cal.compose Iter.poly_line).compose (Poly.maps _ natLen)
  have q := (Poly.identity.pair indices).compose (Poly.push (default : X) (0 : ℕ) hf)
  change Poly (fun x => List.ofFn fun i : Fin (l x).length => f (x, i.val))
  simpa only [polyPush, Iter.lined, List.map_ofFn, Function.comp_def, tally_length] using q

theorem poly_fixedTab {n : ℕ} (f : Fin n → X → T) (h : ∀ i, Poly (f i)) :
    Poly (fun x => List.ofFn fun i => f i x) := by
  induction n with
  | zero => simpa only [List.ofFn_zero] using (poly_const ([] : List T))
  | succ n ih =>
    have rest := ih (fun i => f i.succ) (fun i => h i.succ)
    simpa only [List.ofFn_succ] using ((h 0).pair rest).compose Poly.cons

theorem poly_fixedSum {I : Type} [Fintype I] (f : I → X → ℕ) (hp : ∀ j, Poly (f j)) :
    Poly (fun x => ∑ j, f j x) := by
  classical
  have s (u : Finset I) : Poly (fun x => ∑ j ∈ u, f j x) := by
    induction u using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (poly_const 0)
    | insert j u hj ih => simpa only [Finset.sum_insert hj] using poly_addNat (hp j) ih
  exact s Finset.univ

/-- Fixed rational mass coefficients operate on binary widths, including a perfect-square boundary. -/
theorem poly_copies {I : Type} [Fintype I] (mass : I → ℚ) (L : ℕ) (w : I → X → ℕ)
    (hp : ∀ i, Poly (w i)) :
    Poly (fun x => OAI.Computability.VPVNP.MotifAdmission.copies mass (fun i => w i x) L) := by
  let e (x : X) := OAI.Computability.VPVNP.MotifAdmission.energy mass (fun i => w i x)
  let d := L ^ 2 * OAI.Computability.VPVNP.MotifAdmission.denominator mass
  have energy : Poly e := by
    unfold e OAI.Computability.VPVNP.MotifAdmission.energy
    apply poly_fixedSum
    intro i
    simpa only [pow_two] using
      poly_mulNat (poly_const (OAI.Computability.VPVNP.MotifAdmission.weight mass i))
        (poly_mulNat (hp i) (hp i))
  have en := asFigure energy
  have zero := Figure.natural (r := reg X) 0
  have one := Figure.natural (r := reg X) 1
  have root := ((en.subtracted one).quotients (Figure.natural d)).rooted
  have ceil := writeFigure ((root.added one).variant zero (zero.compare_ en))
  convert ceil using 1
  funext x
  change OAI.Computability.VPVNP.MotifAdmission.ceilRoot (e x) d =
    if 0 < e x then ((e x - 1) / d).sqrt + 1 else 0
  by_cases hz : e x = 0
  · simp [OAI.Computability.VPVNP.MotifAdmission.ceilRoot, hz]
  · simp only [OAI.Computability.VPVNP.MotifAdmission.ceilRoot, if_neg hz,
      OAI.Computability.VPVNP.MotifAdmission.floorRoot_eq, if_pos (Nat.pos_of_ne_zero hz)]

end P1ChkFinal.AstraC10
