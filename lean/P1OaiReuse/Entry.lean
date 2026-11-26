import OAI.Computability.MultitapeWeakETH.MotifFixed

/-!
# P1OaiReuse.Entry: the motif map entry as ONE polynomial-time tape program (reuse of OpenAI's program)

Owner: P1-lean-oaireuse. Row 1 of `research/p1/lean/OaiReuse/SPIKE-TABLE.md`.

`P1OaiReuse.entry_poly`: for every fixed block `B` (OpenAI's `FixedBlock`, so for `B.shrink` and `B.refresh` of the
compressor), every finite coefficient ring `R` and all parameter values `κ`, ONE function `val` that is `Code.Poly`
(a fixed `Prog Ltr` with a polynomial step bound in the size of its input tree, OpenAI's calculus) returns the motif
map entry `evalEntry κ (entry B hp w v j x y)` on the input `fixedInput B I` (OpenAI's encoding of the widths `w`, `v`,
the party `j` and the half-words `x`, `y`).

Proof: OpenAI's `MotifFields.fixed_program` (MultitapeWeakETH/MotifFixed.lean:30) returns the ordered list of parameter
names; `MotifConversion.runEntry_correct` (VPVNP/MotifConversion.lean:246) says that the product of `κ` over these
names is the entry. This file adds the table look-up of the names and the product in the finite ring.

This is the `Code.Poly` form of `P1P5.entry_eval` (P5/P1P5/EvalEntry.lean). The input format differs: the tree
`send (fixedInput B I)` in place of seven registers over `EntrySym R`.
-/

namespace P1OaiReuse

open OAI.Computability OAI.Computability.MultitapeWeakETH
open IntegerMultiplication Code VPVNP StackInterpreter MotifBlocks MotifGrid MotifConversion MotifSelector
open PairSimulation LocalHistory MotifFields
open scoped Classical

noncomputable section

variable {R : Type} [CommRing R] [Fintype R]

/-- Product of two ring letters. -/
def mulL (p : Label R × Label R) : Label R := ⟨p.1.val * p.2.val⟩

/-- Product of a list of ring letters (a left fold from `1`). -/
def prodL (l : List (Label R)) : Label R := l.foldl (fun x y => mulL (x, y)) ⟨1⟩

theorem foldl_mulL (l : List (Label R)) (c : Label R) :
    (l.foldl (fun x y => mulL (x, y)) c).val = c.val * (l.map Label.val).prod := by
  induction l generalizing c with
  | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons y l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih]
    simp only [mulL, mul_assoc]

theorem prodL_val (l : List (Label R)) : (prodL l).val = (l.map Label.val).prod := by
  rw [prodL, foldl_mulL]
  exact one_mul _

theorem prodL_poly : Poly (prodL (R := R)) := by
  have hf : Poly (mulL (R := R)) := (Easy.finite _).poly
  have hfold := Poly.fold_left (f := mulL (R := R)) hf (2 * Fintype.card R + 1) 0
    (fun s l _ => by
      rw [pow_zero, Nat.mul_one]
      exact label_size (l.foldl (fun x y => mulL (x, y)) s.2).val)
  exact (Poly.identity.pair (Code.Poly.const (⟨1⟩ : Label R))).compose hfold

/-- Table look-up: the letter with the given ordinal (unary), `1` beyond the table. -/
def decT {N : ℕ} (tbl : Fin N → Label R) (t : Tally) : Label R :=
  Iter.pick (⟨1⟩ : Label R) (List.ofFn tbl, t)

theorem decT_poly {N : ℕ} (tbl : Fin N → Label R) : Poly (decT tbl) :=
  ((Code.Poly.const (List.ofFn tbl)).pair Poly.identity).compose (Iter.facile (⟨1⟩ : Label R)).poly

theorem decT_tally {N : ℕ} (tbl : Fin N → Label R) (i : Fin N) : decT tbl (tally i.val) = tbl i :=
  Iter.entry tbl i _

/-- The value of an optional list of names: `0` if absent, else the product of the named letters. -/
def valOf {N : ℕ} (tbl : Fin N → Label R) (o : Option (List Tally)) : Label R :=
  bif o.elim false (fun _ => true) then prodL ((o.elim [] id).map (decT tbl)) else ⟨0⟩

theorem valOf_poly {N : ℕ} (tbl : Fin N → Label R) : Poly (valOf tbl) :=
  Poly.choose
    (NearSquareRoot.PhaseTable.easyOption false (fun _ : List Tally => true) (Easy.const true)).poly
    (((NearSquareRoot.PhaseTable.easyOption ([] : List Tally) id Easy.identity).poly.compose
      (Poly.maps _ (decT_poly tbl))).compose prodL_poly)
    (Code.Poly.const (⟨0⟩ : Label R))

theorem valOf_none {N : ℕ} (tbl : Fin N → Label R) : valOf tbl none = ⟨0⟩ := rfl

theorem valOf_some {N : ℕ} (tbl : Fin N → Label R) (l : List Tally) :
    valOf tbl (some l) = prodL (l.map (decT tbl)) := rfl

/-- The value of the names of a result of OpenAI's entry evaluator: `0` if absent, else the product of `κ`. -/
theorem valOf_names {α : Type} {N : ℕ} (tbl : Fin N → Label R) (num : α → Fin N) (κ : α → R)
    (hκ : ∀ x, (tbl (num x)).val = κ x) (r : Option (List α)) :
    (valOf tbl (r.map (List.map (tally ∘ fun x => (num x).val)))).val =
      r.elim 0 (fun names => (names.map κ).prod) := by
  cases r with
  | none => rfl
  | some ns =>
    show (valOf tbl (some (ns.map (tally ∘ fun x => (num x).val)))).val = (ns.map κ).prod
    rw [valOf_some, prodL_val, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left (fun x _ => ?_)
    show (decT tbl (tally (num x).val)).val = κ x
    rw [decT_tally]
    exact hκ x

/-- **The motif map entry is polynomial-time computable by one fixed tape program** (OpenAI's program, wrapped).
For every fixed block `B`, finite ring `R` and parameter values `κ`. -/
theorem entry_poly {k J D E : Type} [Field k] [Fintype J] [Fintype D] [Fintype E] [DecidableEq J]
    {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
    (B : FixedBlock k a b P (realWidths p) (realWidths q) H H') (hp : ∀ i, 0 < p i)
    (κ : (parameterData B).Entry → R) :
    ∃ val : FixedInput J → Label R, Poly val ∧ ∀ I : EntryInput B,
      (val (fixedInput B I)).val =
        MotifConversion.evalEntry κ
          (MotifConversion.entry B hp I.demand I.payload I.party I.demandBits I.supplyBits) := by
  letI : Fintype (parameterData B).Entry := Fintype.ofFinite _
  let e := Fintype.equivFin (parameterData B).Entry
  obtain ⟨eval, hpoly, hspec⟩ := fixed_program B hp (fun x => (e x).val)
  let tbl : Fin (Fintype.card (parameterData B).Entry) → Label R := fun i => ⟨κ (e.symm i)⟩
  refine ⟨fun x => valOf tbl (eval x), hpoly.compose (valOf_poly tbl), fun I => ?_⟩
  show (valOf tbl (eval (fixedInput B I))).val = _
  rw [hspec I]
  exact (valOf_names tbl (fun x => e x) κ
      (fun x => by show κ (e.symm (e x)) = κ x; rw [Equiv.symm_apply_apply]) _).trans
    (MotifConversion.runEntry_correct B κ hp I.demand I.payload I.party I.demandBits I.supplyBits)

end

end P1OaiReuse
