import P1SolFmt.FigureTools
import P1SolFmt.ScheduleMath
import Mathlib.Data.List.OfFn

namespace P1SolFmt.SolSchedule

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip SolFigure

variable {X A : Type} {r : Regime X} {t i : X → ℕ}

/-- A phase of the repeated schedule, with a fixed fallback at and beyond the final row. -/
theorem figure_phase (block : List A) (f : A → ℕ) (d : ℕ)
    (ht : Realizes r t) (hi : Realizes r i) :
    Figure r (fun x => ((blocks block (t x))[i x]?).elim d f) := by
  let hlen := Staff.Realizes.fix (r := r) block.length
  have h := (figure_table (block.map f) d (hi.rem hlen)).variant
    (Carry.Figure.natural d) (hi.below (hlen.times ht))
  convert h using 1
  funext x
  by_cases hx : i x < block.length * t x
  · rw [ite_eq_left hx, blocks_get block (t x) (i x) hx, List.getElem?_map]
    cases block[i x % block.length]? <;> rfl
  · have he : (blocks block (t x))[i x]? = none := by
      apply List.getElem?_eq_none
      rw [blocks_length]
      exact Nat.le_of_not_lt hx
    rw [he, ite_eq_right hx]
    rfl

theorem realizes_phase (block : List A) (f : A → ℕ) (d : ℕ)
    (ht : Realizes r t) (hi : Realizes r i) :
    Realizes r (fun x => ((blocks block (t x))[i x]?).elim d f) := by
  let hlen := Staff.Realizes.fix (r := r) block.length
  have h := (realizes_table (block.map f) d (hi.rem hlen)).select
    (Staff.Realizes.fix (r := r) d) (hi.below (hlen.times ht))
  convert h using 1
  funext x
  by_cases hx : i x < block.length * t x
  · rw [ite_eq_left hx, blocks_get block (t x) (i x) hx, List.getElem?_map]
    cases block[i x % block.length]? <;> rfl
  · have he : (blocks block (t x))[i x]? = none := by
      apply List.getElem?_eq_none
      rw [blocks_length]
      exact Nat.le_of_not_lt hx
    rw [he, ite_eq_right hx]
    rfl

private theorem partialBlock_figure (block : List A) (f : ℕ → ℕ)
    (hb : 0 < block.length) (hi : Realizes r i) :
    Figure r (fun x => f (i x % block.length)) := by
  have h := figure_table (List.ofFn (fun j : Fin block.length => f j.val)) 0
    (hi.rem (Staff.Realizes.fix block.length))
  convert h using 1
  funext x
  have hm : i x % block.length < (List.ofFn (fun j : Fin block.length => f j.val)).length := by
    rw [List.length_ofFn]
    exact Nat.mod_lt _ hb
  rw [List.getElem?_eq_getElem hm, Option.getD_some, List.getElem_ofFn]

private theorem partialBlock_realizes (block : List A) (f : ℕ → ℕ)
    (hb : 0 < block.length) (hi : Realizes r i) :
    Realizes r (fun x => f (i x % block.length)) := by
  have h := realizes_table (List.ofFn (fun j : Fin block.length => f j.val)) 0
    (hi.rem (Staff.Realizes.fix block.length))
  convert h using 1
  funext x
  have hm : i x % block.length < (List.ofFn (fun j : Fin block.length => f j.val)).length := by
    rw [List.length_ofFn]
    exact Nat.mod_lt _ hb
  rw [List.getElem?_eq_getElem hm, Option.getD_some, List.getElem_ofFn]

/-- The divisor for the complete blocks and the final partial block before a row. -/
theorem figure_prefixDivisor (block : List A) (f : A → ℕ) (hb : 0 < block.length)
    (hi : Realizes r i) :
    Figure r (fun x => (block.map f).prod ^ (i x / block.length) *
      (((block.take (i x % block.length)).map f).prod)) :=
  ((Carry.Figure.natural (r := r) (block.map f).prod).repeated
    (hi.dividing (Staff.Realizes.fix block.length))).multiplied
      (partialBlock_figure block (fun j => ((block.take j).map f).prod) hb hi)

/-- The unary sum of the lane losses before a row. -/
theorem realizes_prefixLoss (block : List A) (f : A → ℕ) (hb : 0 < block.length)
    (hi : Realizes r i) :
    Realizes r (fun x => (block.map f).sum * (i x / block.length) +
      ((block.take (i x % block.length)).map f).sum) :=
  ((Staff.Realizes.fix (r := r) (block.map f).sum).times
    (hi.dividing (Staff.Realizes.fix block.length))).plus
      (partialBlock_realizes block (fun j => ((block.take j).map f).sum) hb hi)

end P1SolFmt.SolSchedule
