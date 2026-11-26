import OAI.Computability.IntegerMultiplication.Carry.Figure

namespace P1SolFmt.SolFigure

open OAI.Computability.IntegerMultiplication
open Code Carry Staff Strip

/-- Polynomial time measured in the size of a coded input. -/
abbrev inputRegime (X : Type) [Codec X] : Regime X := ⟨size, send, Dom.base _⟩

theorem Figure.pullback {X Y : Type} [Codec X] [Codec Y]
    {f : X → Y} (hf : Poly f) {n : Y → ℕ} (hn : Figure (inputRegime Y) n) :
    Figure (inputRegime X) (fun x => n (f x)) := by
  obtain ⟨w, hw, he⟩ := hn
  exact ⟨fun x => w (f x), hf.compose (show Poly w from hw), fun x => he (f x)⟩

variable {X : Type} {r : Regime X} {f g : X → ℕ}

theorem realizes_of_tally {a : X → Tally} (ha : r.Has a) :
    Realizes r (fun x => (a x).length) := by
  have he : (fun x => tally (a x).length) = a := by
    funext x
    induction a x with
    | nil => rfl
    | cons h t ih =>
      cases h
      rw [List.length_cons, tally_succ, ih]
  change r.Has (fun x => tally (a x).length)
  rw [he]
  exact ha

theorem classified_congr {p q : X → Prop}
    (hp : Classified r p) (h : ∀ x, p x ↔ q x) : Classified r q := by
  obtain ⟨a, ha, he⟩ := hp
  exact ⟨a, ha, fun x => (h x).symm.trans (he x)⟩

theorem classified_eq (hf : Figure r f) (hg : Figure r g) :
    Classified r (fun x => f x = g x) := by
  apply classified_congr (((hf.subtracted hg).maximum (hg.subtracted hf)).compare_
    (Carry.Figure.natural (r := r) 1))
  intro x
  simp only [max_lt_iff]
  omega

/-- A finite vector of computations selected by a unary index. -/
theorem figure_lookup (rows : List (X → ℕ)) (hrows : ∀ f ∈ rows, Figure r f)
    (hdefault : Figure r g) (hf : Realizes r f) :
    Figure r (fun x => ((rows[f x]?).getD g) x) := by
  induction rows generalizing f with
  | nil => exact hdefault
  | cons head rows ih =>
    have hh := hrows head (List.mem_cons_self)
    have htail := ih (fun a ha => hrows a (List.mem_cons_of_mem _ ha))
      (hf.minused (Staff.Realizes.fix (r := r) 1))
    have hchoice := hh.variant htail (hf.below (Staff.Realizes.fix (r := r) 1))
    convert hchoice using 1
    funext x
    cases h : f x with
    | zero => simp only [List.getElem?_cons_zero, Option.getD_some, Nat.zero_lt_one, ite_true]
    | succ i =>
      have hn : ¬i + 1 < 1 := by omega
      simp only [List.getElem?_cons_succ, Nat.add_sub_cancel, ite_eq_right hn]

/-- Read one natural number from a fixed finite table with a unary index. -/
theorem figure_table (rows : List ℕ) (d : ℕ) (hf : Realizes r f) :
    Figure r (fun x => (rows[f x]?).getD d) := by
  have hrows : ∀ a ∈ rows.map (fun n => fun _ : X => n), Figure r a := by
    intro a ha
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ha
    exact Carry.Figure.natural n
  have h := figure_lookup _ hrows (Carry.Figure.natural (r := r) d) hf
  convert h using 1
  funext x
  rw [List.getElem?_map]
  cases rows[f x]? <;> rfl

theorem realizes_table (rows : List ℕ) (d : ℕ) (hf : Realizes r f) :
    Realizes r (fun x => (rows[f x]?).getD d) := by
  apply (figure_table rows d hf).pay ((Dom.const _ (rows.sum + d)).mono _)
  have hb (i : ℕ) : (rows[i]?).getD d ≤ rows.sum + d := by
    induction rows generalizing i with
    | nil => simp only [List.getElem?_nil, Option.getD_none, List.sum_nil, Nat.zero_add, le_rfl]
    | cons a t ih =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.getD_some, List.sum_cons]
        omega
      | succ i =>
        simp only [List.getElem?_cons_succ, List.sum_cons]
        exact (ih i).trans (by omega)
  exact fun x => hb (f x)

end P1SolFmt.SolFigure
