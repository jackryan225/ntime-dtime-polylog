import P1P5.LevelsPolyDefs
import P1OaiReuse.Plan

open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter

namespace P1ProgEng.SolLevPoly

noncomputable section

variable {R : Type} [CommRing R] [Fintype R]

private abbrev State (R : Type) := List (Label R)
private abbrev Term (R : Type) := Label R × List Tally
private abbrev Entry (R : Type) := List (Term R)
private abbrev Level (R : Type) := List (Entry R)

/-- A pointer beyond the end of the state reads as zero. -/
private def lookup (p : State R × Tally) : Label R :=
  Iter.pick ⟨0⟩ p

private theorem lookup_poly : Poly (lookup (R := R)) :=
  (Iter.facile (⟨0⟩ : Label R)).poly

private def evalTerm (p : State R × Term R) : Label R :=
  P1OaiReuse.mulL (P1OaiReuse.prodL (polyPush lookup (p.1, p.2.2)), p.2.1)

private theorem evalTerm_poly : Poly (evalTerm (R := R)) := by
  have hs : Poly (Prod.fst : State R × Term R → State R) := Easy.fst.poly
  have ht : Poly (Prod.snd : State R × Term R → Term R) := Easy.snd.poly
  have hp := (hs.pair ht.sndCompose).compose (Poly.push [] [] lookup_poly)
  exact (hp.compose P1OaiReuse.prodL_poly).pair ht.fstCompose
    |>.compose (Easy.finite (P1OaiReuse.mulL (R := R))).poly

private def evalEntry (p : State R × Entry R) : Label R :=
  P1OaiReuse.sumL (polyPush evalTerm p)

private theorem evalEntry_poly : Poly (evalEntry (R := R)) :=
  (Poly.push [] (⟨0⟩, []) evalTerm_poly).compose P1OaiReuse.sumL_poly

private def evalLevel (p : State R × Level R) : State R :=
  polyPush evalEntry p

private theorem evalLevel_poly : Poly (evalLevel (R := R)) :=
  Poly.push [] [] evalEntry_poly

private def evalLevels (p : List (Level R) × State R) : State R :=
  p.1.foldl (fun st L => evalLevel (st, L)) p.2

private def labelListFactor (R : Type) [Fintype R] : ℕ :=
  2 * Fintype.card R + 2

omit [CommRing R] in
private theorem labelListFactor_pos : 0 < labelListFactor R := by
  unfold labelListFactor
  omega

/-- A level output has one bounded-size letter for each entry of the level. -/
private theorem size_map_label {X : Type} [Codec X] (f : X → Label R) (l : List X) :
    size (l.map f) ≤ labelListFactor R * size l := by
  induction l with
  | nil =>
    simp only [List.map_nil, size_nil, Nat.mul_one]
    exact labelListFactor_pos
  | cons a l ih =>
    have ha : size (f a) + 1 ≤ labelListFactor R := by
      have h := label_size (f a).val
      change size (f a) ≤ 2 * Fintype.card R + 1 at h
      unfold labelListFactor
      omega
    simp only [List.map_cons, size_cons, Nat.mul_add, Nat.mul_one]
    omega

private theorem evalLevels_size_le (B : ℕ) (Ls : List (Level R)) (st : State R)
    (hstart : size st ≤ labelListFactor R * B)
    (hlevel : ∀ L ∈ Ls, size L ≤ B) :
    size (evalLevels (Ls, st)) ≤ labelListFactor R * B := by
  induction Ls generalizing st with
  | nil => exact hstart
  | cons L Ls ih =>
    change size (evalLevels (Ls, evalLevel (st, L))) ≤ labelListFactor R * B
    apply ih
    · exact (size_map_label (fun e => evalEntry (st, e)) L).trans
        (Nat.mul_le_mul_left _ (hlevel L List.mem_cons_self))
    · exact fun L' hm => hlevel L' (List.mem_cons_of_mem _ hm)

private theorem evalLevels_poly : Poly (evalLevels (R := R)) := by
  apply Poly.fold_left evalLevel_poly (labelListFactor R) 1
  intro s ls hp
  change size (evalLevels (ls, s.2)) ≤ _
  rw [pow_one]
  apply evalLevels_size_le
  · have hs : size s.2 ≤ size s + 1 := by
      rw [size_prod]
      omega
    exact hs.trans (Nat.le_mul_of_pos_left _ labelListFactor_pos)
  · intro L hL
    have hs := (size_bel (hp.subset hL)).le
    rw [size_prod]
    omega

omit [Fintype R] in
private theorem lookup_enc (st : List R) (i : ℕ) :
    lookup (st.map Label.mk, tally i) = Label.mk (st.getD i 0) := by
  simp only [lookup, Iter.pick, tally_length, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases st[i]? <;> rfl

private theorem evalTerm_enc (st : List R) (p : R × List ℕ) :
    (evalTerm (st.map Label.mk, (Label.mk p.1, p.2.map tally))).val =
      (p.2.map fun i => st.getD i 0).prod * p.1 := by
  simp only [evalTerm, polyPush, P1OaiReuse.mulL, P1OaiReuse.prodL_val, List.map_map,
    Function.comp_def, lookup_enc]

private theorem evalEntry_enc (st : List R) (e : List (R × List ℕ)) :
    evalEntry (st.map Label.mk, e.map fun p => (Label.mk p.1, p.2.map tally)) =
      Label.mk (P1P5.entryEval st e) := by
  apply Label.ext
  simp only [evalEntry, polyPush, P1OaiReuse.sumL_val, P1P5.entryEval, List.map_map,
    Function.comp_def, evalTerm_enc]

private theorem evalLevel_enc (st : List R) (L : P1P5.Level R) :
    evalLevel (st.map Label.mk, P1P5.encLevel L) = (P1P5.stepEval L st).map Label.mk := by
  simp only [evalLevel, polyPush, P1P5.encLevel, P1P5.stepEval, List.map_map,
    Function.comp_def, evalEntry_enc]

private theorem evalLevels_enc (Ls : List (P1P5.Level R)) (st : List R) :
    evalLevels (Ls.map P1P5.encLevel, st.map Label.mk) =
      (P1P5.runLevels Ls st).map Label.mk := by
  induction Ls generalizing st with
  | nil => rfl
  | cons L Ls ih =>
    change evalLevels (Ls.map P1P5.encLevel, evalLevel (st.map Label.mk, P1P5.encLevel L)) =
      (P1P5.runLevels Ls (P1P5.stepEval L st)).map Label.mk
    rw [evalLevel_enc, ih]

end

end P1ProgEng.SolLevPoly

theorem P1ProgEng.runLevels_poly' {R : Type} [CommRing R] [Fintype R] :
    ∃ val : List (List (List (Label R × List Tally))) × List (Label R) → List (Label R), Poly val ∧
      ∀ (Ls : List (P1P5.Level R)) (st : List R),
        val (Ls.map P1P5.encLevel, st.map Label.mk) = (P1P5.runLevels Ls st).map Label.mk :=
  ⟨P1ProgEng.SolLevPoly.evalLevels, P1ProgEng.SolLevPoly.evalLevels_poly,
    P1ProgEng.SolLevPoly.evalLevels_enc⟩

#print axioms P1ProgEng.runLevels_poly'
