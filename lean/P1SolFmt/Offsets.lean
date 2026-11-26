import P1SolFmt.LayoutSums
import OAI.Computability.IntegerMultiplication.Bits.Add
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Code.Pace

namespace P1SolFmt.SolFormat

open OAI.Computability.IntegerMultiplication
open Code P1Wit

private def sumWords (ws : List Bits.Word) : Bits.Word :=
  ws.foldl (fun a b => Bits.add (a, b)) []

private theorem sumWords_fold (ws : List Bits.Word) (seed : Bits.Word) :
    let result := ws.foldl (fun a b => Bits.add (a, b)) seed
    size result ≤ size seed + 3 * size ws ∧
      Bits.value result = Bits.value seed + (ws.map Bits.value).sum := by
  induction ws generalizing seed with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨Nat.le_add_right _ _, trivial⟩
  | cons w ws ih =>
    obtain ⟨hb, hv⟩ := ih (Bits.add (seed, w))
    dsimp only [List.foldl_cons] at hb hv ⊢
    refine ⟨?_, ?_⟩
    · rw [Bits.size_word (Bits.add (seed, w)), Bits.add_length] at hb
      rw [size_cons, Bits.size_word seed, Bits.size_word w]
      omega
    · rw [hv, Bits.add_val, List.map_cons, List.sum_cons, Nat.add_assoc]

private theorem sumWords_poly : Poly sumWords := by
  have step : Poly Bits.add := (Bits.easy_add Easy.identity).poly
  have fold := Poly.fold_left step 4 1 (fun p l h => by
    obtain ⟨q, hq⟩ := h
    have hsize := size_append_right l q
    have hbound := (sumWords_fold l p.2).1
    rw [pow_one, size_prod, ← hq]
    omega)
  exact (Poly.identity.pair (Code.Poly.const ([] : Bits.Word))).compose fold

private theorem value_sumWords (ws : List Bits.Word) :
    Bits.value (sumWords ws) = (ws.map Bits.value).sum := by
  simpa only [sumWords, Bits.value_nil, Nat.zero_add] using (sumWords_fold ws []).2

/-- Compute the offset by enumerating the preceding sections and summing their extents. -/
theorem offsets_with_value {d : Bits.Word → Dims} {s : Bits.Word → ℕ}
    (hs : Poly (fun x => tally (s x))) {word : Bits.Word × Tally → Bits.Word}
    (hword : Poly word)
    (hv : ∀ p, Bits.value (word p) = (d p.1).count p.2.length * (d p.1).width p.2.length) :
    ∃ out : Bits.Word → Bits.Word, Poly out ∧ ∀ x, Bits.value (out x) = (d x).off (s x) := by
  have hindex := Poly.identity.pair (hs.compose Iter.poly_line)
  have hlist := hindex.compose (Poly.push ([] : Bits.Word) ([] : Tally) hword)
  refine ⟨_, hlist.compose sumWords_poly, fun x => ?_⟩
  change Bits.value (sumWords (polyPush word (x, Iter.lineup (tally (s x))))) = (d x).off (s x)
  rw [value_sumWords, Iter.lined]
  simp only [polyPush, List.map_ofFn, Function.comp_def, hv, tally_length]
  exact offAt_ofFn _ _ _

end P1SolFmt.SolFormat
