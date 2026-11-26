import P1Wrap.OuterSpec
import P1Hier.UMachine
import OAI.Computability.IntegerMultiplication.Bits.Small

/-! # Decoding unary table indices in the outer guess

The transducer proposes a list of indices. The validator checks its canonical
encoding against the input and checks every remaining bit for zero. This makes
soundness independent of what the counter does on an overlong run of ones.
-/

namespace P1Wrap.W3.AstraOuter

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Hier (Entry)

noncomputable section

private def start (k : ℕ) : Fin (k + 1) := ⟨0, Nat.zero_lt_succ _⟩

private def indexStep (k : ℕ) : Bool → Fin (k + 1) → Fin (k + 1) × List (Fin k)
  | true, q => (⟨min (q.val + 1) k, Nat.lt_succ_of_le (min_le_right _ _)⟩, [])
  | false, q =>
      (start k, if h : q.val = 0 then [] else [⟨q.val - 1, by have := q.isLt; omega⟩])

private def scanFrom {k : ℕ} (q : Fin (k + 1)) (z : List Bool) : List (Fin k) :=
  (machine (indexStep k) (z, q)).1

private def indices (k : ℕ) (z : List Bool) : List (Fin k) := scanFrom (start k) z

private theorem scan_cons {k : ℕ} (q : Fin (k + 1)) (b : Bool) (z : List Bool) :
    scanFrom q (b :: z) = (indexStep k b q).2 ++ scanFrom (indexStep k b q).1 z := by
  unfold scanFrom
  rw [machine_cons]

private theorem scan_ones {k : ℕ} (q t : ℕ) (h : q + t ≤ k) (z : List Bool) :
    scanFrom (⟨q, by omega⟩ : Fin (k + 1)) (List.replicate t true ++ z) =
      scanFrom (⟨q + t, by omega⟩ : Fin (k + 1)) z := by
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    have hq : q + 1 ≤ k := by omega
    have hqt : q + 1 + t ≤ k := by omega
    have e : q + 1 + t = q + (t + 1) := by omega
    rw [List.replicate_succ, List.cons_append, scan_cons]
    simp only [indexStep, Nat.min_eq_left hq, List.nil_append]
    exact (ih (q + 1) hqt).trans (congrArg (fun s : Fin (k + 1) => scanFrom s z) (Fin.ext e))

private theorem stop_index {k : ℕ} (i : Fin k) :
    indexStep k false ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = (start k, [i]) := by
  rcases i with ⟨v, hv⟩
  simp [indexStep]

private theorem scan_row {k : ℕ} (i : Fin k) (z : List Bool) :
    indices k (List.replicate (i.val + 1) true ++ false :: z) = i :: indices k z := by
  have h : 0 + (i.val + 1) ≤ k := by have := i.isLt; omega
  calc
    _ = scanFrom (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (k + 1)) (false :: z) := by
      simpa only [indices, start, Nat.zero_add] using scan_ones 0 (i.val + 1) h (false :: z)
    _ = _ := by rw [scan_cons, stop_index i]; rfl

private theorem scan_zeros (k r : ℕ) : indices k (List.replicate r false) = [] := by
  have hs : indexStep k false (start k) = (start k, []) := by simp [indexStep, start]
  unfold indices
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, scan_cons, hs]
    exact ih

private def rowAt (tbl : List Entry) (i : Fin tbl.length) : Entry := tbl.get i

/-- Rows proposed by the finite-state transducer, before validation. -/
def parsedRows (tbl : List Entry) (z : List Bool) : List Entry :=
  (indices tbl.length z).map (rowAt tbl)

theorem parsedRows_mem (tbl : List Entry) (z : List Bool) :
    ∀ e ∈ parsedRows tbl z, e ∈ tbl := by
  intro e he
  obtain ⟨i, _, hi⟩ := List.mem_map.mp he
  rw [← hi]
  exact List.get_mem tbl i

/-- Completeness of the candidate generator on the entire specified layout. -/
theorem parsedRows_enc (tbl : List Entry) (τ : List Entry) (r : ℕ)
    (hm : ∀ e ∈ τ, e ∈ tbl) :
    parsedRows tbl (encT tbl τ ++ List.replicate r false) = τ := by
  induction τ with
  | nil => simp only [encT_nil, List.nil_append, parsedRows, scan_zeros, List.map_nil]
  | cons e τ ih =>
    have he : e ∈ tbl := hm e List.mem_cons_self
    have ht : ∀ f ∈ τ, f ∈ tbl := fun f hf => hm f (List.mem_cons_of_mem _ hf)
    let i : Fin tbl.length := ⟨tbl.idxOf e, List.idxOf_lt_length_of_mem he⟩
    have hi : rowAt tbl i = e := List.getElem_idxOf (List.idxOf_lt_length_of_mem he)
    rw [encT_cons, List.append_assoc, List.cons_append]
    change (indices tbl.length
        (List.replicate (i.val + 1) true ++ false :: (encT tbl τ ++ List.replicate r false))).map
          (rowAt tbl) = e :: τ
    rw [scan_row i, List.map_cons, hi]
    exact congrArg (List.cons e) (ih ht)

private theorem easy_indices (k : ℕ) : Easy (indices k) := by
  have h : Easy (fun z : List Bool => (z, start k)) := easy_id.pair (Easy.const _)
  exact Easy.fstCompose (Easy.machine (step := indexStep k) h)

theorem easy_parsedRows (tbl : List Entry) : Easy (parsedRows tbl) :=
  easy_map (easy_indices tbl.length) (Easy.finite (rowAt tbl))

private def wordAt (tbl : List Entry) (i : Fin tbl.length) : List Bool :=
  List.replicate (tbl.idxOf (rowAt tbl i) + 1) true ++ [false]

private theorem render_indices (tbl : List Entry) (is : List (Fin tbl.length)) :
    (is.map (wordAt tbl)).flatten = encT tbl (is.map (rowAt tbl)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.flatten_cons, ih, encT_cons, wordAt, List.append_assoc,
      List.singleton_append]

theorem easy_render (tbl : List Entry) : Easy (fun z => encT tbl (parsedRows tbl z)) := by
  have h := easy_flatten (easy_map (easy_indices tbl.length) (Easy.finite (wordAt tbl)))
  exact P1Hier.UM.easy_congr h (fun z => congrArg send (render_indices tbl (indices tbl.length z)))

private def prefixCut (p : List Bool × List Bool) : List Bool × List Bool :=
  cutLists (ruler p.1, p.2)

/-- The second word consists of the first word followed by zero padding. -/
private def zerosAfter (p : List Bool × List Bool) : Bool :=
  decide ((prefixCut p).1 = p.1) && P1Hier.UM.allFalse (prefixCut p).2

private theorem zerosAfter_iff (v z : List Bool) :
    zerosAfter (v, z) = true ↔ ∃ r, z = v ++ List.replicate r false := by
  simp only [zerosAfter, prefixCut, cutLists, ruler_length, Bool.and_eq_true_iff,
    decide_eq_true_iff, P1Hier.UM.allFalse_iff]
  constructor
  · rintro ⟨hp, hz⟩
    have he : z.drop v.length = List.replicate (z.drop v.length).length false :=
      List.eq_replicate_iff.mpr ⟨rfl, hz⟩
    refine ⟨(z.drop v.length).length, ?_⟩
    calc
      z = z.take v.length ++ z.drop v.length := (List.take_append_drop _ _).symm
      _ = v ++ List.replicate (z.drop v.length).length false := congrArg₂ List.append hp he
  · rintro ⟨r, rfl⟩
    rw [List.take_left, List.drop_left]
    exact ⟨rfl, fun _ hb => List.eq_of_mem_replicate hb⟩

private theorem easy_zerosAfter : Easy zerosAfter := by
  have h : Easy prefixCut := easy_cut ((Easy.ruler Easy.fst).pair Easy.snd)
  have he := ((Easy.fstCompose h).pair Easy.fst).compose P1Hier.easy_eqBits
  exact P1Hier.UM.easy_and he ((Easy.sndCompose h).compose P1Hier.UM.easy_allFalse)

def layoutOK (tbl : List Entry) (z : List Bool) : Bool :=
  zerosAfter (encT tbl (parsedRows tbl z), z)

theorem easy_layoutOK (tbl : List Entry) : Easy (layoutOK tbl) :=
  ((easy_render tbl).pair easy_id).compose easy_zerosAfter

/-- Eliminates the transcript and padding witnesses, keeping any downstream check. -/
theorem layout_check_iff (tbl : List Entry) (z : List Bool) (Q : List Entry → Prop) :
    (layoutOK tbl z = true ∧ Q (parsedRows tbl z)) ↔
      ∃ (τ : List Entry) (r : ℕ), (∀ e ∈ τ, e ∈ tbl) ∧
        z = encT tbl τ ++ List.replicate r false ∧ Q τ := by
  constructor
  · rintro ⟨hok, hQ⟩
    obtain ⟨r, hr⟩ := (zerosAfter_iff _ _).mp hok
    exact ⟨_, r, parsedRows_mem tbl z, hr, hQ⟩
  · rintro ⟨τ, r, hm, hr, hQ⟩
    have he : parsedRows tbl z = τ := by rw [hr]; exact parsedRows_enc tbl τ r hm
    refine ⟨(zerosAfter_iff _ _).mpr ⟨r, ?_⟩, he.symm ▸ hQ⟩
    rw [he]
    exact hr

end

end P1Wrap.W3.AstraOuter
