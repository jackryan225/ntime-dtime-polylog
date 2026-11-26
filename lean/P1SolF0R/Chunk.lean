import P1SolF0R.Interval
import P1SolF0R.LocalBeta
import P1P5.KWRefresh
import P1SolC10P.Primitives

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

/-- The trit, start, previous-owner, and next-owner bits of a big interval. -/
abbrev IntervalChunk := List Bool × List Bool × List Bool × List Bool

def chunkAt (p : List (List Bool) × ℕ) : IntervalChunk :=
  let off := 4 * p.2
  (readAt [] p.1 off, readAt [] p.1 (off + 1), readAt [] p.1 (off + 2), readAt [] p.1 (off + 3))

theorem chunkAt_poly : Poly chunkAt := by
  unfold chunkAt
  fun_prop

def witnessChunk (D : Dims) (u : List Bool) (i : ℕ) : IntervalChunk :=
  chunkAt ((intervalReqs D.r D.I D.N D.bigW i).map (P1Batch.fetch u), 0)

theorem readNat_poly : Poly (fun p : List Bool × ℕ × ℕ => readNat p.1 p.2.1 p.2.2) := by
  have hd : Poly (fun p : List Bool × ℕ × ℕ => p.1.drop p.2.1) :=
    P1ProgEng.SolKWR.poly_drop (by fun_prop) Easy.fst.poly
  have ht : Poly (fun p : List Bool × ℕ × ℕ => (p.1.drop p.2.1).take p.2.2) :=
    P1ProgEng.SolKWR.poly_take (by fun_prop) hd
  simpa only [readNat, bitsVal_eq_bval] using poly_bval ht

def tritInChunk (r : ℕ) (p : List Bool × ℕ × ℕ) : ℕ :=
  readNat p.1 ((p.2.1 * r + p.2.2) * 2) 2

theorem tritInChunk_poly (r : ℕ) : Poly (tritInChunk r) :=
  (show Poly (fun p : List Bool × ℕ × ℕ => (p.1, (p.2.1 * r + p.2.2) * 2, (2 : ℕ))) from
    by fun_prop).compose readNat_poly

def tritColumn (r : ℕ) (p : (Tally × List Bool) × ℕ) : List ℕ :=
  (List.range p.1.1.length).map fun j => tritInChunk r (p.1.2, j, p.2)

theorem tritColumn_poly (r : ℕ) : Poly (tritColumn r) := by
  have hr : Poly (fun p : (Tally × List Bool) × ℕ => List.range p.1.1.length) := by
    simpa only [rangeIn, min_self] using
      poly_rangeIn (show Poly (fun p : (Tally × List Bool) × ℕ => p.1.1) from by fun_prop)
        (show Poly (fun p : (Tally × List Bool) × ℕ => p.1.1.length) from by fun_prop)
  have hv : Poly (fun p : ((Tally × List Bool) × ℕ) × ℕ => tritInChunk r (p.1.1.2, p.2, p.1.2)) :=
    (show Poly (fun p : ((Tally × List Bool) × ℕ) × ℕ => (p.1.1.2, p.2, p.1.2)) from
      by fun_prop).compose (tritInChunk_poly r)
  exact poly_mapWith hr hv

def startInChunk (p : List Bool × ℕ × ℕ) : ℕ := readNat p.1 (p.2.2 * p.2.1) p.2.1

theorem startInChunk_poly : Poly startInChunk :=
  (show Poly (fun p : List Bool × ℕ × ℕ => (p.1, p.2.2 * p.2.1, p.2.1)) from by fun_prop).compose
    readNat_poly

def ownerInChunk (p : List Bool × ℕ × ℕ × ℕ) : ℕ :=
  readNat p.1 ((p.2.2.1 * 3 + p.2.2.2) * p.2.1) p.2.1

theorem ownerInChunk_poly : Poly ownerInChunk :=
  (show Poly (fun p : List Bool × ℕ × ℕ × ℕ => (p.1, (p.2.2.1 * 3 + p.2.2.2) * p.2.1, p.2.1)) from
    by fun_prop).compose readNat_poly

theorem tritInChunk_eq (D : Dims) (u : List Bool) (i j tape : ℕ)
    (hj : j < D.N) (ht : tape < D.r) :
    tritInChunk D.r ((witnessChunk D u i).1, j, tape) = rdTrit D u (i * D.N + j) tape :=
  rdTrit_interval D u i j tape hj ht

theorem startInChunk_eq (D : Dims) (u : List Bool) (i tape : ℕ) (ht : tape < D.r) :
    startInChunk ((witnessChunk D u i).2.1, D.bigW, tape) = rdStart D u i tape :=
  rdStart_interval D u i tape ht

theorem prevInChunk_eq (D : Dims) (u : List Bool) (i tape δ : ℕ) (ht : tape < D.r) (hδ : δ < 3) :
    ownerInChunk ((witnessChunk D u i).2.2.1, D.bigW, tape, δ) = rdPrev D u i tape δ :=
  rdPrev_interval D u i tape δ ht hδ

theorem nextInChunk_eq (D : Dims) (u : List Bool) (i tape δ : ℕ) (ht : tape < D.r) (hδ : δ < 3) :
    ownerInChunk ((witnessChunk D u i).2.2.2, D.bigW, tape, δ) = rdNext D u i tape δ :=
  rdNext_interval D u i tape δ ht hδ

theorem tritColumn_eq {K : Type} {I h : ℕ} (D : Dims) (u : List Bool)
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K) (tape : ℕ)
    (hN : D.N = 2 ^ h) (ht : tape < D.r)
    (hmove : ∀ j : Fin (2 ^ h), rdTrit D u (ι.val * 2 ^ h + j.val) tape =
      readAt 0 (intervalMoves σ ι k) j.val) :
    tritColumn D.r ((tally (2 ^ h), (witnessChunk D u ι.val).1), tape) =
      intervalMoves σ ι k := by
  apply List.ext_getElem
  · simp only [tritColumn, tally_length, List.length_map, List.length_range, intervalMoves, List.length_ofFn]
  · intro j hj hk
    have hj' : j < 2 ^ h := by simpa only [intervalMoves, List.length_ofFn] using hk
    simp only [tritColumn, List.getElem_map, List.getElem_range]
    rw [tritInChunk_eq D u ι.val j tape (by rwa [hN]) ht, hN, hmove ⟨j, hj'⟩]
    simp only [readAt, List.getElem?_eq_getElem hk, Option.getD_some]

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.tritColumn_eq
