import P1SolF0R.Routing
import P1SolF0R.Chunk
import P1SolF0R.RouteInput

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1Wit P1ChkFinal.AstraC10 P1SolFactor P1SolFactor.Owner
open scoped P1ChkFinal.AstraC10

abbrev RoutingQuery := (Tally × Tally) × ((List Tally × List Tally) × (ℕ × ℕ × ℕ))

/-- Build the crossing arguments for a routing site of fixed type width. -/
def routeArgs (t : ℕ) (p : RoutingQuery) : CrossIn :=
  let (hc, nc) := p.1
  let (column, typ, lane) := p.2.2
  let m := hc.length + t
  let label := requestLabel ((tally t, hc, nc.length), (typ, lane))
  ((hc ++ tally (t - 1), p.2.1), (tally (min column (2 * m)), tally (min label (2 ^ t * nc.length))))

theorem routeArgs_poly (t : ℕ) : Poly (routeArgs t) := by
  have hl : Poly (fun p : RoutingQuery =>
      ((tally t, p.1.1, p.1.2.length), (p.2.2.2.1, p.2.2.2.2))) := by fun_prop
  have hc : Poly (fun p : RoutingQuery => p.2.2.1) := by fun_prop
  have hm : Poly (fun p : RoutingQuery => 2 * (p.1.1.length + t)) := by fun_prop
  have hhc : Poly (fun p : RoutingQuery => p.1.1) := by fun_prop
  have hnc : Poly (fun p : RoutingQuery => p.1.2) := by fun_prop
  have hcap := (Dom.const (size (X := RoutingQuery)) 2).mul
    ((P1ProgEng.SolKWR.length_dom hhc).add (Dom.const _ t))
  have hcol := P1ProgEng.SolKWR.poly_tallyMin hc hm hcap
  have hind := P1ProgEng.SolKWR.poly_tallyCap (2 ^ t) (hl.compose requestLabel_poly) hnc
  have hdim : Poly (fun p : RoutingQuery => p.1.1 ++ tally (t - 1)) :=
    Code.Poly.app (by fun_prop) (Code.Poly.const _)
  exact (hdim.pair (by fun_prop)).pair (hcol.pair hind)

theorem routeArgs_eq {t h : ℕ} (ht : 0 < t) (c : Fin (2 * (t + h)))
    (typ : BitWord t) (lane : BitWord h) (tables : List Tally × List Tally) :
    routeArgs t ((tally h, tally (2 ^ h)),
      (tables, c.val, (laneEquiv t typ).val, P1ChkFinal.bwNum lane)) =
      ((tally (t + h - 1), tables), tally c.val, tally (bitWordFinEquiv (t + h) (addrOf typ lane)).val) := by
  have hc : c.val ≤ 2 * (h + t) := by rw [Nat.add_comm h t]; exact c.isLt.le
  have ha : (bitWordFinEquiv (t + h) (addrOf typ lane)).val ≤ 2 ^ t * 2 ^ h := by
    rw [← Nat.pow_add]
    exact (bitWordFinEquiv (t + h) (addrOf typ lane)).isLt.le
  have hd : tally h ++ tally (t - 1) = tally (t + h - 1) := by
    change List.replicate h () ++ List.replicate (t - 1) () = List.replicate (t + h - 1) ()
    rw [List.replicate_append_replicate, show h + (t - 1) = t + h - 1 by omega]
  simp only [routeArgs, tally_length, requestLabel_eq, min_eq_left hc, min_eq_left ha, hd]

/-- Extract the relative block centers from one fetched trit column and start field. -/
def chunkCenters (r : ℕ) (p : Tally × (IntervalChunk × ℕ × ℕ)) : List ℕ :=
  let moves := tritColumn r ((p.1, p.2.1.1), p.2.2.2)
  let raw := startInChunk (p.2.1.2.1, p.2.2.1, p.2.2.2)
  centerValues (moves, (startParts (p.1.length, raw)).2)

theorem chunkCenters_poly (r : ℕ) : Poly (chunkCenters r) := by
  have hm : Poly (fun p : Tally × (IntervalChunk × ℕ × ℕ) => ((p.1, p.2.1.1), p.2.2.2)) := by
    fun_prop
  have hs : Poly (fun p : Tally × (IntervalChunk × ℕ × ℕ) => (p.2.1.2.1, p.2.2.1, p.2.2.2)) := by
    fun_prop
  have hlen : Poly (fun p : Tally × (IntervalChunk × ℕ × ℕ) => p.1.length) := by fun_prop
  have hp := (hlen.pair (hs.compose startInChunk_poly)).compose startParts_poly
  exact ((hm.compose (tritColumn_poly r)).pair hp.sndCompose).compose centerValues_poly

theorem chunkCenters_eq {K : Type} {I h : ℕ} (D : P1Wit.Dims) (u : List Bool)
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (i : Fin I) (k : K) (tape : ℕ)
    (hN : D.N = 2 ^ h) (ht : tape < D.r)
    (hmove : ∀ j : Fin (2 ^ h), rdTrit D u (i.val * 2 ^ h + j.val) tape =
      readAt 0 (intervalMoves σ i k) j.val)
    (hstart : rdStart D u i.val tape = P1Wit.zigzag (betaOf σ k (i.val * 2 ^ h))) :
    chunkCenters D.r (tally (2 ^ h), (witnessChunk D u i.val, D.bigW, tape)) = trueCenters σ i k := by
  simp only [chunkCenters, tally_length, tritColumn_eq D u σ i k tape hN ht hmove,
    startInChunk_eq D u i.val tape ht, hstart]
  exact centerValues_genuine σ i k _ rfl

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.routeArgs_eq
#print axioms P1SolF0R.SolReader.chunkCenters_eq
