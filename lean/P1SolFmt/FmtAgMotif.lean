import P1SolFmt.FmtAgCore
import P1SolGreedy.MotifFormat

open OAI.Computability.IntegerMultiplication Code
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1SolGreedy.SolDemand

namespace P1SolFmt.SolFmtAg

private theorem motifRow_poly (all : Bool) {D : NumberWord → Dims}
    (h : AgFigures (fun p => (D p.1).lv p.2.length)) :
    Poly (fun p : LevelInput =>
      let L := (D p.1).lv p.2.length
      motifRow all (D p.1) p.2.length L.slotW (residualBits L)) := by
  let c := fun a : ℕ => 2 * 2 ^ a + 1
  have hslots := h.slotTable (fun a => bin (2 ^ a))
  have hcolours := h.slotTable (fun a => bin (2 ^ c a))
  have htag := h.slotTable (fun a => bin (2 ^ packingTagBits (2 ^ a)))
  have hradices := hslots.pair (hcolours.pair (htag.pair
    ((bin_poly h.residualRadix).pair (bin_poly h.packedRadix))))
  have hcolourCount := h.slotTable (fun a => bin (c a))
  have hslotTally := h.slotTable (fun a => tally (2 ^ a))
  have hcolourTally := h.slotTable (fun a => tally (2 ^ c a))
  have hwires : Poly (fun p : LevelInput =>
      if all then tally (2 ^ packedBits ((D p.1).lv p.2.length)) else []) := by
    cases all
    · exact Code.Poly.const []
    · exact h.packedTally
  have hpieces := h.slotTable (fun a => bin (PackingData.pieceCount (2 ^ a) (c a)))
  have hshifts := h.slotTable (fun a => colourShiftTable (c a))
  have harity := h.level.termArity.added (Carry.Figure.natural 1)
  have hstride := (bin_poly h.level.lanes).pair ((bin_poly h.level.termKeys).pair (bin_poly harity))
  unfold motifRow wireRadices
  exact hradices.pair (hcolourCount.pair (hslotTally.pair
    (hcolourTally.pair (hwires.pair (hpieces.pair (hshifts.pair hstride))))))

end P1SolFmt.SolFmtAg

open P1SolFmt.SolFmtAg

theorem P1SolFmt.fmtHypMotif_genuine (all : Bool) {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) :
    P1SolGreedy.SolDemand.FmtHypMotif all
      (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (fun n => P1Wrap.Params.m Kc (P1Int.lpTime a b n))
      (fun n ℓ =>
        (((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).slotW,
          ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).laneW -
            packingLaneBits
              ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
                termBias).lv ℓ).slotW 0)) := by
  unfold FmtHypMotif motifFormat
  exact (P1SolFmt.fmtHypGreedy_genuine A Kc V aM a b d bigBias termBias).pair
    (genuineRows_poly A Kc V aM a b d bigBias termBias
      (fun D ℓ => motifRow all D ℓ (D.lv ℓ).slotW (residualBits (D.lv ℓ))) (motifRow_poly all))

#print axioms P1SolFmt.fmtHypMotif_genuine
