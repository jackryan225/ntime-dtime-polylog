import P1SolFmt.FmtAgCore
import P1SolGreedy.C6Format

open OAI.Computability.IntegerMultiplication Code
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1SolGreedy.SolDemand

namespace P1SolFmt.SolFmtAg

private theorem tagsRow_poly {D : NumberWord → Dims}
    (h : AgFigures (fun p => (D p.1).lv p.2.length)) :
    Poly (fun p : LevelInput =>
      let L := (D p.1).lv p.2.length
      tagRow L.slotW (residualBits L)) := by
  have htag := h.slotTable (fun a => bin (2 ^ packingTagBits (2 ^ a)))
  have hslots := h.slotTable (fun a => tally (2 ^ a))
  have htags := h.slotTable (fun a => tally (2 ^ packingTagBits (2 ^ a)))
  unfold tagRow
  exact ((bin_poly h.packedRadix).pair ((bin_poly h.residualRadix).pair htag)).pair
    (hslots.pair htags)

end P1SolFmt.SolFmtAg

open P1SolFmt.SolFmtAg

theorem P1SolFmt.fmtHypTags_genuine {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) :
    P1SolGreedy.SolDemand.FmtHypTags
      (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (fun n => P1Wrap.Params.m Kc (P1Int.lpTime a b n))
      (fun n ℓ =>
        (((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).slotW,
          ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).laneW -
            packingLaneBits
              ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
                termBias).lv ℓ).slotW 0)) := by
  unfold FmtHypTags tagFormat
  exact (P1SolFmt.fmtHypGreedy_genuine A Kc V aM a b d bigBias termBias).pair
    (genuineRows_poly A Kc V aM a b d bigBias termBias
      (fun D ℓ => tagRow (D.lv ℓ).slotW (residualBits (D.lv ℓ))) tagsRow_poly)

#print axioms P1SolFmt.fmtHypTags_genuine
