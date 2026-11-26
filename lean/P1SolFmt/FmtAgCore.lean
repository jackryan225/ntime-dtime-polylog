import P1SolFmt.FmtG
import P1ChkFinal.BinBits

open OAI.Computability.IntegerMultiplication Code Carry Staff
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1Wrap P1ChkFinal P1SolGreedy.SolDemand

namespace P1SolFmt.SolFmtAg

open SolFigure SolFormat SolGeometry SolParameters
open private boundedFields genuineRow_bounds range_map_poly from P1SolFmt.FmtG

abbrev LevelInput := NumberWord × Tally

def residualBits (L : LevelDims) : ℕ :=
  L.laneW - packingLaneBits L.slotW 0

def packedBits (L : LevelDims) : ℕ :=
  packingLaneBits L.slotW (residualBits L)

theorem bin_poly {X : Type} [Codec X] {f : X → ℕ} (hf : Figure (inputRegime X) f) :
    Poly (fun x => bin (f x)) := by
  simpa only [bin_eq_bits] using figure_poly hf

/-- Values depending only on the degree use a fixed table for the schedule. -/
private theorem slotTable_poly {X Y : Type} [Codec X] [Codec Y] {a : X → ℕ}
    (ha : Figure (inputRegime X) a) {cap : ℕ} (hb : ∀ x, a x ≤ cap) (f : ℕ → Y) :
    Poly (fun x => f (a x)) := by
  have hp := ((bin_poly ha).pair
    (Code.Poly.const (X := X) ((List.range (cap + 1)).map fun j => (bin j, f j)))).compose
      (selectRow_poly (f 0))
  convert hp using 1
  funext x
  rw [selectRow_table, bval_bin, ite_eq_left (Nat.lt_succ_of_le (hb x))]

structure AgFigures (L : LevelInput → LevelDims) : Prop where
  level : LevelFigures (inputRegime LevelInput) L
  slotBound : ∃ cap : ℕ, ∀ p, (L p).slotW ≤ cap
  residualRadix : Figure (inputRegime LevelInput) (fun p => 2 ^ residualBits (L p))
  packedRadix : Figure (inputRegime LevelInput) (fun p => 2 ^ packedBits (L p))
  packedTally : Realizes (inputRegime LevelInput) (fun p => 2 ^ packedBits (L p))

theorem AgFigures.slotTable {Y : Type} [Codec Y] {L : LevelInput → LevelDims}
    (h : AgFigures L) (f : ℕ → Y) : Poly (fun p => f (L p).slotW) := by
  obtain ⟨cap, hb⟩ := h.slotBound
  exact slotTable_poly h.level.slotW hb f

private theorem packedBits_eq_max (L : LevelDims) :
    packedBits L = max (packingLaneBits L.slotW 0) L.laneW := by
  unfold packedBits residualBits
  rw [← packingLaneBits_add]
  omega

private theorem laneRadix_bound (t : ℕ) : 2 ^ Params.h t ≤ (Params.lam t + 1) ^ 10 := by
  have hpow : 2 ^ Params.p t ≤ Params.lam t + 1 := by
    by_cases h : Params.lam t = 0
    · rw [Params.p, h]
      decide
    · exact (Nat.pow_log_le_self 2 h).trans (Nat.le_succ _)
  calc
    2 ^ Params.h t ≤ 2 ^ (Params.p t * 10) := by
      apply Nat.pow_le_pow_right (by decide)
      unfold Params.h
      omega
    _ = (2 ^ Params.p t) ^ 10 := pow_mul 2 _ _
    _ ≤ (Params.lam t + 1) ^ 10 := Nat.pow_le_pow_left hpow _

private theorem agFigures_of_level {L : LevelInput → LevelDims} {t : LevelInput → ℕ}
    (ht : Figure (inputRegime LevelInput) t) (hL : LevelFigures (inputRegime LevelInput) L)
    (cap : ℕ) (hslot : ∀ p, (L p).slotW ≤ cap) (hlane : ∀ p, (L p).laneW ≤ Params.h (t p)) :
    AgFigures L := by
  let R := inputRegime LevelInput
  have hw : Realizes R (fun p => (L p).laneW) :=
    hL.laneW.pay ((diameter _ (realizes_h ht)).mono hlane)
  have hbase : Realizes R (fun p => packingLaneBits (L p).slotW 0) :=
    slotTable_poly hL.slotW hslot (fun a => tally (packingLaneBits a 0))
  have hres : Realizes R (fun p => residualBits (L p)) := hw.minused hbase
  have hpacked : Figure R (fun p => 2 ^ packedBits (L p)) := by
    simpa only [packedBits, packingLaneBits_add] using
      (Carry.Figure.natural (r := R) 2).repeated (hbase.plus hres)
  have hfixed : Realizes R (fun p => 2 ^ packingLaneBits (L p).slotW 0) :=
    slotTable_poly hL.slotW hslot (fun a => tally (2 ^ packingLaneBits a 0))
  have hbudget := (diameter _ hfixed).add
    ((diameter _ ((realizes_lam ht).plus (Staff.Realizes.fix 1))).pow 10)
  refine ⟨hL, ⟨cap, hslot⟩, (Carry.Figure.natural 2).repeated hres, hpacked,
    hpacked.pay (hbudget.mono ?_)⟩
  intro p
  rw [packedBits_eq_max]
  refine max_rec' (fun e : ℕ =>
    2 ^ e ≤ 2 ^ packingLaneBits (L p).slotW 0 + (Params.lam (t p) + 1) ^ 10) ?_ ?_
  · exact Nat.le_add_right _ _
  · exact ((Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (hlane p)).trans
      (laneRadix_bound (t p))).trans (Nat.le_add_left _ _)

/-- Level rows from the fixed schedule, indexed by their binary level numbers. -/
theorem genuineRows_poly {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ)
    {Y : Type} [Codec Y] (row : Dims → ℕ → Y)
    (hrow : ∀ {D : NumberWord → Dims}, AgFigures (fun p => (D p.1).lv p.2.length) →
      Poly (fun p : LevelInput => row (D p.1) p.2.length)) :
    Poly (fun w : NumberWord =>
      let D := genuineDims A Kc V aM (P1Int.lpTime a b (P1Batch.bval w))
        (a * (P1Batch.bval w ^ 2 + 1)) d bigBias termBias
      (List.range (D.top + 1)).map (fun i => (bin i, row D i))) := by
  let t := fun w : NumberWord => P1Int.lpTime a b (P1Batch.bval w)
  let g := fun w : NumberWord => a * (P1Batch.bval w ^ 2 + 1)
  let D := fun w => genuineDims A Kc V aM (t w) (g w) d bigBias termBias
  have ht : Figure (inputRegime NumberWord) t := by
    simpa only [t, P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hg : Figure (inputRegime NumberWord) g := by
    let num := fun n => Carry.Figure.natural (r := inputRegime NumberWord) n
    simpa only [g, pow_two] using (num a).multiplied ((figure_bval.multiplied figure_bval).added (num 1))
  have wd : DimsFigures (inputRegime NumberWord) D :=
    genuineDims_figures A Kc V aM d bigBias termBias ht hg
  have hfst : Poly (Prod.fst : LevelInput → NumberWord) := Easy.fst.poly
  have ht' := SolFigure.Figure.pullback hfst ht
  have sd : DimsFigures (inputRegime LevelInput) (fun p => D p.1) :=
    genuineDims_figures A Kc V aM d bigBias termBias ht' (SolFigure.Figure.pullback hfst hg)
  have hi : Realizes (inputRegime LevelInput) (fun p => p.2.length) :=
    realizes_of_tally Easy.snd.poly
  obtain ⟨cap, hcap⟩ := genuineRow_bounds S
  have hb (p : LevelInput) :
      boundedFields ((D p.1).lv p.2.length) ≤ cap ∧ ((D p.1).lv p.2.length).laneW ≤ Params.h (t p.1) :=
    hcap _ _ _ _
  have hslot (p : LevelInput) : ((D p.1).lv p.2.length).slotW ≤ cap := by
    have h := (hb p).1
    unfold boundedFields at h
    omega
  have hlevel := agFigures_of_level ht' (sd.level hi) cap hslot (fun p => (hb p).2)
  exact range_map_poly ([] : NumberWord) (f := fun w i => (bin i, row (D w) i))
    (wd.top.plus (Staff.Realizes.fix 1)) ((bin_poly (Carry.Figure.of_spoken hi)).pair (hrow hlevel))

end P1SolFmt.SolFmtAg
