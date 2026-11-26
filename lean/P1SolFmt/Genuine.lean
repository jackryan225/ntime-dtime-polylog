import P1Wit.SpaceFacts
import P1SolFmt.Parameters
import P1SolFmt.Rows
import P1Wrap.ParamAlg

namespace P1SolFmt.SolFormat

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1Wrap
open SolFigure SolParameters SolGeometry SolSchedule
open private levelDims layoutRows runPhases blockPhases from P1Wit.SpaceFacts

variable {X : Type} {r : Regime X}

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable {t g : X → ℕ}

private theorem runPhases_eq_blocks (S : BlockSchedule k) (n : ℕ) :
    runPhases S n = blocks (blockPhases S) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [runPhases, blocks, ih]

private theorem block_length_pos (S : BlockSchedule k) : 0 < (blockPhases S).length := by
  unfold blockPhases
  simp only [List.length_append, List.length_singleton, Nat.zero_lt_succ]

private theorem genuineRowFigures (S : BlockSchedule k) {p g n i : X → ℕ}
    (hp : Figure r p) (hg : Realizes r g) (hn : Realizes r n) (hi : Realizes r i) :
    LevelFigures r (fun x => ((layoutRows S (p x) (g x) (runPhases S (n x)))[i x]?).getD
      (levelDims S.expanderExponent 0 0 0 none)) := by
  have h := rowFigures (blockPhases S) (block_length_pos S)
    Phase.exponent Phase.laneLoss Phase.divisor Phase.shrink (S.degreeExponent 0)
    S.expanderExponent packingTagBits (levelDims S.expanderExponent) (fun _ _ _ _ => rfl)
    hp hg hn hi
  convert h using 1
  funext x
  rw [runPhases_eq_blocks]
  apply indexedBlockRows
  · intro p g
    rfl
  · intro p g ph xs
    rfl

theorem genuineDims_figures (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine)
    (aM d bigBias termBias : ℕ) (ht : Figure r t) (hg : Figure r g) :
    DimsFigures r (fun x => genuineDims A K V aM (t x) (g x) d bigBias termBias) := by
  let num := fun n => Carry.Figure.natural (r := r) n
  let fix := fun n => Staff.Realizes.fix (r := r) n
  have hT := realizes_T K ht
  have hH := realizes_h ht
  let tapes := Fintype.card V.K
  let externalCount := Fintype.card (P1Net.Ext V.K)
  have hP : Figure r (fun x => initialPositions V aM (t x)) :=
    figure_initial_positions aM tapes externalCount ht
  have hW : Figure r (fun x => P1Net.tupWidth V (Params.B (t x))) :=
    figure_tuple_width externalCount (Fintype.card V.Γ) (Fintype.card V.Q) tapes ht
  refine ⟨?_, num tapes, figure_I aM ht, figure_N ht, figure_guess_blocks ht hg,
    figure_big_width bigBias ht, figure_small_width termBias A.growthConstant hT hW,
    figure_chain_length S.positionFactor hP hT, num (Nat.clog 2 d), fun hi =>
      genuineRowFigures S hP hH hT hi⟩
  change Realizes r (fun x => (runPhases S (Params.T K (t x))).length)
  simpa only [runPhases_eq_blocks, blocks_length] using ((fix (blockPhases S).length).times hT)

/-- Exact format for the genuine dimensions, with binary computations of time and guess length. -/
theorem fmtHyp_genuine_of (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine)
    (aM d bigBias termBias : ℕ) (t g : ℕ → ℕ)
    (ht : Figure (inputRegime Bits.Word) (fun w => t (P1Batch.bval w)))
    (hg : Figure (inputRegime Bits.Word) (fun w => g (P1Batch.bval w))) :
    P1ChkFinal.FmtHyp (fun n => genuineDims A K V aM (t n) (g n) d bigBias termBias) := by
  let q : Bits.Word × Tally → Bits.Word := Prod.fst
  have hq : Poly q := Easy.fst.poly
  have wdata := genuineDims_figures A K V aM d bigBias termBias ht hg
  have sdata := genuineDims_figures A K V aM d bigBias termBias
    (SolFigure.Figure.pullback hq ht) (SolFigure.Figure.pullback hq hg)
  exact fmtHyp_of_figures (fun n => genuineDims A K V aM (t n) (g n) d bigBias termBias) wdata sdata

/-- The witness format for the time and guess length of Lemma P. -/
theorem fmtHyp_genuine (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine)
    (aM a b d bigBias termBias : ℕ) :
    P1ChkFinal.FmtHyp
      (fun n => genuineDims A K V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias) := by
  have ht : Figure (inputRegime Bits.Word) (fun w => P1Int.lpTime a b (P1Batch.bval w)) := by
    simpa only [P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hg : Figure (inputRegime Bits.Word) (fun w => a * (P1Batch.bval w ^ 2 + 1)) := by
    let num := fun n => Carry.Figure.natural (r := inputRegime Bits.Word) n
    simpa only [pow_two] using (num a).multiplied ((figure_bval.multiplied figure_bval).added (num 1))
  exact fmtHyp_genuine_of A K V aM d bigBias termBias _ _ ht hg

#print axioms fmtHyp_genuine

end P1SolFmt.SolFormat
