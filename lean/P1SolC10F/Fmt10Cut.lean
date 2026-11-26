import P1C10.Fmt10Defs
import P1SolFmt.Genuine

namespace P1SolC10F.Sol

open P1C10 P1Wit
open P1Wit.SolSpace
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open private levelDims layoutRows layoutRows_length from P1Wit.SpaceFacts

theorem fmt10_beyond (D : Dims) (L : LevelDims) {i : ℕ} (hi : D.top + 2 ≤ i)
    (hrow : ∀ j, D.top + 2 ≤ j → D.lv j = L) :
    fmt10 D i =
      ([D.top, P1ChkGreedy.levBits D, D.fixedLen, L.bases, L.slots, L.lanes, L.laneW,
        if L.shrink then 1 else 0, L.termKeys, L.termArity, L.bases, L.slots, L.lanes, L.laneW] ++
        (memAll.flatMap fun _ => [D.fixedLen, 0]) ++
        (memAll.flatMap fun _ => [D.fixedLen, 0])).map Nat.bits := by
  have hi' : D.top + 2 ≤ i + 1 := by omega
  simp only [fmt10, hrow i hi, hrow (i + 1) hi', off_secLev_beyond D hi,
    width_secLev_beyond D hi, off_secLev_beyond D hi', width_secLev_beyond D hi']

theorem fmt10_zero_beyond {i : ℕ} (hi : 2 ≤ i) :
    fmt10 zeroDims i = List.replicate 62 [] := by
  rw [fmt10_beyond zeroDims zeroLevel hi (fun _ _ => rfl)]
  decide

theorem fmt10_empty_cut (G : ℕ → Dims) {n₀ n : ℕ} (hn : n < n₀) (i : ℕ) :
    fmt10 (cutDims n₀ G n) i =
      if i = 0 then List.replicate 15 [] ++ [[true]] ++ List.replicate 46 []
      else List.replicate 62 [] := by
  rw [cutDims_of_lt G hn]
  rcases i with _ | (_ | i)
  · decide
  · decide
  · rw [ite_eq_right (by omega), fmt10_zero_beyond (by omega)]

theorem genuine_row_beyond {k : Type*} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (K : P1Wrap.Consts) (V : FiniteMultiTapeMachine)
    (aM t g d bigBias termBias i : ℕ)
    (hi : (genuineDims A K V aM t g d bigBias termBias).top + 2 ≤ i) :
    (genuineDims A K V aM t g d bigBias termBias).lv i =
      levelDims S.expanderExponent 0 0 0 none := by
  unfold genuineDims at hi ⊢
  dsimp only at hi ⊢
  rw [List.getElem?_eq_none (by rw [layoutRows_length]; omega)]
  rfl


open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open P1SolFmt.SolFigure P1SolFmt.SolFormat P1SolFmt.SolGeometry
open P1SolFmt.SolParameters
open private sumWords sumWords_poly value_sumWords from P1SolFmt.Offsets

private theorem offsets_figures {X : Type} [Codec X] (x₀ : X)
    {D : X → Dims} {s : X → ℕ} (hs : Realizes (inputRegime X) s)
    (h : Figure (inputRegime (X × Tally))
      (fun p => (D p.1).count p.2.length * (D p.1).width p.2.length)) :
    Figure (inputRegime X) (fun x => (D x).off (s x)) := by
  obtain ⟨word, hw, hv⟩ := h
  have hindex := Poly.identity.pair ((show Poly (fun x => tally (s x)) from hs).compose Iter.poly_line)
  have hwords := hindex.compose (Poly.push x₀ ([] : Tally) (show Poly word from hw))
  refine ⟨_, hwords.compose sumWords_poly, fun x => ?_⟩
  change Bits.value (sumWords (polyPush word (x, Iter.lineup (tally (s x))))) = (D x).off (s x)
  rw [value_sumWords, Iter.lined]
  simp only [polyPush, List.map_ofFn, Function.comp_def, hv, tally_length]
  exact offAt_ofFn _ _ _

private theorem poly_cons {X : Type} [Codec X] {f : X → Bits.Word}
    {g : X → List Bits.Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) :=
  (hf.pair hg).compose Poly.cons

private theorem poly_ite {X Y : Type} [Codec X] [Codec Y]
    {p : X → Prop} [DecidablePred p] {f g : X → Y}
    (hp : Classified (inputRegime X) p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  obtain ⟨flag, hflag, he⟩ := hp
  have choice := (show Poly flag from hflag).choose hf hg
  convert choice using 1
  funext x
  cases h : flag x with
  | false =>
    have hn : ¬ p x := fun hx => Bool.false_ne_true (h.symm.trans ((he x).mp hx))
    rw [ite_eq_right hn]
    rfl
  | true =>
    rw [ite_eq_left ((he x).mpr h)]
    rfl

private theorem level_sections_poly {X : Type} [Codec X] {D : X → Dims}
    {i : X → ℕ} (hi : Realizes (inputRegime X) i)
    (data : DimsFigures (inputRegime X) D)
    (sectionData : DimsFigures (inputRegime (X × Tally)) (fun p => D p.1))
    (defaultInput : X) (ms : List Mem) :
    Poly (fun x =>
      (ms.flatMap fun m => [(D x).off (secLev (i x) m), (D x).width (secLev (i x) m)]).map Nat.bits) := by
  have hj : Realizes (inputRegime (X × Tally)) (fun p : X × Tally => p.2.length) :=
    realizes_of_tally Easy.snd.poly
  have extent := (sectionData.count hj).multiplied (sectionData.width hj)
  induction ms with
  | nil => exact Code.Poly.const []
  | cons m ms ih =>
    let num := fun n => Staff.Realizes.fix (r := inputRegime X) n
    have hs : Realizes (inputRegime X) (fun x => secLev (i x) m) :=
      ((num 5).plus ((num 12).times hi)).plus (num m.toNat)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]
    exact poly_cons (figure_poly (offsets_figures defaultInput hs extent))
      (poly_cons (figure_poly (data.width hs)) ih)

private theorem fmt10_poly_of_figures {X : Type} [Codec X] {D : X → Dims}
    {i : X → ℕ} (hi : Realizes (inputRegime X) i)
    (data : DimsFigures (inputRegime X) D)
    (sectionData : DimsFigures (inputRegime (X × Tally)) (fun p => D p.1))
    (defaultInput : X) :
    Poly (fun x => fmt10 (D x) (i x)) := by
  let num := fun n => Staff.Realizes.fix (r := inputRegime X) n
  have hNext := hi.plus (num 1)
  have hTop := data.top
  have hBits : Figure (inputRegime X) (fun x => P1ChkGreedy.levBits (D x)) :=
    Figure.of_spoken (Figure.of_spoken (hTop.plus (num 1))).short_log
  have hEnd : Realizes (inputRegime X) (fun x => (D x).nSec) :=
    (num 7).plus ((num 12).times (hTop.plus (num 1)))
  have hj : Realizes (inputRegime (X × Tally)) (fun p : X × Tally => p.2.length) :=
    realizes_of_tally Easy.snd.poly
  have hLen : Figure (inputRegime X) (fun x => (D x).fixedLen) :=
    offsets_figures defaultInput hEnd ((sectionData.count hj).multiplied (sectionData.width hj))
  have L := data.level hi
  have N := data.level hNext
  have hShrink : Figure (inputRegime X) (fun x => if ((D x).lv (i x)).shrink then 1 else 0) := by
    convert L.shrink using 1
    funext x
    cases ((D x).lv (i x)).shrink <;> rfl
  have header : Poly (fun x =>
    [(D x).top, P1ChkGreedy.levBits (D x), (D x).fixedLen,
      ((D x).lv (i x)).bases, ((D x).lv (i x)).slots, ((D x).lv (i x)).lanes,
      ((D x).lv (i x)).laneW, if ((D x).lv (i x)).shrink then 1 else 0,
      ((D x).lv (i x)).termKeys, ((D x).lv (i x)).termArity,
      ((D x).lv (i x + 1)).bases, ((D x).lv (i x + 1)).slots, ((D x).lv (i x + 1)).lanes,
      ((D x).lv (i x + 1)).laneW].map Nat.bits) := by
    simp only [List.map_cons, List.map_nil]
    exact poly_cons (figure_poly (Figure.of_spoken hTop)) <|
      poly_cons (figure_poly hBits) <| poly_cons (figure_poly hLen) <|
      poly_cons (figure_poly L.bases) <| poly_cons (figure_poly L.slots) <|
      poly_cons (figure_poly L.lanes) <| poly_cons (figure_poly L.laneW) <|
      poly_cons (figure_poly hShrink) <| poly_cons (figure_poly L.termKeys) <|
      poly_cons (figure_poly L.termArity) <| poly_cons (figure_poly N.bases) <|
      poly_cons (figure_poly N.slots) <| poly_cons (figure_poly N.lanes) <|
      poly_cons (figure_poly N.laneW) (Code.Poly.const [])
  simp only [fmt10, List.map_append]
  exact (header.app (level_sections_poly hi data sectionData defaultInput memAll)).app
    (level_sections_poly hNext data sectionData defaultInput memAll)

private theorem fmt10_genuine_poly {k : Type} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (K : P1Wrap.Consts) (V : FiniteMultiTapeMachine)
    (aM d bigBias termBias : ℕ) (t g : ℕ → ℕ)
    (ht : Figure (inputRegime Bits.Word) (fun w => t (P1Batch.bval w)))
    (hg : Figure (inputRegime Bits.Word) (fun w => g (P1Batch.bval w))) :
    FmtHyp10 (fun n => genuineDims A K V aM (t n) (g n) d bigBias termBias) := by
  let X := Bits.Word × Bits.Word
  let D (x : X) := genuineDims A K V aM (t (P1Batch.bval x.1)) (g (P1Batch.bval x.1)) d bigBias termBias
  have htX := P1SolFmt.SolFigure.Figure.pullback (show Poly (Prod.fst : X → Bits.Word) from Easy.fst.poly) ht
  have hgX := P1SolFmt.SolFigure.Figure.pullback (show Poly (Prod.fst : X → Bits.Word) from Easy.fst.poly) hg
  have data : DimsFigures (inputRegime X) D :=
    genuineDims_figures A K V aM d bigBias termBias htX hgX
  have sdata : DimsFigures (inputRegime (X × Tally)) (fun p => D p.1) :=
    genuineDims_figures A K V aM d bigBias termBias
      (P1SolFmt.SolFigure.Figure.pullback Easy.fst.poly htX) (P1SolFmt.SolFigure.Figure.pullback Easy.fst.poly hgX)
  have raw := P1SolFmt.SolFigure.Figure.pullback (show Poly (Prod.snd : X → Bits.Word) from Easy.snd.poly) figure_bval
  have cap : Realizes (inputRegime X) (fun x => (D x).top + 2) :=
    data.top.plus (Staff.Realizes.fix 2)
  have capFig := Figure.of_spoken cap
  have idxFig : Figure (inputRegime X) (fun x => min (P1Batch.bval x.2) ((D x).top + 2)) := by
    convert raw.variant capFig (raw.compare_ capFig) using 1
    funext x
    by_cases hx : P1Batch.bval x.2 < (D x).top + 2
    · rw [ite_eq_left hx, min_eq_left hx.le]
    · rw [ite_eq_right hx, min_eq_right (Nat.le_of_not_gt hx)]
  -- Cap the binary index before requesting its unary representation.
  have idx := idxFig.pay ((diameter _ cap).mono (fun _ => min_le_right _ _))
  have h := fmt10_poly_of_figures idx data sdata (([], []) : X)
  change Poly (fun x : X => fmt10 (D x) (P1Batch.bval x.2))
  convert h using 1
  funext x
  by_cases hx : P1Batch.bval x.2 ≤ (D x).top + 2
  · rw [min_eq_left hx]
  · have hb : (D x).top + 2 ≤ P1Batch.bval x.2 := by omega
    rw [min_eq_right hb]
    have hrow (j : ℕ) (hj : (D x).top + 2 ≤ j) :
        (D x).lv j = levelDims S.expanderExponent 0 0 0 none :=
      genuine_row_beyond A K V aM _ _ d bigBias termBias j hj
    rw [fmt10_beyond (D x) _ hb hrow, fmt10_beyond (D x) _ (le_refl _) hrow]

private theorem fmt10_zero_poly :
    Poly (fun x : Bits.Word × Bits.Word => fmt10 zeroDims (P1Batch.bval x.2)) := by
  have hi : Figure (inputRegime (Bits.Word × Bits.Word)) (fun x => P1Batch.bval x.2) :=
    P1SolFmt.SolFigure.Figure.pullback Easy.snd.poly figure_bval
  let first : List Bits.Word := List.replicate 15 [] ++ [[true]] ++ List.replicate 46 []
  let rest : List Bits.Word := List.replicate 62 []
  have program : Poly (fun x : Bits.Word × Bits.Word =>
      if P1Batch.bval x.2 = 0 then first else rest) :=
    poly_ite (classified_eq hi (Figure.natural 0)) (Code.Poly.const first) (Code.Poly.const rest)
  have he (x : Bits.Word × Bits.Word) :
      fmt10 zeroDims (P1Batch.bval x.2) = if P1Batch.bval x.2 = 0 then first else rest := by
    have h := fmt10_empty_cut (fun _ => zeroDims) (n := 0) (n₀ := 1) (by decide) (P1Batch.bval x.2)
    rwa [cutDims_of_lt _ (by decide : 0 < 1)] at h
  exact (funext he).symm ▸ program

private theorem fmt10_cut_of_poly (G : ℕ → Dims) (n₀ : ℕ) (hG : FmtHyp10 G) :
    FmtHyp10 (cutDims n₀ G) := by
  let X := Bits.Word × Bits.Word
  have hn : Figure (inputRegime X) (fun x => P1Batch.bval x.1) :=
    P1SolFmt.SolFigure.Figure.pullback Easy.fst.poly figure_bval
  have program : Poly (fun x : X => if P1Batch.bval x.1 < n₀ then fmt10 zeroDims (P1Batch.bval x.2)
      else fmt10 (G (P1Batch.bval x.1)) (P1Batch.bval x.2)) :=
    poly_ite (hn.compare_ (Figure.natural n₀)) fmt10_zero_poly hG
  have he (x : X) : fmt10 (cutDims n₀ G (P1Batch.bval x.1)) (P1Batch.bval x.2) =
      if P1Batch.bval x.1 < n₀ then fmt10 zeroDims (P1Batch.bval x.2)
      else fmt10 (G (P1Batch.bval x.1)) (P1Batch.bval x.2) := by
    by_cases hx : P1Batch.bval x.1 < n₀
    · rw [ite_eq_left hx, cutDims_of_lt G hx]
    · rw [ite_eq_right hx, cutDims_of_le G (Nat.le_of_not_gt hx)]
  change Code.Poly (fun x : X => fmt10 (cutDims n₀ G (P1Batch.bval x.1)) (P1Batch.bval x.2))
  exact (funext he).symm ▸ program

theorem fmt10_cut_proof : Fmt10CutTarget := by
  intro k _ S A K V aM a b d bigBias termBias n₀
  have ht : Figure (inputRegime Bits.Word) (fun w => P1Int.lpTime a b (P1Batch.bval w)) := by
    simpa only [P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hg : Figure (inputRegime Bits.Word) (fun w => a * (P1Batch.bval w ^ 2 + 1)) := by
    let num := fun n => Figure.natural (r := inputRegime Bits.Word) n
    simpa only [pow_two] using (num a).multiplied ((figure_bval.multiplied figure_bval).added (num 1))
  exact fmt10_cut_of_poly (genD A K V aM a b d bigBias termBias) n₀
    (fmt10_genuine_poly A K V aM d bigBias termBias (P1Int.lpTime a b) (fun n => a * (n ^ 2 + 1)) ht hg)

end P1SolC10F.Sol

theorem P1SolC10F.fmt10Cut : P1C10.Fmt10CutTarget :=
  P1SolC10F.Sol.fmt10_cut_proof

#print axioms P1SolC10F.fmt10Cut
