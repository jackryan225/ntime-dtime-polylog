import P1SolGreedy.BinaryMotif
import P1SolFmt.Genuine
import P1ChkFinal.BinBits
import P1Wrap.ParamTask

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

namespace P1SolFmt.SolFmtG

open P1Wit P1Wit.SolSpace P1Wrap
open P1SolGreedy.SolDemand
open SolFigure SolFormat SolParameters SolSchedule

open private levelDims layoutRows runPhases blockPhases from P1Wit.SpaceFacts
open private runPhases_eq_blocks from P1SolFmt.Genuine

-- These fields depend only on the fixed phase, including the final and fallback rows.
private def boundedFields (L : LevelDims) : ℕ :=
  L.slots + L.slotW + L.colW + L.tagW

private theorem layoutRow_bounds {k : Type*} [Field k] (S : BlockSchedule k)
    (C P H i : ℕ) (phases : List Phase)
    (hfinal : boundedFields (levelDims S.expanderExponent (S.degreeExponent 0) 0 0 none) ≤ C)
    (hdefault : boundedFields (levelDims S.expanderExponent 0 0 0 none) ≤ C)
    (hphase : ∀ ph ∈ phases,
      boundedFields (levelDims S.expanderExponent ph.exponent 0 0 (some ph.shrink)) ≤ C) :
    let L := ((layoutRows S P H phases)[i]?).getD (levelDims S.expanderExponent 0 0 0 none)
    boundedFields L ≤ C ∧ L.laneW ≤ H := by
  induction phases generalizing P H i with
  | nil =>
    cases i with
    | zero => exact ⟨hfinal, le_rfl⟩
    | succ i =>
      simp only [layoutRows, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
      exact ⟨hdefault, Nat.zero_le _⟩
  | cons ph phases ih =>
    cases i with
    | zero => exact ⟨hphase ph List.mem_cons_self, le_rfl⟩
    | succ i =>
      obtain ⟨hb, hl⟩ := ih (P / ph.divisor) (H - ph.laneLoss) i
        (fun q hq => hphase q (List.mem_cons_of_mem _ hq))
      exact ⟨hb, hl.trans (Nat.sub_le _ _)⟩

private theorem mem_blocks {X : Type*} {block : List X} {x : X} (n : ℕ)
    (h : x ∈ blocks block n) : x ∈ block := by
  induction n with
  | zero => exact (List.not_mem_nil h).elim
  | succ n ih =>
    rw [blocks, List.mem_append] at h
    exact h.elim id ih

private theorem genuineRow_bounds {k : Type*} [Field k] (S : BlockSchedule k) :
    ∃ C : ℕ, ∀ P H T i : ℕ,
      let L := ((layoutRows S P H (runPhases S T))[i]?).getD
        (levelDims S.expanderExponent 0 0 0 none)
      boundedFields L ≤ C ∧ L.laneW ≤ H := by
  let weight (ph : Phase) :=
    boundedFields (levelDims S.expanderExponent ph.exponent 0 0 (some ph.shrink))
  let final := boundedFields (levelDims S.expanderExponent (S.degreeExponent 0) 0 0 none)
  let fallback := boundedFields (levelDims S.expanderExponent 0 0 0 none)
  let total := ((blockPhases S).map weight).sum
  refine ⟨final + fallback + total, fun P H T i => ?_⟩
  apply layoutRow_bounds S _ P H i (runPhases S T)
  · change final ≤ final + fallback + total
    omega
  · change fallback ≤ final + fallback + total
    omega
  · intro ph hm
    rw [runPhases_eq_blocks] at hm
    have hb : weight ph ≤ total :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := weight) (mem_blocks T hm))
    change weight ph ≤ final + fallback + total
    omega

private theorem width_bound (D : Dims) (C H : ℕ)
    (h : ∀ i, boundedFields (D.lv i) ≤ C ∧ (D.lv i).laneW ≤ H) (s : ℕ) :
    D.width s ≤ 2 + D.bigW + D.wW + D.chainW + C + H := by
  cases he : D.kind s <;> simp only [Dims.width, he]
  case lev i m =>
    have ⟨hc, hh⟩ := h i
    unfold boundedFields at hc
    cases m <;> simp only [Dims.levWidth] <;> omega
  all_goals omega

private theorem figure_bin {X : Type} [Codec X] {f : X → ℕ}
    (h : Figure (inputRegime X) f) :
    Poly (fun x => P1ChkFinal.bin (f x)) := by
  simpa only [P1ChkFinal.bin_eq_bits] using figure_poly h

private theorem range_map_poly {X Y : Type} [Codec X] [Codec Y]
    (x₀ : X) {n : X → ℕ} {f : X → ℕ → Y}
    (hn : Realizes (inputRegime X) n)
    (hf : Poly (fun p : X × Tally => f p.1 p.2.length)) :
    Poly (fun x => (List.range (n x)).map (f x)) := by
  have h := (Poly.identity.pair ((show Poly (fun x => tally (n x)) from hn).compose
    Iter.poly_line)).compose (Poly.push x₀ ([] : Tally) hf)
  convert h using 1
  funext x
  change (List.range (n x)).map (f x) =
    Code.polyPush (fun p : X × Tally => f p.1 p.2.length) (x, Iter.lineup (tally (n x)))
  simp only [Code.polyPush, Iter.lined]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro j hj hk
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, tally_length]

private theorem offsets_figures {X : Type} [Codec X] (x₀ : X)
    {D : X → Dims} {s : X → ℕ} (hs : Realizes (inputRegime X) s)
    (h : Figure (inputRegime (X × Tally))
      (fun p => (D p.1).count p.2.length * (D p.1).width p.2.length)) :
    Figure (inputRegime X) (fun x => (D x).off (s x)) := by
  obtain ⟨word, hw, hv⟩ := h
  have hi := Poly.identity.pair ((show Poly (fun x => tally (s x)) from hs).compose Iter.poly_line)
  have hw' : Poly word := hw
  have hl := hi.compose (Poly.push x₀ ([] : Tally) hw')
  refine ⟨_, hl.compose sumWords_poly, fun x => ?_⟩
  change Bits.value (sumWords (Code.polyPush word (x, Iter.lineup (tally (s x))))) = _
  rw [value_bval, bval_sumWords, Iter.lined]
  simp only [Code.polyPush, List.map_ofFn, Function.comp_def, ← value_bval, hv, tally_length]
  exact offAt_ofFn _ _ _

private theorem shrink_poly {X : Type} [Codec X] {f : X → Bool}
    (hf : Figure (inputRegime X) (fun x => (f x).toNat)) : Poly f := by
  obtain ⟨flag, hflag, hv⟩ := classified_eq hf (Carry.Figure.natural 1)
  have eq : flag = f := by
    funext x
    have h : (f x).toNat = 1 ↔ f x = true := by cases f x <;> decide
    exact Bool.eq_iff_iff.mpr ((hv x).symm.trans h)
  exact eq ▸ hflag

private theorem m_figure (Kc : Consts) (a b : ℕ) :
    Figure (inputRegime Bits.Word) (fun w => Params.m Kc (P1Int.lpTime a b (P1Batch.bval w))) := by
  refine ⟨P1Wrap.W3.PT.mW Kc.j a b, P1Wrap.W3.PT.poly_mW Kc.j a b, fun w => ?_⟩
  rw [P1Wrap.W3.PT.value_mW, value_bval, P1Int.lpM2, P1Wrap.W3.lpT2_sOf]
  rfl

private theorem sections_poly {D : Bits.Word → Dims}
    (hsec : Poly (fun p : Bits.Word × Tally =>
      ((P1ChkFinal.bin ((D p.1).off p.2.length), P1ChkFinal.bin ((D p.1).width p.2.length)),
        tally ((D p.1).width p.2.length)))) :
    Poly (fun p : Bits.Word × Tally => (List.range 12).map fun j =>
      let s := secLev p.2.length (Mem.ofCode j)
      ((P1ChkFinal.bin ((D p.1).off s), P1ChkFinal.bin ((D p.1).width s)),
        tally ((D p.1).width s))) := by
  let X := Bits.Word × Tally
  let R := inputRegime (X × Tally)
  let fix := fun n => Staff.Realizes.fix (r := R) n
  have hi : Realizes R (fun p : X × Tally => p.1.2.length) :=
    realizes_of_tally (Easy.fst.poly.compose Easy.snd.poly)
  have hj : Realizes R (fun p : X × Tally => p.2.length) :=
    realizes_of_tally Easy.snd.poly
  have hs := ((fix 5).plus ((fix 12).times hi)).plus hj
  have hinput : Poly (fun p : X × Tally => (p.1.1, tally (5 + 12 * p.1.2.length + p.2.length))) :=
    (Easy.fst.poly.compose Easy.fst.poly).pair hs
  let sectionAt (p : X) (j : ℕ) :=
    let s := 5 + 12 * p.2.length + j
    ((P1ChkFinal.bin ((D p.1).off s), P1ChkFinal.bin ((D p.1).width s)),
      tally ((D p.1).width s))
  have hsection : Poly (fun q : X × Tally => sectionAt q.1 q.2.length) := by
    simpa only [sectionAt, tally_length] using hinput.compose hsec
  have h := range_map_poly (([], []) : X) (f := sectionAt) (Staff.Realizes.fix 12) hsection
  convert h using 1
  funext p
  apply List.map_congr_left
  intro j hj
  rw [secLev, Mem.toNat_ofNat j (List.mem_range.mp hj)]

private theorem fmt_of_genuine_figures {k : Type*} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (Kc : Consts) (V : FiniteMultiTapeMachine)
    (aM d bigBias termBias : ℕ) (t g M : ℕ → ℕ)
    (ht : Figure (inputRegime Bits.Word) (fun w => t (P1Batch.bval w)))
    (hg : Figure (inputRegime Bits.Word) (fun w => g (P1Batch.bval w)))
    (hM : Figure (inputRegime Bits.Word) (fun w => M (P1Batch.bval w))) :
    FmtHypGreedy
      (fun n => genuineDims A Kc V aM (t n) (g n) d bigBias termBias) M := by
  let X := Bits.Word × Tally
  let R := inputRegime X
  let fix := fun n => Staff.Realizes.fix (r := R) n
  let num := fun n => Carry.Figure.natural (r := R) n
  let D : Bits.Word → Dims :=
    fun w => genuineDims A Kc V aM (t (P1Batch.bval w)) (g (P1Batch.bval w)) d bigBias termBias
  have wd : DimsFigures (inputRegime Bits.Word) D :=
    genuineDims_figures A Kc V aM d bigBias termBias ht hg
  have htX := SolFigure.Figure.pullback (show Poly (Prod.fst : X → Bits.Word) from Easy.fst.poly) ht
  have sd : DimsFigures R (fun p : X => D p.1) :=
    genuineDims_figures A Kc V aM d bigBias termBias htX
      (SolFigure.Figure.pullback Easy.fst.poly hg)
  have hi : Realizes R (fun p : X => p.2.length) := realizes_of_tally Easy.snd.poly
  obtain ⟨cap, hcap⟩ := genuineRow_bounds S
  have hrow (w : Bits.Word) (i : ℕ) :
      boundedFields ((D w).lv i) ≤ cap ∧ ((D w).lv i).laneW ≤ Params.h (t (P1Batch.bval w)) :=
    hcap _ _ _ i
  have hlevel := sd.level hi
  have hslots : Realizes R (fun p : X => ((D p.1).lv p.2.length).slots) := by
    apply hlevel.slots.pay ((Dom.const _ cap).mono _)
    intro p
    have h := (hrow p.1 p.2.length).1
    unfold boundedFields at h
    omega
  have hbig : Realizes R (fun p : X => (D p.1).bigW) :=
    (fix bigBias).plus ((fix 6).times (realizes_lam htX))
  have htuple := figure_tuple_width (Fintype.card (P1Net.Ext V.K))
    (Fintype.card V.Γ) (Fintype.card V.Q) (Fintype.card V.K) htX
  have hgrowth := (num A.growthConstant).repeated (realizes_T Kc htX)
  have hsmall : Realizes R (fun p : X => (D p.1).wW) :=
    (fix termBias).plus (((hgrowth.multiplied (htuple.added (num 1))).added (num 1)).short_log)
  have hwidth := sd.width hi
  have hwidthSmall : Realizes R (fun p : X => (D p.1).width p.2.length) := by
    have hbound := (((((fix 2).plus hbig).plus hsmall).plus (fix (Nat.clog 2 d))).plus
      (fix cap)).plus (realizes_h htX)
    exact hwidth.pay ((diameter _ hbound).mono
      (fun p => width_bound (D p.1) cap _ (hrow p.1) p.2.length))
  have hprev : Poly (fun q : X × Tally => (q.1.1, q.2)) :=
    (Easy.fst.poly.compose Easy.fst.poly).pair Easy.snd.poly
  have hext := SolFigure.Figure.pullback hprev ((sd.count hi).multiplied hwidth)
  have hoff := offsets_figures (([], []) : X) (D := fun p => D p.1) hi hext
  have hsec := ((figure_bin hoff).pair (figure_bin hwidth)).pair
    (show Poly (fun p : X => tally ((D p.1).width p.2.length)) from hwidthSmall)
  have hsections := sections_poly hsec
  have hcolCount : Realizes R (fun p : X => 2 * ((D p.1).lv p.2.length).slots + 1) :=
    ((fix 2).times hslots).plus (fix 1)
  have hrowPoly : Poly (fun p : X => levelRow (D p.1) p.2.length) := by
    unfold levelRow
    exact (shrink_poly hlevel.shrink).pair ((figure_bin hlevel.bases).pair
      ((figure_bin hlevel.slots).pair ((show Code.Poly _ from hslots).pair
        ((show Code.Poly _ from hcolCount).pair hsections))))
  have hlevels := range_map_poly ([] : Bits.Word)
    (f := fun w i => (P1ChkFinal.bin i, levelRow (D w) i))
    (wd.top.plus (Staff.Realizes.fix 1)) ((figure_bin (Carry.Figure.of_spoken hi)).pair hrowPoly)
  have hradix : Figure (inputRegime Bits.Word) (fun w => 2 ^ P1ChkGreedy.levBits (D w)) :=
    (Carry.Figure.natural 2).repeated
      (((Carry.Figure.of_spoken wd.top).added (Carry.Figure.natural 1)).short_log)
  exact (figure_bin hradix).pair ((figure_bin hM).pair hlevels)

end P1SolFmt.SolFmtG

open P1SolFmt.SolFigure P1SolFmt.SolFormat P1SolFmt.SolParameters

theorem P1SolFmt.fmtHypGreedy_genuine {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) :
    P1SolGreedy.SolDemand.FmtHypGreedy
      (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (fun n => P1Wrap.Params.m Kc (P1Int.lpTime a b n)) := by
  have ht : Figure (inputRegime Bits.Word) (fun w => P1Int.lpTime a b (P1Batch.bval w)) := by
    simpa only [P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hg : Figure (inputRegime Bits.Word) (fun w => a * (P1Batch.bval w ^ 2 + 1)) := by
    let num := fun n => Carry.Figure.natural (r := inputRegime Bits.Word) n
    simpa only [pow_two] using (num a).multiplied ((figure_bval.multiplied figure_bval).added (num 1))
  exact P1SolFmt.SolFmtG.fmt_of_genuine_figures A Kc V aM d bigBias termBias _ _ _ ht hg
    (P1SolFmt.SolFmtG.m_figure Kc a b)

#print axioms P1SolFmt.fmtHypGreedy_genuine
