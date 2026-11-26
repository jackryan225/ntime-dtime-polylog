import P1SolCone.TraceBudget

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW P1SolFmt.SolFigure
open scoped P1ChkFinal.AstraC10
open private slotCap from P1Wit.SpaceFacts

theorem dom_sizePair {X A B : Type*} [Codec A] [Codec B] {σ : X → ℕ} {a : X → A} {b : X → B}
    (ha : Dom σ (fun x => size (a x))) (hb : Dom σ (fun x => size (b x))) :
    Dom σ (fun x => size (a x,b x)) :=
  ((ha.add hb).add (Dom.const _ 1)).mono (fun x => by rw [size_prod])

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

local notation "Wn" q => bin (List.length (Prod.fst q))
local notation "Dq" q => coneDims B V a b d bigBias termBias (P1Batch.bval (Wn q))
local notation "Cq" q => coneReadClock B V a b bigBias termBias (Wn q)
local notation "Mq" q => Mbar B V a b (P1Batch.bval (Wn q))
local notation "σ" => coneScale B V a b

theorem queryBin_dom : Dom σ (fun q : Qry => size (Wn q)) :=
  (smallQuery_dom B V a b).mono (fun q => by change size (smallQuery q).1 ≤ _; rw [size_prod]; omega)

theorem queryTop_dom : Dom σ (fun q : Qry => (Dq q).top) := by
  have h := ((coneSchedule_poly B V a b d bigBias termBias).length.map (fun q : Qry => Wn q)).sub
    (queryBin_dom B V a b)
  refine h.mono (fun q => ?_)
  rw [← show (coneSchedule B V a b d bigBias termBias (Wn q)).length = (Dq q).top by
    rw [coneSchedule_eq B V a b d bigBias termBias]
    simp only [List.length_reverse,List.length_map,List.length_range]]
  exact (duration _).le

theorem queryWidth_dom : Dom σ (fun q : Qry => (Mq q)) :=
  ((diameter _ (coneMbarRealizes B V a b (Code.Poly.identity (X := Bits.Word)))).map
    (fun q : Qry => Wn q)).sub (queryBin_dom B V a b)

theorem queryTraceBits_dom :
    Dom σ (queryTraceBits B V a b d bigBias termBias) := by
  have clock : Dom σ (fun q : Qry => (Cq q).length) :=
    (((coneReadClock_poly B V a b bigBias termBias).length.map (fun q : Qry => Wn q)).sub
      (queryBin_dom B V a b)).mono (fun _ => (duration _).le)
  have big : Dom σ (fun q : Qry => (Dq q).bigW) := by
    have h := ((diameter _ (coneFieldWidth_realizes B V a b bigBias termBias
      (Code.Poly.identity (X := Bits.Word)))).map (fun q : Qry => Wn q)).sub (queryBin_dom B V a b)
    apply h.mono
    intro q
    exact Nat.le_add_left _ _ |>.trans (Nat.le_add_right _ _) |>.trans
      (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _)
  have challenge : Dom σ (fun q : Qry => q.2.2.length) := (Dom.base σ).mono (fun q => by
    have h₁ : q.2.2.length ≤ coneQuerySize q := by unfold coneQuerySize; omega
    exact h₁.trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans (Nat.le_add_right _ _)))
  exact ((big.add challenge).add (((queryTop_dom B V a b d bigBias termBias).add (Dom.const _ 1)).mul clock)).add
    (Dom.const _ 1)

theorem queryHalfCount_dom : Dom σ (fun q : Qry => halfCount (slotCap S) (Mq q)) := by
  refine ((Dom.base σ).pow (2 * slotCap S)).mono (fun q => ?_)
  rw [halfCount, Nat.mul_comm (2 * slotCap S), pow_mul]
  apply Nat.pow_le_pow_left
  have h : (Mq q) ≤ B.growthConstant * (Mq q) := Nat.le_mul_of_pos_left _
    ((by decide : 0 < 2).trans_le (le_max_left _ _))
  have hb := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h
  rw [bval_bin] at hb ⊢
  unfold coneScale pureConeScale
  exact hb.trans ((Nat.le_mul_of_pos_right _ (coneQuerySize_pos q)).trans (Nat.le_add_right _ _))

theorem queryKeyCount_dom : Dom σ (fun q : Qry => keyCountBound (slotCap S) (Mq q)) :=
  (queryWidth_dom B V a b).mul (queryHalfCount_dom B V a b)

theorem queryLevelCode_dom (r : ℕ) :
    Dom σ (fun q : Qry => levelCodeBound (slotCap S) (Mq q) B.recordLimit r) := by
  let c := Dom.const σ
  have n := queryKeyCount_dom B V a b
  have h := queryHalfCount_dom B V a b
  have entry := (c (2*r+2)).add (((c B.recordLimit).mul (((c 2).mul n).add (c 2))).add (c 1))
  exact (n.mul (((h.pow B.recordLimit).mul (entry.add (c 1))).add (c 2))).add (c 1)

variable {F : Type} [CommRing F] [Fintype F]

theorem queryTrace_dom {X : Type*} (q : X → Qry) (ls : X → List ℕ)
    (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (hls : ∀ x l, l ∈ ls x → l < (Dq (q x)).top) (hn : ∀ x, (ls x).length ≤ (Dq (q x)).top) :
    Dom (σ ∘ q) (fun x => size (encodeConeState (queryTrace B V a b d bigBias termBias shr ref (q x) (ls x)))) := by
  let c := Dom.const σ
  have k := queryKeyCount_dom B V a b
  have bits := queryTraceBits_dom B V a b d bigBias termBias
  have width := queryWidth_dom B V a b
  have s := (((c 4).mul bits).add ((c (2*slotCap S)).mul (((c 2).mul width).add (c 2)))).add (c 8)
  have top := queryTop_dom B V a b d bigBias termBias
  have levels := queryLevelCode_dom B V a b (Fintype.card F)
  have h := ((k.mul s).add (top.mul (levels.add (c 1)))).add (c 5)
  exact (h.map q).mono (fun x => queryTrace_size B V a b d bigBias termBias shr ref (q x) (ls x) (hls x) (hn x))

end

end P1SolCone.SolCone
