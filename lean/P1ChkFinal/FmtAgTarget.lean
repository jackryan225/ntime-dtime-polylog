import P1SolGreedy.C6Format
import P1SolGreedy.MotifFormat
import P1Wit.SpaceFacts
import P1Int.LemmaP

/-!
# P1ChkFinal.FmtAgTarget: the targets of Sol P1-sol-fmtag (format facts of C6, C7, C8 at the genuine dims)

Lane P1-lean-greedy (2026-11-25). `ag` is integ's `P1Int.P11.genuineAg dims` (Interfaces/P1Int/FormAg.lean, p1intB-87),
written out here so that the prover needs no import of the integration layer:
`genuineAg dims n ℓ = ((dims n).lv ℓ).slotW, ((dims n).lv ℓ).laneW - packingLaneBits ((dims n).lv ℓ).slotW 0)` (rfl).
-/

namespace P1ChkFinal.FmtAgTarget

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- The genuine level parameters of a dims function (= `P1Int.P11.genuineAg`, by `rfl`). -/
def agG (dims : ℕ → P1Wit.Dims) : ℕ → ℕ → ℕ × ℕ :=
  fun n ℓ => (((dims n).lv ℓ).slotW, ((dims n).lv ℓ).laneW - packingLaneBits ((dims n).lv ℓ).slotW 0)

/-- Target 1 (C6). -/
def TagsTarget.{u} : Prop :=
  ∀ {k : Type u} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ),
    P1SolGreedy.SolDemand.FmtHypTags
      (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (fun n => P1Wrap.Params.m Kc (P1Int.lpTime a b n))
      (fun n ℓ =>
        (((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).slotW,
          ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).laneW -
            packingLaneBits
              ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
                termBias).lv ℓ).slotW 0))

/-- Target 2 (C7 with `all = false`, C8 with `all = true`). -/
def MotifTarget.{u} : Prop :=
  ∀ (all : Bool) {k : Type u} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ),
    P1SolGreedy.SolDemand.FmtHypMotif all
      (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (fun n => P1Wrap.Params.m Kc (P1Int.lpTime a b n))
      (fun n ℓ =>
        (((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).slotW,
          ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).laneW -
            packingLaneBits
              ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
                termBias).lv ℓ).slotW 0))

/-- The inline `ag` of the targets is `agG` of the genuine dims function (so `genuineAg` too, by `rfl`). -/
example {k : Type} [Field k] {S : BlockSchedule k} (A : S.Templates)
    (Kc : P1Wrap.Consts) (V : FiniteMultiTapeMachine) (aM a b d bigBias termBias : ℕ) :
    agG (fun n => P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias) =
      (fun n ℓ =>
        (((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).slotW,
          ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias).lv ℓ).laneW -
            packingLaneBits
              ((P1Wit.SolSpace.genuineDims A Kc V aM (P1Int.lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
                termBias).lv ℓ).slotW 0)) := rfl

/-! Small case of the shape of `agG`: a level with `slotW = 0`, `laneW = packingLaneBits 0 5` gives `(0, 5)`. -/
example (D : P1Wit.Dims) (ℓ : ℕ) (ha : (D.lv ℓ).slotW = 0) (hg : (D.lv ℓ).laneW = packingLaneBits 0 5) :
    agG (fun _ => D) 7 ℓ = (0, 5) := by
  simp only [agG]
  rw [ha, hg]
  unfold packingLaneBits
  simp only [pow_zero, Nat.mul_one]
  congr 1
  all_goals omega

end P1ChkFinal.FmtAgTarget
