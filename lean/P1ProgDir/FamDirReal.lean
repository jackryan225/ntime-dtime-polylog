import P1ProgDir.DirFitTarget

/-!
# P1ProgDir.FamDirReal: C1, C2, C3, C14 as `FamProg` at the REAL parameters (lane P1-lean-greedy)

Inputs of `famC1 .. famC14` discharged: tape numbering `Fintype.equivFin (toOAI V).K` (integ's `fixedTapeOrder`), input tape
`(toOAI V).inputTape` (integ's `c14G`), witness fit = `DirFitTarget` (Sol P1-sol-dirfit; here a hypothesis until it lands).
-/

namespace P1ProgDir.DirFit

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11

open Classical

section

universe u v

variable (hfit : DirFitTarget.{u, v}) {k : Type u} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {R : Type v}
  [CommRing R] (κ : Bt.Entry → R) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
  (hs : (2 : ℝ) ^ (-((portConsts Bt).j : ℤ)) ≤ 1) (hb : 1 ≤ b)

include hfit κ hκ hs hb

theorem famC1_real : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C1F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ := by
  obtain ⟨n₀, h⟩ := hfit Bt κ hκ V a b d bigBias termBias
  obtain ⟨Rc, cc, hR⟩ := FamDir.famC1 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias _ hs hb n₀
    (fun _ => Fintype.equivFin (toOAI V).K) (fun n hn => le_trans (h n hn).1 (h n hn).2)
  exact ⟨Rc, cc, n₀, hR⟩

theorem famC2_real : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C2F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ := by
  haveI : Nonempty (toOAI V).K := ⟨(toOAI V).inputTape⟩
  haveI : NeZero (Fintype.card (toOAI V).K) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨n₀, h⟩ := hfit Bt κ hκ V a b d bigBias termBias
  obtain ⟨Rc, cc, hR⟩ := FamDir.famC2 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias _ hs hb n₀
    (fun _ => Fintype.equivFin (toOAI V).K) (fun n hn => (h n hn).2)
  exact ⟨Rc, cc, n₀, hR⟩

theorem famC3_real : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C3F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ := by
  haveI : Nonempty (toOAI V).K := ⟨(toOAI V).inputTape⟩
  haveI : NeZero (Fintype.card (toOAI V).K) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨n₀, h⟩ := hfit Bt κ hκ V a b d bigBias termBias
  obtain ⟨Rc, cc, hR⟩ := FamDir.famC3 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias _ hs hb n₀
    (fun _ => Fintype.equivFin (toOAI V).K) (fun n hn => (h n hn).2)
  exact ⟨Rc, cc, n₀, hR⟩

theorem famC14_real : ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), P11.FamProg Ltr.bit P1Dispatch.answer Rc
    (fun x u i => decide (P1ChkDir.C14F (rD Bt V a b d bigBias termBias x.length) (Fintype.equivFin (toOAI V).K)
      (toOAI V).inputTape (fun q => ((q : ℕ) : ℤ)) u i))
    ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ := by
  obtain ⟨n₀, h⟩ := hfit Bt κ hκ V a b d bigBias termBias
  obtain ⟨Rc, cc, hR⟩ := FamDir.famC14 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias _ hs hb
    ((Fintype.equivFin (toOAI V).K) (toOAI V).inputTape : ℕ) n₀
    (fun _ => Fintype.equivFin (toOAI V).K) (toOAI V).inputTape (fun _ _ => rfl) (fun n hn => (h n hn).2)
  exact ⟨Rc, cc, n₀, hR⟩

end

end P1ProgDir.DirFit

#print axioms P1ProgDir.DirFit.famC1_real
#print axioms P1ProgDir.DirFit.famC14_real
