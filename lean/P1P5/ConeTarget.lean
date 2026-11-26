import P1SolCone.Wof
import P1P5.KernelWriter

/-!
# P1, the cone program: OWNER TARGET of `whyp_cone` (lane P1-lean-eval, 2026-11-25 13:50Z; G3-chief order, board 2208)

The cone prover P1-sol-cone proves `wof_def_ok` (its `Wof` equals the pushed factor `W_v` on genuine witnesses). The check
C13link (`P1ChkFinal.progC13link`) needs the hypothesis `WHyp` for ONE `Wof` term. This file fixes that term and the target:
* `coneDims`, `coneWof`: THE `Wof` term (the arguments of `wof_def_ok`), for kernel evaluators `values` and level-0 factors
  `factors`; the texts of `P1SolCone.Wof`, `KernelValues`, `ScheduleKernelsOK`, `Factor0Hyp`, `βW`, `Mbar` are FROZEN (snapshot
  research/p1/lean/P5/P1SolCone/, SHA256SUMS-1345Z.txt).
* `ConeTarget`: from the shrink kernel writers of all steps and the level-0 header reader `Factor0Hyp`, there are kernel
  evaluators `values` (right on the scheduled kernels: `ScheduleKernelsOK`) and a constant `c` with
  `WHyp b (coneWof .. values hf.choose) M K (βW Bt V a b c)` for ALL `M K`.
* `cone_c13link_task` (TEST, proved from the target): with `progC13link` it gives the C13link Task with budget
  `budget c' + βW c`; `βW` fits the branch budget by `P1P5.cone_scan_fit` and `P1P5.cone_local_fit` (ConeBudget.lean).
* `coneWof_out`: the failure branches (`v` out of range) give `0`; for indices `≥ cnt13link` C13link accepts whatever `Wof`
  says (`P1ChkFinal.C13linkw_out`).
-/

namespace P1P5.Cone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Int P1Int.P11 Module
open scoped Classical

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

/-- The witness dimensions at input length `n` (as in `wof_def_ok`). -/
def coneDims : ℕ → P1Wit.Dims := fun n =>
  P1Wit.SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1 (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias

/-- **THE `Wof` term** (the arguments of `wof_def_ok`). -/
def coneWof (values : P1SolCone.SolCone.KernelValues F) (factors : P1SolCone.Factor0In F → List (Label F)) :
    List Bool → List Bool → ℕ → F :=
  P1SolCone.Wof (coneDims Bt V a b d bigBias termBias) Bt.recordLimit Bt.growthConstant
    (P1SolCone.SolCone.Mbar Bt V a b) (2 ^ S.expanderExponent) values factors

/-- **Owner target of `P1SolCone.whyp_cone`.** -/
def ConeTarget (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) {Dd : ℕ} (bs : Basis (Fin Dd) (ZMod 2) F) : Prop :=
  (∀ i : Fin S.steps, P1P5.KW.ShrinkKernelProgram Bt.shrink (S.shrink i)) →
  ∀ hf : P1SolCone.Factor0Hyp Bt κ hκ V a b d bigBias termBias ρ P1Benes.NetBridge.bset,
    ∃ (values : P1SolCone.SolCone.KernelValues F) (c : ℕ),
      P1SolCone.SolCone.ScheduleKernelsOK Bt κ hκ values ∧
      ∀ M K : ℕ → ℕ, P1ChkFinal.WHyp bs (coneWof Bt V a b d bigBias termBias values hf.choose) M K
        (P1SolCone.βW Bt V a b c)

/-- TEST: the target composes with `progC13link` (same `Wof` term, budget `budget c' + βW c`). -/
theorem cone_c13link_task (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) {Dd : ℕ}
    (bs : Basis (Fin Dd) (ZMod 2) F)
    (hT : ConeTarget Bt κ hκ V a b d bigBias termBias ρ bs)
    (hs : ∀ i : Fin S.steps, P1P5.KW.ShrinkKernelProgram Bt.shrink (S.shrink i))
    (hf : P1SolCone.Factor0Hyp Bt κ hκ V a b d bigBias termBias ρ P1Benes.NetBridge.bset)
    (M K : ℕ → ℕ) (hb : P1ChkFinal.BatchHyp) (hl : P1ChkFinal.LenHyp)
    (hM : ∀ n, (coneDims Bt V a b d bigBias termBias n).fixedLen ≤ M n)
    (hrq : Poly (fun z : (List Bool × List Bool) × List Bool =>
      (P1ChkFinal.rqLink (coneDims Bt V a b d bigBias termBias) z, z)))
    (hdec : Poly (P1ChkFinal.decLink bs))
    (hfb : Dom (fun n : ℕ => Nat.log 2 (n + 1)) (fun n => P1ChkFinal.totC13 (coneDims Bt V a b d bigBias termBias n))) :
    ∃ (values : P1SolCone.SolCone.KernelValues F) (c c' : ℕ),
      P1SolCone.SolCone.ScheduleKernelsOK Bt κ hκ values ∧
      Code.Task (fun p : P1ChkFinal.QDom M K => P1ChkFinal.budget c' p.val + P1SolCone.βW Bt V a b c p)
        (fun p => send p.val)
        (fun p => send (decide (P1ChkFinal.C13linkw bs (coneDims Bt V a b d bigBias termBias)
          (coneWof Bt V a b d bigBias termBias values hf.choose) p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  obtain ⟨values, c, hv, hW⟩ := hT hs hf
  obtain ⟨c', hc'⟩ := P1ChkFinal.progC13link bs (coneDims Bt V a b d bigBias termBias)
    (coneWof Bt V a b d bigBias termBias values hf.choose) M K (P1SolCone.βW Bt V a b c)
    hb hl hM (hW M K) hrq hdec hfb
  exact ⟨values, c, c', hv, hc'⟩

/-- TEST: out of range, `Wof` returns `0` (and C13link accepts every index `≥ cnt13link` by `C13linkw_out`). -/
theorem coneWof_out (values : P1SolCone.SolCone.KernelValues F) (factors : P1SolCone.Factor0In F → List (Label F))
    (x u : List Bool) (v : ℕ) (hv : ¬ v < P1ChkFinal.finP (coneDims Bt V a b d bigBias termBias x.length)) :
    coneWof Bt V a b d bigBias termBias values factors x u v = 0 := by
  unfold coneWof P1SolCone.Wof
  simp only [hv, and_false, ite_false]

end

end P1P5.Cone
