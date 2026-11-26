import P1Int.FinalInputs
import P1Int.DispCk
import P1Int.DispCnt
import P1Int.DispOut
import P1Int.DispBeta
import P1ProgDir.FamConv
import P1ChkFinal.C13linkFmtTarget
import P1Dispatch.Spec
import P1SolFinal.C13lFmt

/-!
# P1Int.DispFam: the 16 family programs and integ's input `DispIn` (lane P1-lean-disp, item p11_dispatch)

`dispFam`: for every family `c' < 16` a stack program with `FamProg` for the decider `dispCk c'` at the real parameters
(`s = 2^-j`, `Ltr.bit`, `P1Dispatch.answer`), from the lanes' PROVED family theorems:
0-2, 14 `famC1/2/3/14_closed`; 3 `FamDir.famC4`; 4, 8 `famC5/9_genuine`; 5, 7 `famC6/8_genuine`; 6 `famC7all_genuine`
(D15); 9 `P1C10.famC10_closed` (cut dims = `gdims` for `|x| ≥ n₀`: `famProg_congr`); 10, 11, 13 `FamFinal.famC11/12/13ends`;
12 `P1ProgDir.famProg_of_task_beta` with the cone program `hW`, the D14 bound `betaW_bound` (DispBeta) and the format form
`C13linkFmtTarget` of the C13link program (Sol P1-sol-c13lfmt, owner P1-lean-greedy: a HYPOTHESIS here until it lands);
15 `fam15` (constant `true`, from `Task.const`).
`dispIn`: integ's `DispIn` (FinalInputs.lean) from `C13linkFmtTarget` alone, with `ck := dispCk`, `cnt := dispCnt`.
-/

namespace P1Int

namespace P11

namespace Disp

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

theorem s_le_one (j : ℕ) : (2 : ℝ) ^ (-(j : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

/-- `FamProg` depends on the decider only at long inputs. -/
theorem famProg_congr {A : Type} {letter : Bool → A} {answer : Option A → Bool} {Rc : Prog A}
    {ck ck' : List Bool → List Bool → ℕ → Bool} {s : ℝ} {a b cc n₂ n₀ : ℕ}
    (h : ∀ x : List Bool, n₀ ≤ x.length → ∀ u i, ck x u i = ck' x u i)
    (hf : FamProg letter answer Rc ck s a b cc n₂) : FamProg letter answer Rc ck' s a b cc (max n₂ n₀) := by
  intro x hx
  obtain ⟨bnd, hb, hans⟩ := hf x (le_of_max_le_left hx)
  refine ⟨bnd, hb, fun u ρ hρ => ?_⟩
  rw [← h x (le_of_max_le_right hx)]
  exact hans u ρ hρ

/-- **Family 15**: the constant `true` as `FamProg` (program: discard the input, write `true`). -/
theorem fam15 {s : ℝ} (hs : s ≤ 1) {a b : ℕ} (hb : 1 ≤ b) :
    ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), FamProg Ltr.bit P1Dispatch.answer Rc (fun _ _ _ => true) s a b cc n₂ := by
  refine P1ProgDir.famProg_of_task hs hb (fun _ _ _ => true) 0 ?_
  refine (Task.const (send true) (fun p : P1ChkFinal.QDom (lpM2 s a b) (fun n => lpK2 a b n - 4) => send p.val)).bound
    6 (fun p => ?_)
  change size p.val + 1 ≤ 6 * (P1ChkFinal.budget 0 p.val + 1)
  obtain ⟨⟨x, u, ρ⟩, _⟩ := p
  simp only [size_prod, P1Dispatch.size_list, P1ChkFinal.budget, pow_zero]
  omega

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
  (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)

include κ hκ in
open Classical in
/-- **Item p11_dispatch: the 16 family programs** for the deciders `dispCk`, at the real parameters. -/
theorem dispFam (hb : 1 ≤ b) (hC13 : P1ChkFinal.C13linkFmtTarget) (cW : ℕ)
    (hW : ∀ M K : ℕ → ℕ, P1ChkFinal.WHyp bs Wof M K (P1SolCone.βW Bt V a b cW)) :
    ∀ c' < 16, ∃ (Rc : Prog Ltr) (cc n₂ : ℕ), FamProg Ltr.bit P1Dispatch.answer Rc
      (dispCk Bt V a b d bigBias termBias bs l Wof c') ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂ := by
  have hs := s_le_one (portConsts Bt).j
  intro c' hc'
  interval_cases c'
  · exact P1ChkFinal.FamClosed.famC1_closed Bt κ hκ V a b d bigBias termBias hs hb
  · exact P1ChkFinal.FamClosed.famC2_closed Bt κ hκ V a b d bigBias termBias hs hb
  · exact P1ChkFinal.FamClosed.famC3_closed Bt κ hκ V a b d bigBias termBias hs hb
  · obtain ⟨Rc, cc, h⟩ := P1ProgDir.FamDir.famC4 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias _ hs hb
      (four_le_baseDegree S) (fun kk => ((Fintype.equivFin (toOAI V).K kk : Fin _) : ℕ))
    exact ⟨Rc, cc, 16, h⟩
  · exact P1ChkFinal.FamGreedy.famC5_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias hs hb
  · exact P1ChkFinal.FamGreedy.famC6_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias hs hb
  · exact P1ChkFinal.FamClosed.famC7all_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias Bt.shrink hs hb
  · exact P1ChkFinal.FamGreedy.famC8_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias Bt.shrink hs hb
  · exact P1ChkFinal.FamGreedy.famC9_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias hs hb
  · obtain ⟨n₀, hfit⟩ := P1SolDirFit.dirFit Bt κ hκ V a b d bigBias termBias
    obtain ⟨Rc, cc, n₂, h⟩ := P1C10.famC10_closed Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias n₀ hs hb
      (fun n hn => (hfit n hn).2)
    refine ⟨Rc, cc, max n₂ n₀, famProg_congr (fun x hx u i => ?_) h⟩
    show decide (P1C10.C10w (P1C10.fx10 Bt)
        (P1C10.cutDims n₀ (P1C10.genD Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias)) x u i) =
      decide (P1C10.C10w (P1C10.fx10 Bt) (gdims Bt V a b d bigBias termBias) x u i)
    have e : P1C10.cutDims n₀ (P1C10.genD Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias) x.length =
        gdims Bt V a b d bigBias termBias x.length := P1C10.cutDims_of_le _ hx
    apply decide_eq_decide.mpr
    unfold P1C10.C10w
    rw [e]
  · exact P1ChkFinal.FamFinal.famC11 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias hs hb
  · exact P1ChkFinal.FamFinal.famC12 Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias hs hb
  · obtain ⟨cβ, hβ⟩ := betaW_bound Bt V a b cW
    obtain ⟨c, T⟩ := hC13 bs (gdims Bt V a b d bigBias termBias) Wof (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b)
      (fun n => lpK2 a b n - 4) (P1SolCone.βW Bt V a b cW) P1ChkFinal.batchHyp P1SolFmt.SolLength.lenHyp
      (P1SolFmt.SolFormat.fmtHyp_genuine Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias) (hW _ _)
    exact P1ProgDir.famProg_of_task_beta hs hb
      (fun x u i => decide (P1ChkFinal.C13linkw bs (gdims Bt V a b d bigBias termBias) Wof x u i)) c cβ _ hβ T
  · exact P1ChkFinal.FamFinal.famC13ends Bt (portConsts Bt) (toOAI V) 1 a b d bigBias termBias bs l hs hb
  · exact P1ChkFinal.FamClosed.famC14_closed Bt κ hκ V a b d bigBias termBias hs hb
  · exact fam15 hs hb

end

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)

/-- **integ's input `DispIn`** (FinalInputs.lean), with the ONE hypothesis `C13linkFmtTarget` (Sol P1-sol-c13lfmt). -/
theorem dispIn_of [Fintype F] (hC13 : P1ChkFinal.C13linkFmtTarget) (d : ℕ) (bs : Module.Basis (Fin d) (ZMod 2) F)
    (l : F →ₗ[ZMod 2] ZMod 2) : DispIn Bt κ hκ d bs l := by
  intro V a b bigBias termBias values _hv hf cW hW hb
  have hfam := dispFam Bt κ hκ V a b d bigBias termBias bs l
    (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) hb hC13 cW hW
  refine ⟨fun c' => if h : c' < 16 then some (hfam c' h).choose else none,
    dispCk Bt V a b d bigBias termBias bs l (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose),
    dispCnt Bt V a b d bigBias termBias, fun c' hc' => ?_, ?_⟩
  · have hc16 : c' < 16 := hc'
    exact ⟨(hfam c' hc16).choose, dif_pos hc16, (hfam c' hc16).choose_spec⟩
  · obtain ⟨n₀, hfit⟩ := dispCnt_fit Bt V a b d bigBias termBias hb
    refine ⟨n₀, fun x hx => ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
      dispCk_iff Bt V a b d bigBias termBias bs l (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) x
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun c hc => hfit x.length hx c hc,
      fun u c hc i _ hst => dispCk_out Bt V a b d bigBias termBias bs l
        (P1P5.Cone.coneWof Bt V a b d bigBias termBias values hf.choose) x (List.ofFn u) c hc i hst⟩

/-- **integ's input `DispIn`, with NO hypothesis**: `C13linkFmtTarget` is `P1ChkFinal.SolFinal.progC13linkFmt`
(Sol P1-sol-c13lfmt, P1SolFinal/C13lFmt.lean sha256 887f6279.., accepted by P1-lean-greedy). -/
theorem dispIn [Fintype F] (d : ℕ) (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) :
    DispIn Bt κ hκ d bs l :=
  dispIn_of Bt κ hκ P1ChkFinal.SolFinal.progC13linkFmt d bs l

/-- The delivered C13link program has exactly the target type. -/
example : P1ChkFinal.C13linkFmtTarget := P1ChkFinal.SolFinal.progC13linkFmt

end Disp

end P11

end P1Int

#print axioms P1Int.P11.Disp.fam15
#print axioms P1Int.P11.Disp.dispFam
#print axioms P1Int.P11.Disp.dispIn_of
#print axioms P1Int.P11.Disp.dispIn
