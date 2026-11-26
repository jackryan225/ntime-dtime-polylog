import P1Int.FinalInputs
import P1Int.FormC4

/-!
# The final wiring (P1-lean-integ): `FinalInputs → OpenChecksStaged`

For every port: the alphabet `Ltr` of the dispatcher, the programs and deciders of `DispIn` (at `bigBias = termBias = 0`
and the cone's `Wof`), the true records `trueH` for long inputs, and `D5Steps` from `d5Steps_asm` with the proved pieces;
then `groupEquiv_of_d5` and `stagedEquiv_of_groups`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1SolCone P1SolCone.SolCone
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- `0 < D` for a basis `Fin D` of a nontrivial module. -/
theorem pos_of_basis {F : Type} [CommRing F] [Nontrivial F] [Algebra (ZMod 2) F] {D : ℕ}
    (bs : Module.Basis (Fin D) (ZMod 2) F) : 0 < D :=
  Fin.pos_iff_nonempty.mpr bs.index_nonempty

set_option maxHeartbeats 1000000 in
theorem finalWiring : FinalWiringTarget := by
  intro hIn S Bt F _ _ _ _ κ hκ D bs l hl1 hlane hgrow
  letI : Fintype F := Fintype.ofFinite F
  have hAll := hIn S Bt F κ hκ D bs l hl1 hlane hgrow
  have hF0 := hAll.2.1
  have hGreedy := hAll.2.2.1
  have hDisp := hAll.2.2.2.1
  have hEnergy := hAll.2.2.2.2
  have hd : 0 < D := pos_of_basis bs
  intro L V a b n₀ hb _hPar
  have hf := hF0 V a b 0 0 hb
  refine Exists.elim (hAll.1 V a b 0 0 hb hf) (fun values h1 => Exists.elim h1 (fun cW h2 => ?_))
  have hv := h2.1
  have hD := hDisp V a b 0 0 values hv hf cW h2.2 hb
  refine Exists.elim hD (fun chk hD => Exists.elim hD (fun ck hD => Exists.elim hD (fun cnt hD => ?_)))
  refine Exists.elim hD.2 (fun n₄ hlong => ?_)
  refine Exists.elim (trueH_facts Bt κ hκ V a b D 0 0 hb) (fun n₂ hTrue => ?_)
  refine Exists.elim (encFits_true Bt κ hκ V a b D 0 0 hb) (fun n₅ hEnc => ?_)
  refine Exists.elim (sizeFacts Bt V a b D 0 0 hb) (fun n₆ hSize => ?_)
  refine Exists.elim (hEnergy V a b 0 0 hb) (fun n₇ hEF => ?_)
  refine ⟨Ltr, P1Dispatch.ltrFintype, P1Dispatch.answer, Ltr.bit, fun _ _ h => Ltr.bit.inj h, fun _ => rfl,
    P1Dispatch.answer, rfl, chk, ck, 0, 0, hD.1, max n₄ (max n₂ (max n₅ (max n₆ n₇))), fun x hx => ?_⟩
  have hx4 : n₄ ≤ x.length := le_of_max_le_left hx
  have hx2 : n₂ ≤ x.length := le_of_max_le_left (le_of_max_le_right hx)
  have hx5 : n₅ ≤ x.length := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right hx))
  have hx6 : n₆ ≤ x.length := le_of_max_le_left (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx)))
  have hx7 : n₇ ≤ x.length := le_of_max_le_right (le_of_max_le_right (le_of_max_le_right (le_of_max_le_right hx)))
  have hH := hTrue x hx2
  have hS := hSize x hx6
  have hI := hS.1
  have hIN := hS.2.1
  have hB := hS.2.2.1
  have hP := hS.2.2.2.1
  have hn := hS.2.2.2.2.1
  have hN := hS.2.2.2.2.2
  haveI : NeZero (fixedDims Bt V a b x D 0 0).I := ⟨hI⟩
  haveI : NeZero ((fixedDims Bt V a b x D 0 0).I * (fixedDims Bt V a b x D 0 0).N) := ⟨hIN⟩
  haveI : NeZero (P1Wrap.Params.B (lpTime a b x.length)) := ⟨hB⟩
  have hl := hlong x hx4
  have hk0 := hl.1
  replace hl := hl.2
  have hk1 := hl.1
  replace hl := hl.2
  have hk2 := hl.1
  replace hl := hl.2
  have hk3 := hl.1
  replace hl := hl.2
  have hk4 := hl.1
  replace hl := hl.2
  have hk5 := hl.1
  replace hl := hl.2
  have hk6 := hl.1
  replace hl := hl.2
  have hk7 := hl.1
  replace hl := hl.2
  have hk8 := hl.1
  replace hl := hl.2
  have hk9 := hl.1
  replace hl := hl.2
  have hk10 := hl.1
  replace hl := hl.2
  have hk11 := hl.1
  replace hl := hl.2
  have hk12 := hl.1
  replace hl := hl.2
  have hk13 := hl.1
  replace hl := hl.2
  have hk14 := hl.1
  replace hl := hl.2
  have hc0 := hl.1
  replace hl := hl.2
  have hc1 := hl.1
  replace hl := hl.2
  have hc2 := hl.1
  replace hl := hl.2
  have hc3 := hl.1
  replace hl := hl.2
  have hc4 := hl.1
  replace hl := hl.2
  have hc5 := hl.1
  replace hl := hl.2
  have hc6 := hl.1
  replace hl := hl.2
  have hc7 := hl.1
  replace hl := hl.2
  have hc8 := hl.1
  replace hl := hl.2
  have hc9 := hl.1
  replace hl := hl.2
  have hc10 := hl.1
  replace hl := hl.2
  have hc11 := hl.1
  replace hl := hl.2
  have hc12 := hl.1
  replace hl := hl.2
  have hc13 := hl.1
  replace hl := hl.2
  have hc14 := hl.1
  replace hl := hl.2
  have hfit := hl.1
  replace hl := hl.2
  have hout := hl
  have henc := hEnc x hx5 hH
  refine ⟨trueH Bt κ hκ V a b x D 0 0 hH, ?_⟩
  let Wof0 := P1P5.Cone.coneWof Bt V a b D 0 0 values hf.choose
  let ck' : ℕ → (Fin (fixedM Bt a b x) → Bool) → ℕ → Bool := fun c u i => ck c x (List.ofFn u) i
  have hni : ∀ c, c ≤ 3 ∨ (10 ≤ c ∧ c ≤ 14) → cnt x.length c ≤ 2 ^ (lpK2 a b x.length - 4) := by
    intro c hc
    exact hfit c (by omega)
  have hE := hEF x hx7
  have hG3 := hGreedy V a b x 0 0 hH hE
  have hBS := hG3.1
  have hBR := hG3.2
  have hGF := P1ChkFinal.GreedyBridge.greedyFieldE Bt κ hκ V a b x D 0 0 hH hE
  have hgreedy := hGF hBS hBR bs l Wof0 ck' (2 ^ (lpK2 a b x.length - 4)) (cnt x.length)
    (fun u i => hk4 _ i) (fun u i => hk5 _ i) (fun u i => hk6 _ i) (fun u i => hk7 _ i) (fun u i => hk8 _ i)
    hc4 hc5 hc6 hc7 hc8 (fun c hc4' hc8' => hfit c (by omega))
  have hc10step := P1C10.c10_field_closed Bt κ hκ V a b x D 0 0 hH (gdims Bt V a b D 0 0) rfl bs l Wof0
    (cnt x.length) hc9 (2 ^ (lpK2 a b x.length - 4)) (hc9 ▸ hfit 9 (by omega)) ck' (fun u i => hk9 _ i)
  have hsteps := d5Steps_asm Bt κ hκ V a b x D 0 0 (trueH Bt κ hκ V a b x D 0 0 hH) hd bs l Wof0
    (2 ^ (lpK2 a b x.length - 4)) (cnt x.length) ck' (fun kk => ((Fintype.equivFin (toOAI V).K kk : Fin _) : ℕ))
    (fun _ => rfl)
    (fun u i => hk0 _ i) (fun u i => hk1 _ i) (fun u i => hk2 _ i) (fun u i => hk3 _ i) (fun u i => hk14 _ i)
    (fun u i => hk10 _ i) (fun u i => hk11 _ i) (fun u i => hk12 _ i) (fun u i => hk13 _ i)
    hc0 hc1 hc2 hc3 hc14 hc10 hc11 hc12 hc13 hni hP hn hN hout hgreedy hc10step
    (c4_bridge Bt κ hκ V a b x D 0 0 _)
    (formSound_asm Bt κ hκ V a b x D 0 0 _)
    (formClose_asm Bt κ hκ V a b x D 0 0 _)
    henc
    (wlink_true Bt κ hκ V a b x D 0 0 hH values hv hf henc)
    (fun σ ι => fixed_finP Bt κ hκ V a b x D 0 0 σ ι)
  exact stagedEquiv_of_groups (groupEquiv_of_d5 _ _ hsteps)

/-- **The final theorem from the named inputs.** -/
theorem openChecksRec_of_inputs (h : FinalInputs) : OpenChecksRec :=
  openChecksRec_of_staged (finalWiring h)

end P11

end P1Int

#print axioms P1Int.P11.openChecksRec_of_inputs
