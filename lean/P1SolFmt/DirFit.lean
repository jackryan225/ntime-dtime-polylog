import P1ProgDir.DirFitTarget
import P1Int.RecordsFitProof

open Filter P1Int P1Int.P11 P1ProgDir.DirFit P1Wrap.Params

namespace P1SolDirFit.Sol

theorem trit_le_fixedLen (D : P1Wit.Dims) : 2 * (D.I * D.N * D.r) ≤ D.fixedLen := by
  rw [P1Wit.fixedLen_eq, P1Wit.head_eq, Nat.mul_comm 2]
  omega

end P1SolDirFit.Sol

open private live_choices live_execute from P1Int.RecordsFitProof

theorem P1SolDirFit.dirFit.{u, v} : P1ProgDir.DirFit.DirFitTarget.{u, v} := by
  intro k _ S Bt R _ κ hκ V a b d bigBias termBias
  obtain ⟨n₀, hfit⟩ := eventually_atTop.1
    (witness_fits Bt κ hκ (portConsts Bt) V 1 le_rfl (portConsts_b0 Bt)
      (portConsts_C2 Bt) d bigBias termBias a b)
  refine ⟨n₀, fun n hn => ⟨P1SolDirFit.Sol.trit_le_fixedLen _, ?_⟩⟩
  let t := lpTime a b n
  let σ : Fin (I 1 t * 2 ^ h t) → (toOAI V).K → Fin 3 := fun _ _ => 0
  let X := P1Net.rnState (toOAI V) (B t) (I 1 t) σ (four_le_baseDegree S)
  let laneBound := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  obtain ⟨ι⟩ := live_choices _ (live_execute Bt κ hκ (T (portConsts Bt) t) laneBound X)
  exact (Nat.le_add_right _ _).trans (@hfit n hn inferInstance inferInstance σ ι)

example : P1ProgDir.DirFit.DirFitTarget.{0, 0} := P1SolDirFit.dirFit

#print axioms P1SolDirFit.dirFit
