import P1Int.PortData
import P1Wit.SpaceFacts
import P1Wrap.W3Arith

/-!
# P1Int.WitnessFit: the witness of the genuine layout fits into `lpM2` bits (integration of P1-sol-space)

Owner: P1-lean-integ (second restart, 2026-11-25; owner of the outside prover P1-sol-space since 11:41Z).
The two files of research/agents/P1-sol-space (copied UNCHANGED to research/p1/lean/Wit/P1Wit/{SpaceEstimates,
SpaceFacts}.lean) prove, for the dims `P1Wit.SolSpace.genuineDims` and all large time bounds `t`:
`fixedLen + totalWidth of the final state ≤ P1Wrap.Params.m K t` (`genuine_enc_length_le`, from the 20 size facts
`genuine_spaceIn` and P6's `P1Wit.enc_length_le`).

This file is the CONSUMER FORM for `P1Int.P11.NetInput` (the check that the delivered statement is the needed one):
* `m_eq_lpM2`: `Params.m K (lpTime a b n) = lpM2 (2^-K.j) a b n` (the witness length of Lemma P);
* `tendsto_lpTime`;
* `witness_fits`: for all large input lengths `n`, at `t = lpTime a b n`, guess length `g = a (n² + 1)`, the
  parameters `B = Params.B t`, `I = Params.I aM t`, `h = Params.h t`, `Tc = Params.T K t` of `NetInput`, the machine
  `toOAI V`, the degree input `four_le_baseDegree S` and the lane budget `lane_bound`: for every skeleton candidate
  `σ` and branch `ι`, `fixedLen + totalWidth ≤ lpM2 (2^-K.j) a b n`.
Inputs that the final assembly must supply: `1 ≤ aM`, `S.laneBits ≤ K.b0`, `Bt.growthConstant ≤ K.C2`.
-/

namespace P1Int

namespace P11

open Filter OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- The witness length of `P1Wrap.Params` at the time bound of Lemma P is `lpM2` at `s = 2^-j`. -/
theorem m_eq_lpM2 (K : P1Wrap.Consts) (a b n : ℕ) :
    P1Wrap.Params.m K (lpTime a b n) = lpM2 ((2 : ℝ) ^ (-(K.j : ℤ))) a b n := by
  have hT : lpT2 ((2 : ℝ) ^ (-(K.j : ℤ))) a b n = P1Wrap.Params.T K (lpTime a b n) := by
    have h := P1Wrap.W3.lpT2_sOf K.j a b n
    unfold P1Wrap.W3.sOf at h
    rw [h]
    rfl
  unfold lpM2
  rw [hT]
  rfl

/-- The time bound of Lemma P tends to infinity with the input length. -/
theorem tendsto_lpTime (a b : ℕ) : Tendsto (lpTime a b) atTop atTop :=
  tendsto_atTop_mono (fun n => (P1Wrap.W3.lt_lpTime a b n).le) tendsto_id

/-- **The genuine witness fits** (P1-sol-space, in the parameters of `NetInput`). -/
theorem witness_fits {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {R : Type*} [CommRing R]
    (κ : Bt.Entry → R) (hκ : Bt.IsSolution κ) (K : P1Wrap.Consts) (V : C1Challenge.Machine) (aM : ℕ)
    (haM : 1 ≤ aM) (hb0 : S.laneBits ≤ K.b0) (hC2 : Bt.growthConstant ≤ K.C2)
    (d bigBias termBias a b : ℕ) :
    ∀ᶠ n in atTop,
      ∀ [NeZero (P1Wrap.Params.B (lpTime a b n))] [NeZero (P1Wrap.Params.I aM (lpTime a b n))],
      ∀ (σ : Fin (P1Wrap.Params.I aM (lpTime a b n) * 2 ^ P1Wrap.Params.h (lpTime a b n)) →
          (toOAI V).K → Fin 3)
        (ι : (Bt.execute κ hκ (P1Wrap.Params.T K (lpTime a b n))
          (lane_bound K S.laneBits hb0 (lpTime a b n))
          (P1Net.rnState (toOAI V) (P1Wrap.Params.B (lpTime a b n)) (P1Wrap.Params.I aM (lpTime a b n)) σ
            (four_le_baseDegree S))).Choices),
        (P1Wit.SolSpace.genuineDims Bt K (toOAI V) aM (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias
            termBias).fixedLen +
          ((Bt.execute κ hκ (P1Wrap.Params.T K (lpTime a b n))
            (lane_bound K S.laneBits hb0 (lpTime a b n))
            (P1Net.rnState (toOAI V) (P1Wrap.Params.B (lpTime a b n)) (P1Wrap.Params.I aM (lpTime a b n)) σ
              (four_le_baseDegree S))).finalState ι).totalWidth ≤
          lpM2 ((2 : ℝ) ^ (-(K.j : ℤ))) a b n := by
  have h := P1Wit.SolSpace.genuine_enc_length_le Bt κ hκ K (toOAI V) aM haM hb0 hC2
    (four_le_baseDegree S) d bigBias termBias
  filter_upwards [(tendsto_lpTime a b).eventually h] with n hn
  intro instB instI σ ι
  rw [← m_eq_lpM2 K a b n]
  exact @hn instB instI (a * (n ^ 2 + 1)) (by unfold lpTime; omega) σ ι

end P11

end P1Int

#print axioms P1Wit.SolSpace.genuine_spaceIn
#print axioms P1Wit.SolSpace.genuine_enc_length_le
#print axioms P1Int.P11.m_eq_lpM2
#print axioms P1Int.P11.witness_fits
#check @P1Wit.SolSpace.genuine_spaceIn
