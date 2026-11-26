import P1Int.NetHyp
import P1Wrap.SolutionTransfer
import P1Wrap.Params
import OAI.Computability.MultitapeWeakETH.PortTemplates

/-!
# P1Int.PortData: the fixed data of Case 2 from `PortTwo`; `CountHyp` from the port (queue item 3)

Owner: P1-lean-integ (second restart, 2026-11-25).

* `portData_of_portTwo`: from the port in characteristic two (OpenAI's patched `templates_of_port_over`, i.e.
  Theorem 7.1 of the VP/VNP paper over `AlgebraicClosure (ZMod 2)`) and P0 (lane wrap,
  `P1Wrap.isSolution_kappaF`): a block schedule `S`, templates `Bt`, a FINITE `F_2`-algebra `F` that is a domain,
  a solution `κ : Bt.Entry → F` of the template equations, a basis of `F` over `ZMod 2` and a functional `l` with
  `l 1 = 1`, with `0 < S.laneBits` and `2 ≤ Bt.growthConstant`.
* `OpenP11`: THE ONE OPEN PROP of the final theorem in its sharpest current form: for every such port data there is
  a dyadic exponent `j` with `NetHyp Bt κ hκ bs l (2^-j)`.
* `countHyp_of_portTwo : OpenP11 → PortTwo → ∃ j, CountHyp (2^-j)`.
* Parameter facts for the lanes that instantiate `NetInput` with `P1Wrap.Params` at `t = lpTime a b n`:
  `run_bound` (`t ≤ I · 2^h · B`, the `hT` of `NetInput`), `lane_bound` (`T · laneBits ≤ h`, the `hn` of `NetInput`),
  `neZero_B`, `neZero_I`.
-/

namespace P1Int

namespace P11

open Module OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- **The fixed data of Case 2**, from the port and P0. -/
theorem portData_of_portTwo (port : PortTwo) :
    ∃ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) (_ : CommRing F)
      (_ : Algebra (ZMod 2) F) (_ : Finite F) (_ : IsDomain F) (κ : Bt.Entry → F) (_ : Bt.IsSolution κ)
      (D : ℕ) (_ : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2),
      l 1 = 1 ∧ 0 < S.laneBits ∧ 2 ≤ Bt.growthConstant := by
  obtain ⟨S, Bt, hlane, hgrow, κ, hκ⟩ :=
    OAI.Computability.MultitapeWeakETH.templates_of_port_over port
  obtain ⟨hfin, hsol, l, hl⟩ := P1Wrap.isSolution_kappaF Bt κ hκ
  refine ⟨S, Bt, P1Wrap.Fsub κ, inferInstance, inferInstance, hfin, inferInstance, P1Wrap.kappaF κ, hsol, ?_⟩
  exact ⟨Module.finrank (ZMod 2) (P1Wrap.Fsub κ), Module.finBasis (ZMod 2) (P1Wrap.Fsub κ), l, hl, hlane,
    hgrow⟩

/-- **The one open Prop of the final theorem** (P11 in network form): for the data of every port, some dyadic
exponent `j` has `NetHyp` at `s = 2^-j`. Owners of its content: lanes net, P5, checks (chkdir, chkfinal) and the
outside provers; the glue from here to `C1Challenge.c1` is proved (`P1Final.c1_of_openP11`). -/
def OpenP11 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ∃ j : ℕ, NetHyp Bt κ hκ bs l ((2 : ℝ) ^ (-(j : ℤ)))

/-- **`CountHyp` from the port**, given the open Prop. -/
theorem countHyp_of_portTwo (h : OpenP11) (port : PortTwo) :
    ∃ j : ℕ, CountHyp ((2 : ℝ) ^ (-(j : ℤ))) := by
  obtain ⟨S, Bt, F, hF, hA, hfin, hdom, κ, hκ, D, bs, l, hl, hlane, hgrow⟩ := portData_of_portTwo port
  obtain ⟨j, hj⟩ := @h S Bt F hF hA hfin hdom κ hκ D bs l hl hlane hgrow
  exact ⟨j, countHyp_of_netHyp Bt κ hκ bs l hl hj⟩

/-! ## Parameter facts (`P1Wrap.Params` at any time bound `t`) -/

/-- **Run bound** (`hT` of `NetInput` with `I = Params.I aM t`, `h = Params.h t`, `B = Params.B t`): the routed
network covers at least `t` steps. No lower bound on `t` is needed. -/
theorem run_bound (aM t : ℕ) (haM : 1 ≤ aM) :
    t ≤ P1Wrap.Params.I aM t * 2 ^ P1Wrap.Params.h t * P1Wrap.Params.B t := by
  have e1 := P1Wrap.Params.le_ceilDiv_mul (aM * 2 ^ P1Wrap.Params.lam t) (P1Wrap.Params.bb t)
    (P1Wrap.Params.bb_pos t)
  have e3 := P1Wrap.Params.t_le_two_pow_lam t
  have h7 : 2 ^ P1Wrap.Params.lam t ≤ aM * 2 ^ P1Wrap.Params.lam t := Nat.le_mul_of_pos_left _ haM
  have hbb : P1Wrap.Params.I aM t * 2 ^ P1Wrap.Params.h t * P1Wrap.Params.B t =
      P1Wrap.Params.I aM t * P1Wrap.Params.bb t := by
    unfold P1Wrap.Params.bb P1Wrap.Params.N
    ring
  rw [hbb]
  unfold P1Wrap.Params.I
  exact le_trans e3 (le_trans h7 e1)

/-- **Lane budget** (`hn` of `NetInput` with `Tc = Params.T K t`, `h = Params.h t`), when the lane bits of the
schedule are at most the constant `K.b0`. -/
theorem lane_bound (K : P1Wrap.Consts) (laneBits : ℕ) (hS : laneBits ≤ K.b0) (t : ℕ) :
    P1Wrap.Params.T K t * laneBits ≤ P1Wrap.Params.h t := by
  have h1 := P1Wrap.Params.nine_p_add_b0T_le_h K t
  have h2 : P1Wrap.Params.T K t * laneBits ≤ K.b0 * P1Wrap.Params.T K t := by
    rw [Nat.mul_comm K.b0]
    exact Nat.mul_le_mul_left _ hS
  omega

/-- The small block length is positive. -/
theorem neZero_B (t : ℕ) : NeZero (P1Wrap.Params.B t) := ⟨(P1Wrap.Params.B_pos t).ne'⟩

/-- The number of big intervals is positive. -/
theorem neZero_I (aM t : ℕ) (haM : 1 ≤ aM) : NeZero (P1Wrap.Params.I aM t) := by
  refine ⟨fun h0 => ?_⟩
  have e1 := P1Wrap.Params.le_ceilDiv_mul (aM * 2 ^ P1Wrap.Params.lam t) (P1Wrap.Params.bb t)
    (P1Wrap.Params.bb_pos t)
  have h3 : 0 < aM * 2 ^ P1Wrap.Params.lam t := Nat.mul_pos haM (Nat.pos_of_ne_zero (by positivity))
  unfold P1Wrap.Params.I at h0
  rw [h0, Nat.zero_mul] at e1
  exact absurd e1 (Nat.not_le.mpr h3)

end P11

end P1Int
