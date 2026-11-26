import P1Int.WitnessFit
import P1Dispatch.BudgetBounds

/-!
# P1Int.Assembly: `OpenP11` from TWO lane-level inputs, with the parameters fixed (queue item 3, assembly frame)

Owner: P1-lean-integ (second restart, 2026-11-25). `P1Int.P11.OpenP11` asks, per input, for parameters, a run bound,
a lane budget, the dispatcher budget and `4 ≤ lpK2`. This file FIXES the parameters and proves those facts, so that
two named inputs remain:

* `NetP4 S F` (lane net + P1-astra-contract): `P1Net.ContractEqCount` for the routed network of every Challenge
  machine, input, block length, number of big intervals, lane bits and skeleton candidate, at the base degree of `S`,
  with the Beneš settings `P1Benes.NetBridge.bset`, over the ring `F`.
* `ChecksHyp Bt κ hκ bs l` (check lanes + P5 + Sol witfill): for every two-constant parity verifier with `1 ≤ b`:
  an alphabet, the check programs `chk` (16 families, D5), a constant `c ≥ 1` and a threshold `n₁`, such that for
  every input `x` with `|x| ≥ n₁`: every check program answers within `chkBudget c s a b |x| =
  c (lpM2 (lpP2 + 1) + 1)` steps, and there are a final-site order `ord`, an injective witness code `enc` and the
  equivalence `hchecks` for the count data `netData` AT THE FIXED PARAMETERS.

FIXED PARAMETERS (tell P1-lean-integ at once if a lane uses other values):
* constants `K = portConsts Bt`: `b0 = S.laneBits`, `C2 = Bt.growthConstant`, `c2 = ⌈log₂ C2⌉`,
  `j = ⌈log₂ (64 (1 + b0 + c2))⌉`; exponent `s = 2^-j`;
* time bound `t = lpTime a b |x|`; block length `B = Params.B t`; big intervals `I = Params.I 1 t` (`aM = 1`);
  lane bits `h = Params.h t`; compression rounds `Tc = Params.T K t`; lane budget proof `lane_bound`;
  guess length `a (|x|² + 1)`, layout `P1Net.withGuessLayout`; machine `toOAI V`; degree input `four_le_baseDegree S`;
* dispatcher: `d = 4` family bits, budget of one check `bnd = chkBudget c s a b |x|`, constant of Lemma P `2 c + 16`
  (`P1Dispatch.cost_le_tight'`, outside prover Sol);
* threshold of Lemma P: `max n₁ 8` (`4 ≤ lpK2` needs `|x| ≥ 8`).

PROVED here: `portConsts`, `four_le_lpK2`, the instances `NeZero (Params.B t)`, `NeZero (Params.I 1 t)`,
`netHyp_of_checks : NetP4 S F → ChecksHyp Bt κ hκ bs l → NetHyp Bt κ hκ bs l (2^-j)`, and
`openP11_of_parts : OpenNetP4 → OpenChecks → OpenP11`.
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression OAI.Computability.VPVNP.WireTensor

/-! ## Fixed parameters -/

/-- **The constants of P10 for a schedule and its templates**: `b0` = lane bits per block, `C2` = growth constant,
`c2 = ⌈log₂ C2⌉`, and the least `j` with `64 (1 + b0 + c2) ≤ 2^j`. -/
noncomputable def portConsts {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) : P1Wrap.Consts where
  j := Nat.clog 2 (64 * (1 + S.laneBits + Nat.clog 2 Bt.growthConstant))
  b0 := S.laneBits
  C2 := Bt.growthConstant
  c2 := Nat.clog 2 Bt.growthConstant
  C2_le := Nat.le_pow_clog one_lt_two _
  j_spec := Nat.le_pow_clog one_lt_two _

theorem portConsts_b0 {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) :
    S.laneBits ≤ (portConsts Bt).b0 := le_rfl

theorem portConsts_C2 {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) :
    Bt.growthConstant ≤ (portConsts Bt).C2 := le_rfl

/-- The small block length of `P1Wrap.Params` is positive (global instance; `NeZero` is a `Prop`). -/
instance instNeZeroParamsB (t : ℕ) : NeZero (P1Wrap.Params.B t) := neZero_B t

/-- The number of big intervals of `P1Wrap.Params` with `aM = 1` is positive. -/
instance instNeZeroParamsI (t : ℕ) : NeZero (P1Wrap.Params.I 1 t) := neZero_I 1 t le_rfl

/-- The budget of one check program: `c (lpM2 (lpP2 + 1) + 1)` (form of `P1Dispatch.ofTask_fin'` with a Task
budget `β ≤ lpM2 (lpP2 + 1)`). -/
noncomputable abbrev chkBudget (c : ℕ) (s : ℝ) (a b n : ℕ) : ℕ :=
  c * (lpM2 s a b n * (lpP2 a b n + 1) + 1)

/-- The selector has at least the four family bits once the input has length 8. -/
theorem four_le_lpK2 (a b n : ℕ) (hn : 8 ≤ n) : 4 ≤ lpK2 a b n := by
  have h8 : 2 ^ 3 < lpTime a b n :=
    lt_of_le_of_lt (le_trans (by norm_num : 2 ^ 3 ≤ 8) hn) (P1Wrap.W3.lt_lpTime a b n)
  exact (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2 h8

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

/-! ## The two lane-level inputs -/

/-- **Input of lane net (P4, routed, with the scalar)** for the schedule `S` and the ring `F`. -/
def NetP4 (S : BlockSchedule k) (F : Type) [CommRing F] : Prop :=
  ∀ (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I] (h : ℕ)
    (σ : NetSk V I h),
    P1Net.ContractEqCount (toOAI V) Bk (netLayout V a x) I σ (four_le_baseDegree S)
      P1Benes.NetBridge.bset F

open scoped Classical in
/-- **Input of the check lanes, P5 and Sol witfill**, at the fixed parameters (module docstring). -/
def ChecksHyp : Prop :=
  ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A)) (c n₁ : ℕ), 1 ≤ c ∧
    ∀ x : List Bool, n₁ ≤ x.length →
      (∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
        ∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc →
        ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
          ∃ v, ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) v
            (chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)) ∧
      ∃ (ord : ∀ (σ : NetSk V (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.h (lpTime a b x.length)))
          (ι : (Bt.execute κ hκ (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (P1Net.rnState (toOAI V) (P1Wrap.Params.B (lpTime a b x.length))
              (P1Wrap.Params.I 1 (lpTime a b x.length)) σ (four_le_baseDegree S))).Choices),
          ((Bt.execute κ hκ (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (P1Net.rnState (toOAI V) (P1Wrap.Params.B (lpTime a b x.length))
              (P1Wrap.Params.I 1 (lpTime a b x.length)) σ (four_le_baseDegree S))).finalState ι).network.Site ≃
            Fin (Fintype.card ((Bt.execute κ hκ (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
              (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
              (P1Net.rnState (toOAI V) (P1Wrap.Params.B (lpTime a b x.length))
                (P1Wrap.Params.I 1 (lpTime a b x.length)) σ
                (four_le_baseDegree S))).finalState ι).network.Site))
        (enc : (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            ord).toCountData.Tup D →
          (Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool))
        (_ : Function.Injective enc),
        ∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
          (∀ c' < 2 ^ 4, ∀ Rc, chk c' = some Rc → ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
            ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true
              (chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)) ↔
          ∃ t, (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            ord).toCountData.Valid bs l t ∧ enc t = u

/-! ## The assembly frame -/

/-- **`NetHyp` at `s = 2^-j` from the two lane-level inputs.** Supplies: the parameters, `4 ≤ lpK2`, the dispatcher
budget (`P1Dispatch.cost_le_tight'`), the run bound (`run_bound`), the lane budget (`lane_bound`). -/
theorem netHyp_of_checks (hnet : NetP4 S F) (hchk : ChecksHyp Bt κ hκ bs l) :
    NetHyp Bt κ hκ bs l ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) := by
  intro L V a b n₀ hb1 hV
  obtain ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, c, n₁, hc, hx⟩ := hchk L V a b n₀ hb1 hV
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, 2 * c + 16, max n₁ 8, fun x hxn => ?_⟩
  have hx1 : n₁ ≤ x.length := le_trans (le_max_left _ _) hxn
  have hx8 : 8 ≤ x.length := le_trans (le_max_right _ _) hxn
  obtain ⟨htot, ord, enc, hinj, hchecks⟩ := hx x hx1
  refine ⟨four_le_lpK2 a b x.length hx8,
    chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length, ?_, ?_, htot, ?_⟩
  · exact Nat.mul_pos hc (Nat.succ_pos _)
  · exact P1Dispatch.cost_le_tight' _ a b c x.length
  · unfold NetInput
    refine ⟨P1Wrap.Params.B (lpTime a b x.length), inferInstance,
      P1Wrap.Params.I 1 (lpTime a b x.length), inferInstance, P1Wrap.Params.h (lpTime a b x.length),
      P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length),
      lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length), ?_⟩
    refine ⟨run_bound 1 (lpTime a b x.length) le_rfl, ?_, ?_⟩
    · intro σ
      exact hnet V a x _ _ _ σ
    · exact ⟨ord, enc, hinj, hchecks⟩

end

/-! ## The two open Props of the final theorem -/

open OAI.Computability.MultitapeWeakETH (PortTwo)

/-- **Open input 1 (lane net + P1-astra-contract)**: P4 for every schedule over the closure of `F_2` and every
commutative ring. -/
def OpenNetP4 : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (F : Type) [CommRing F], NetP4 S F

/-- **Open input 2 (check lanes, P5, Sol provers, Sol witfill)**: `ChecksHyp` for the data of every port. -/
def OpenChecks : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ChecksHyp Bt κ hκ bs l

/-- **`OpenP11` from the two lane-level inputs.** -/
theorem openP11_of_parts (hnet : OpenNetP4) (hchk : OpenChecks) : OpenP11 := by
  intro S Bt F _ _ _ _ κ hκ D bs l hl hlane hgrow
  exact ⟨(portConsts Bt).j,
    netHyp_of_checks Bt κ hκ bs l (hnet S F) (hchk S Bt F κ hκ D bs l hl hlane hgrow)⟩

end P11

end P1Int
