import P1Wit.Space
import P1Net.Size
import P1P5.Main

/-! Arithmetic estimates for the routed and compressed witness. -/

namespace P1Wit.SolSpace

open Filter P1Wrap
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (A : S.Templates)
variable {R : Type*} [CommRing R] (κ : A.Entry → R) (hκ : A.IsSolution κ)

/-- Number of big blocks containing guess cells at locations `2*j+1`. -/
def guessBlocks (g b : ℕ) : ℕ := if g = 0 then 0 else (2 * g - 1) / b + 1

/-- The common bit width for arc widths and outer-index entries. -/
def smallWidth (termBias T W : ℕ) : ℕ :=
  termBias + Nat.clog 2 (A.growthConstant ^ T * (W + 1) + 1)

open MotifGrid MotifBlocks MotifSelector

/-- A fixed multiplier for coordinates of admitted outer indices. -/
def indexCoeff {J D U : Type} [Fintype J] [Fintype D] [Fintype U]
    {src dst : D → J} {P : Supply J U} {p : D → ℚ} {q : U → ℚ} {H H' : ℝ}
    (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H') : ℕ :=
  ((∑ i, MotifAdmission.weight p i) + 1) * B.scale * B.radius.num.natAbs * MotifAdmission.denominator q

/-- A choice of `termBias` large enough for either fixed compressor template. -/
def templateTermBias : ℕ := max (indexCoeff A.shrink).size (indexCoeff A.refresh).size

/-- The outer-index coordinates fit whenever the chosen width cap bounds the motif's demands. -/
theorem outerIndex_fits {J D U : Type} [Fintype J] [Fintype D] [Fintype U]
    {src dst : D → J} {P : Supply J U} {p : D → ℚ} {q : U → ℚ} {H H' : ℝ}
    (B : FixedBlock k src dst P (realWidths p) (realWidths q) H H') (hq : ∀ i, 0 < q i)
    {width bias : ℕ} (hbias : (indexCoeff B).size ≤ bias) {d : D → ℕ} (hd : ∀ i, d i ≤ width)
    {v : U → ℕ} (hv : v ∈ MotifConversion.outerIndices B d) (i : U) :
    v i < 2 ^ (bias + Nat.clog 2 (width + 1)) := by
  have hc := MotifAdmission.payloadCap_le p q d B.scale width B.radius B.scale_pos hd
  have hval := MotifAdmission.payload_le_cap q hq v _ _ _
    ((MotifConversion.mem_outerIndices_iff B hq d v).mp hv) i
  have hcoef : indexCoeff B < 2 ^ bias :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hbias)
  rw [pow_add]
  exact (hval.trans hc).trans_lt (mul_lt_mul_of_lt_of_le_of_pos_of_nonneg hcoef
    (Nat.le_pow_clog (by decide) _) (Nat.succ_pos _) (Nat.zero_le _))

variable (K : Consts) (V : FiniteMultiTapeMachine) (aM : ℕ)

/-- The lane input condition follows from `eq:p2` with the actual schedule's lane budget. -/
theorem laneBudget (hb : S.laneBits ≤ K.b0) (t : ℕ) : Params.T K t * S.laneBits ≤ Params.h t := by
  have hh := Params.nine_p_add_b0T_le_h K t
  rw [Nat.mul_comm]
  exact (Nat.mul_le_mul_right _ hb).trans (le_trans (Nat.le_add_left _ _) hh)

/-- The fixed coefficient in the routed tuple-width estimate. -/
def tupleCoeff : ℕ :=
  Fintype.card (P1Net.Ext V.K) * (Fintype.card V.Γ + Fintype.card V.Q + Fintype.card V.K)

/-- The fixed coefficient in the number of initial base sites per big interval. -/
def locCoeff : ℕ := 11 + Fintype.card (P1Net.Ext V.K) + 70 * Fintype.card V.K


theorem guessBlocks_le {g t : ℕ} (haM : 1 ≤ aM) (hg : 2 * g ≤ t) :
    guessBlocks g (Params.bb t) ≤ Params.I aM t := by
  by_cases hz : g = 0
  · simp [guessBlocks, hz]
  · have hb := Params.bb_pos t
    have ht : 2 * g ≤ aM * 2 ^ Params.lam t :=
      hg.trans ((Params.t_le_two_pow_lam t).trans (Nat.le_mul_of_pos_left _ haM))
    simp only [guessBlocks, hz, ↓reduceIte, Params.I]
    have he : (2 * g - 1) / Params.bb t + 1 = (2 * g - 1 + Params.bb t) / Params.bb t := by
      rw [Nat.add_div_right _ hb]
    rw [he]
    exact Nat.div_le_div_right (by omega)

theorem h_succ_le (t : ℕ) : Params.h t + 1 ≤ 10 * (Params.p t + 1) := by
  unfold Params.h
  omega

theorem initial_positions_le {t : ℕ} [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3) :
    (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha).positions ≤
      (20 * locCoeff V) * (Params.I aM t * Params.N t * (Params.p t + 1)) := by
  have hl : P1Net.locCount V.K (Params.h t) ≤ (10 * locCoeff V) * (Params.p t + 1) := by
    calc P1Net.locCount V.K (Params.h t) ≤ locCoeff V * (Params.h t + 1) := P1Net.locCount_le
      _ ≤ locCoeff V * (10 * (Params.p t + 1)) := Nat.mul_le_mul_left _ (h_succ_le t)
      _ = _ := by ring
  rw [P1Net.rn_positions]
  change 2 * (Params.I aM t * P1Net.locCount V.K (Params.h t)) * Params.N t ≤ _
  calc
    _ ≤ 2 * (Params.I aM t * ((10 * locCoeff V) * (Params.p t + 1))) * Params.N t := by
      gcongr
    _ = _ := by ring

theorem initial_width_le {t : ℕ} [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3) :
    (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha).maxWireWidth ≤ P1Net.tupWidth V (Params.B t) := by
  exact Finset.sup_le fun e _ => P1Net.rn_width_le V _ _ σ ha e

theorem smallWidth_le (hC : A.growthConstant ≤ K.C2) (termBias t : ℕ) [NeZero (Params.B t)] :
    smallWidth A termBias (Params.T K t) (P1Net.tupWidth V (Params.B t)) ≤
      (termBias + tupleCoeff V + 4) * (Params.p t + 1) := by
  let W := P1Net.tupWidth V (Params.B t)
  let P := Params.p t
  let c := tupleCoeff V + 1
  have hW : W + 1 ≤ 2 ^ (c + P / 2) := by
    have h := P1Net.tupWidth_le V (Params.B t)
    have hB := Params.B_pos t
    calc W + 1 ≤ tupleCoeff V * Params.B t + Params.B t := Nat.add_le_add h hB
      _ = c * Params.B t := by dsimp [c]; ring
      _ ≤ 2 ^ c * Params.B t := Nat.mul_le_mul_right _ (Params.lt_two_pow' c).le
      _ = _ := by rw [pow_add 2 c (P / 2)]; rfl
  have hG : A.growthConstant ^ Params.T K t ≤ 2 ^ P := by
    calc A.growthConstant ^ Params.T K t ≤ (2 ^ K.c2) ^ Params.T K t :=
      Nat.pow_le_pow_left (hC.trans K.C2_le) _
    _ = 2 ^ (K.c2 * Params.T K t) := by rw [pow_mul]
    _ ≤ 2 ^ P := Nat.pow_le_pow_right (by decide) (by have := Params.c2_T K t; dsimp [P]; omega)
  have hM : A.growthConstant ^ Params.T K t * (W + 1) + 1 ≤ 2 ^ (P + (c + P / 2) + 1) := by
    rw [pow_succ, pow_add]
    have h := Nat.mul_le_mul hG hW
    have hpos : 0 < 2 ^ P * 2 ^ (c + P / 2) := by positivity
    omega
  have hlog : Nat.clog 2 (A.growthConstant ^ Params.T K t * (W + 1) + 1) ≤ P + (c + P / 2) + 1 := by
    exact (Nat.clog_mono_right 2 hM).trans_eq (Nat.clog_pow 2 _ (by decide))
  unfold smallWidth
  calc
    _ ≤ termBias + (P + (c + P / 2) + 1) := Nat.add_le_add_left hlog _
    _ ≤ (termBias + c + 2) + 2 * P := by omega
    _ ≤ _ := by dsimp [c, P]; nlinarith

/-- `eq:zlen` for the actual final width, with a constant independent of the branch. -/
theorem final_width_le (t M : ℕ) [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (hM : A.widthAllowance ≤ (M : ℝ)) (hI : Params.I aM t * Params.bb t ≤ 4 * aM * t)
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (hn : Params.T K t * S.laneBits ≤ Params.h t)
    (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
    (ι : (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices) :
    2 ^ Params.T K t * ((A.execute κ hκ (Params.T K t) hn
      (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).finalState ι).totalWidth ≤
      (4 * aM * (20 * locCoeff V) * (2 ^ S.degreeExponent 0 * tupleCoeff V + M)) *
        t * (Params.p t + 1) := by
  let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
  let Y := (A.execute κ hκ (Params.T K t) hn X).finalState ι
  let b := Params.B t
  let i := Params.I aM t
  let n := Params.N t
  let p := Params.p t + 1
  let c := 20 * locCoeff V
  let d := 2 ^ S.degreeExponent 0 * tupleCoeff V
  have hpos : X.positions ≤ c * (i * n * p) := initial_positions_le V aM ha σ
  have hI' : i * n * b ≤ 4 * aM * t := by
    dsimp [i, n, b]
    rw [mul_assoc, mul_comm (Params.N t) (Params.B t)]
    exact hI
  have hW : P1Net.tupWidth V b ≤ tupleCoeff V * b := P1Net.tupWidth_le V b
  have hE := P1Net.sqrt_energy_le_of_width_le X (P1Net.tupWidth V b)
    (P1Net.rn_width_le V b i σ ha)
  have hE' : Real.sqrt X.energy ≤ ((c * (i * n * b) * p * d : ℕ) : ℝ) := by
    apply hE.trans
    exact_mod_cast (show X.positions * 2 ^ S.degreeExponent 0 * P1Net.tupWidth V b ≤ _ from calc
      _ ≤ (c * (i * n * p)) * 2 ^ S.degreeExponent 0 * (tupleCoeff V * b) := by gcongr
      _ = c * (i * n * b) * p * d := by dsimp [d]; ring)
  have hpos' : X.positions ≤ c * (i * n * b) * p := by
    refine hpos.trans ?_
    rw [mul_assoc c (i * n * b) p, mul_assoc (i * n) b p]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Params.B_pos t)))
  have hallow : A.widthAllowance * X.positions ≤ ((c * (i * n * b) * p * M : ℕ) : ℝ) := by
    rw [Nat.cast_mul, mul_comm _ (M : ℝ)]
    exact mul_le_mul hM (by exact_mod_cast hpos') (by positivity) (by positivity)
  obtain ⟨_, hy, he, _⟩ := A.branch_bounds κ hκ (Params.T K t) hn X ι
  have hclear : (Y.totalWidth : ℝ) * (2 : ℝ) ^ Params.T K t ≤
      Real.sqrt X.energy + A.widthAllowance * X.positions :=
    (le_div_iff₀ (by positivity)).mp (hy.trans he)
  have hsum : (Y.totalWidth : ℝ) * (2 : ℝ) ^ Params.T K t ≤
      ((c * (i * n * b) * p * (d + M) : ℕ) : ℝ) := by
    refine hclear.trans ((add_le_add hE' hallow).trans_eq ?_)
    simp only [Nat.cast_mul, Nat.cast_add]
    ring
  have hnat : Y.totalWidth * 2 ^ Params.T K t ≤ c * (i * n * b) * p * (d + M) := by exact_mod_cast hsum
  rw [mul_comm]
  calc
    _ ≤ c * (i * n * b) * p * (d + M) := hnat
    _ ≤ c * (4 * aM * t) * p * (d + M) := by gcongr
    _ = _ := by ring


/-- P5 bounds the entire pushed chain by a width that fits in the small-number fields. -/
theorem pushed_width_fits (t termBias : ℕ) [NeZero (Params.B t)] [NeZero (Params.I aM t)]
    (ha : 4 ≤ 2 ^ S.degreeExponent 0) (hn : Params.T K t * S.laneBits ≤ Params.h t)
    (σ : Fin (Params.I aM t * 2 ^ Params.h t) → V.K → Fin 3)
    (ι : (A.execute κ hκ (Params.T K t) hn (P1Net.rnState V (Params.B t) (Params.I aM t) σ ha)).Choices) :
    let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
    let M := A.growthConstant ^ Params.T K t * (X.maxWireWidth + 1)
    P1P5.ChainPayloadLe
      ((A.execute κ hκ (Params.T K t) hn X).termChain (A.records κ hκ (Params.T K t) hn X) ι) M ∧
      M < 2 ^ smallWidth A termBias (Params.T K t) (P1Net.tupWidth V (Params.B t)) := by
  dsimp only
  let X := P1Net.rnState V (Params.B t) (Params.I aM t) σ ha
  refine ⟨(P1P5.pushed_factor_bounds A κ hκ (Params.T K t) hn X ι).2.2.1, ?_⟩
  let M' := A.growthConstant ^ Params.T K t * (P1Net.tupWidth V (Params.B t) + 1)
  have hW := initial_width_le V aM ha σ
  have hM : A.growthConstant ^ Params.T K t * (X.maxWireWidth + 1) ≤ M' :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hW)
  have hp : M' + 1 ≤ 2 ^ Nat.clog 2 (M' + 1) := Nat.le_pow_clog (by decide) _
  exact hM.trans_lt ((Nat.lt_succ_self _).trans_le (hp.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))))

end
end P1Wit.SolSpace
