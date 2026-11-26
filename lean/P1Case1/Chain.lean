import P1Case1.Bridge
import P1Case1.Arith
import OAI.Computability.MultitapeWeakETH.FieldTables
import OAI.Computability.MultitapeWeakETH.Price

/-!
# P1, Case 1: the TRANS chain in OpenAI's network language

The two remaining big pieces of Case 1 are stated here as propositions about OpenAI's relation networks
(`OAI.Computability.MultitapeWeakETH.Network`, `Tables.lean`) with `n = N²` input bits and blocks of
`b = N` bits (one block = one row of the matrix):

* `TransTraceBound` (tasks G1 + G2, paper thm:transpose, decision form): every deterministic machine
  deciding TRANS at side `N` within `T` steps gives a bounded network with `O(1 + N + T/N)` vertices and
  relation tables that display `xᵀ` (and nothing else) on a `2^{-A(1+N+T/N)}` fraction of the inputs `x`.
* `TransTableBound` (tasks G3 + G4, paper thm:table): such a display on a `2^{-N²/100}` fraction forces
  `c · N √(log₂ N)` vertices.

Proved here:
* `transTableBound_of_field`: the field form `TransFieldTableBound K` over any infinite field gives
  `TransTableBound` (copy of OpenAI's `partialTableBound_of_field`, generic tables of `returns_of_unique`).
* `transLowerBoundOAI_of_bounds` (G5): `TransTraceBound → TransTableBound → TransLowerBoundOAI`.
* `c1_of_priceTwo_of_parts`, `c1_of_price_over_of_parts`: the statement of `C1Challenge.c1` from
  `PriceTwo` (or `PriceOver k`, `k` infinite) and the three open pieces.
-/

namespace P1Case1

open OAI.DepthThreeLowerBound
open OAI.Computability.MultitapeWeakETH (Word Network PriceOver PriceTwo)

/-- Row-major word of the transpose: entry `(i,k)` of the result is entry `(k,i)` of `x`. -/
def transposeWord {N : ℕ} (x : Word (N * N)) : Word (N * N) := fun j =>
  x (finProdFinEquiv (finProdFinEquiv.symm j).swap)

/-- Fraction of the words of length `n` with a property. -/
noncomputable def wordDensity {n : ℕ} (event : Word n → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card (Word n)

/-- With input `x` on the input terminals, the relation network attains exactly one output word on the
output terminals, and it is the transpose of `x`. -/
def TransGood {N : ℕ} (G : Network (N * N) N) (tables : G.Relation) (x : Word (N * N)) : Prop :=
  G.Attains tables x (transposeWord x) ∧ ∀ other, G.Attains tables x other → other = transposeWord x

/-- **Open piece 1 (tasks G1 + G2).** TRANS coarse trace, decision form. -/
def TransTraceBound : Prop := ∀ M : FiniteMultiTapeMachine, ∃ D A : ℕ, 0 < A ∧ ∃ N₀ : ℕ,
  ∀ N ≥ N₀, ∀ T : ℕ, DecidesTransInOAI M N T →
    ∃ G : Network (N * N) N, G.Bounded D ∧ (G.vertices : ℝ) * N ≤ A * ((N : ℝ) + T + N * N) ∧
      ∃ tables : G.Relation,
        (2 : ℝ) ^ (-(A : ℝ) * (1 + N + (T : ℝ) / N)) ≤ wordDensity (TransGood G tables)

/-- **Open piece 2 (tasks G3 + G4), relation form.** TRANS table bound. -/
def TransTableBound : Prop := ∀ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
  ∀ N ≥ N₀, ∀ G : Network (N * N) N, G.Bounded D → ∀ tables : G.Relation,
    (2 : ℝ) ^ (-(1/100 : ℝ) * (N * N)) ≤ wordDensity (TransGood G tables) →
      c * scale N ≤ G.vertices

/-- Field form of the display: the contraction at input `x` is a nonzero multiple of the basis vector
of `xᵀ`. -/
def TransFieldGood {N : ℕ} (G : Network (N * N) N) {K : Type*} [Field K]
    (tables : (v : Fin G.vertices) → G.View v → K) (x : Word (N * N)) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∀ z, G.contract tables x z = if z = transposeWord x then c else 0

/-- **Open piece 2, field form** (paper thm:table over `K`; the form that the entropy price argument
proves). -/
def TransFieldTableBound (K : Type*) [Field K] : Prop := ∀ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
  ∀ N ≥ N₀, ∀ G : Network (N * N) N, G.Bounded D →
    ∀ tables : (v : Fin G.vertices) → G.View v → K,
      (2 : ℝ) ^ (-(1/100 : ℝ) * (N * N)) ≤ wordDensity (TransFieldGood G tables) →
        c * scale N ≤ G.vertices

/-- Relation networks become field networks with the same displays (generic tables over an infinite
field, OpenAI's `returns_of_unique`). -/
theorem transTableBound_of_field {K : Type*} [Field K] [Infinite K]
    (fieldBound : TransFieldTableBound K) : TransTableBound := by
  classical
  intro D
  obtain ⟨c, hc, N₀, lower⟩ := fieldBound D
  refine ⟨c, hc, N₀, ?_⟩
  intro N hN G bounded relation densityBound
  obtain ⟨tables, repr⟩ := G.returns_of_unique (K := K) relation
  apply lower N hN G bounded tables
  apply densityBound.trans
  unfold wordDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro x hx
  obtain ⟨att, unique⟩ := (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, repr x _ att unique⟩

/-- **G5.** The trace bound and the table bound give the TRANS lower bound for OpenAI's machines. -/
theorem transLowerBoundOAI_of_bounds (trace : TransTraceBound) (table : TransTableBound) :
    TransLowerBoundOAI := by
  intro M
  obtain ⟨D, A, hA, N₁, extract⟩ := trace M
  obtain ⟨c, hc, N₂, hard⟩ := table D
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨κ, hκ, N₃, arith⟩ := g5_arith A c hA' hc
  refine ⟨κ, hκ, max N₁ (max N₂ N₃), fun N hN T hdec => ?_⟩
  have hN1 : N₁ ≤ N := le_of_max_le_left hN
  have hN2 : N₂ ≤ N := le_trans (le_max_left _ _) (le_of_max_le_right hN)
  have hN3 : N₃ ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  obtain ⟨small, large⟩ := arith N hN3 T
  by_cases hT : (T : ℝ) ≤ N * N * Real.sqrt (Real.logb 2 N)
  · obtain ⟨loss, conclude⟩ := small hT
    obtain ⟨G, bounded, size, tables, dens⟩ := extract N hN1 T hdec
    have dens' : (2 : ℝ) ^ (-(1/100 : ℝ) * (N * N)) ≤ wordDensity (TransGood G tables) :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) loss).trans dens
    exact conclude G.vertices size (hard N hN2 G bounded tables dens')
  · exact large hT

/-- **Case 1, assembled, over any infinite field `k`.** The statement of `C1Challenge.c1` (with
`σ = 1/4`, `L = coTRANS`) from `PriceOver k` and the three open pieces: the TRANS trace bound
(G1 + G2), the field table bound from `PriceOver k` (G3 + G4) and the NTIME upper bound of coTRANS (C1). -/
theorem c1_of_price_over_of_parts (k : Type) [Field k] [Infinite k]
    (trace : TransTraceBound)
    (fieldTable : PriceOver k → TransFieldTableBound k)
    (upper : C1Challenge.NTIMELinLog coTRANS)
    (price : PriceOver k) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_transLowerBound
    (transLowerBound_of_oai
      (transLowerBoundOAI_of_bounds trace (transTableBound_of_field (fieldTable price)))) upper

/-- **Case 1, assembled, characteristic two** (`k` = algebraic closure of `ZMod 2`; `Infinite` from
the Mathlib instance for algebraically closed fields). -/
theorem c1_of_priceTwo_of_parts
    (trace : TransTraceBound)
    (fieldTable : PriceTwo → TransFieldTableBound (AlgebraicClosure (ZMod 2)))
    (upper : C1Challenge.NTIMELinLog coTRANS)
    (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_price_over_of_parts (AlgebraicClosure (ZMod 2)) trace fieldTable upper price

end P1Case1
