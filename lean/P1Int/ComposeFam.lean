import P1Int.Compose
import P1Count.Correct

/-!
# P1Int.ComposeFam: composition layer 1.5, each family program with its OWN constant and threshold (owner: P1-lean-integ)

The check lanes deliver a family program in the form "for `|x| ≥ n₂` there is a budget `bnd ≤ lpCost2 cc s a b |x|`
within which the program answers `ck c' x u (bval ρ)`" (board 2016, P1ProgDir; the extra `4 * 4 +` of their form only
makes `bnd` smaller). `ChecksFam` asks exactly this per family `c' < 16` (each with its own `cc`, `n₂`), plus the Bool
equivalence with its own threshold. `checksBool_of_fam : ChecksFam → ChecksBool`: one constant `C = 1 + Σ cc`, one
threshold `n₃ + Σ n₂` (`lpCost2 cc ≤ chkBudget C`, `P1Count.progAnswers_mono`).
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

/-- The program of one family in the check lanes' form (own constant `cc`, own threshold `n₂`). -/
def FamProg {A : Type} (letter : Bool → A) (answer : Option A → Bool) (Rc : Prog A)
    (ck : List Bool → List Bool → ℕ → Bool) (s : ℝ) (a b cc n₂ : ℕ) : Prop :=
  ∀ x : List Bool, n₂ ≤ x.length → ∃ bnd, bnd ≤ lpCost2 cc s a b x.length ∧
    ∀ u : Fin (lpM2 s a b x.length) → Bool, ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
      ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) (ck x (List.ofFn u) (P1Count.bval ρ)) bnd

open scoped Classical in
/-- **`ChecksBool` with per-family constants.** -/
def ChecksFam : Prop :=
  ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A))
    (ck : ℕ → List Bool → List Bool → ℕ → Bool) (bigBias termBias : ℕ),
    (∀ c' < 2 ^ 4, ∃ Rc, chk c' = some Rc ∧ ∃ cc n₂ : ℕ,
      FamProg letter answer Rc (ck c') ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b cc n₂) ∧
    ∃ n₃ : ℕ, ∀ x : List Bool, n₃ ≤ x.length →
      ∃ H : FixedRecords Bt κ hκ V a b x D bigBias termBias,
        ∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
          (∀ c' < 2 ^ 4, ∀ i < 2 ^ (lpK2 a b x.length - 4), ck c' x (List.ofFn u) i = true) ↔
          ∃ t, (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (fixedOrd Bt κ hκ V a b x)).toCountData.Valid bs l t ∧
            fixedEnc Bt κ hκ V a b x D bigBias termBias H t = u

theorem lpCost2_le_chkBudget {cc C : ℕ} (h : cc ≤ C) (s : ℝ) (a b n : ℕ) :
    lpCost2 cc s a b n ≤ chkBudget C s a b n := by
  unfold lpCost2 chkBudget
  calc cc * lpM2 s a b n * (lpP2 a b n + 1) = cc * (lpM2 s a b n * (lpP2 a b n + 1)) := by ring
    _ ≤ C * (lpM2 s a b n * (lpP2 a b n + 1)) := Nat.mul_le_mul_right _ h
    _ ≤ C * (lpM2 s a b n * (lpP2 a b n + 1) + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- **Layer 1.5: `ChecksBool` from `ChecksFam`.** -/
theorem checksBool_of_fam (h : ChecksFam Bt κ hκ bs l) : ChecksBool Bt κ hκ bs l := by
  intro L V a b n₀ hb1 hV
  refine Exists.elim (h L V a b n₀ hb1 hV) (fun A h1 => ?_)
  refine Exists.elim h1 (fun hA h1 => ?_)
  refine Exists.elim h1 (fun bit h1 => ?_)
  refine Exists.elim h1 (fun letter h1 => ?_)
  refine Exists.elim h1 (fun hlet h1 => ?_)
  refine Exists.elim h1 (fun hbit h1 => ?_)
  refine Exists.elim h1 (fun answer h1 => ?_)
  refine Exists.elim h1 (fun hans h1 => ?_)
  refine Exists.elim h1 (fun chk h1 => ?_)
  refine Exists.elim h1 (fun ck h1 => ?_)
  refine Exists.elim h1 (fun bigBias h1 => ?_)
  refine Exists.elim h1 (fun termBias h1 => ?_)
  refine Exists.elim h1.2 (fun n₃ hequiv => ?_)
  have hp : ∀ c' : Fin (2 ^ 4), ∃ q : Prog A × ℕ × ℕ, chk c'.1 = some q.1 ∧
      FamProg letter answer q.1 (ck c'.1) ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b q.2.1 q.2.2 := by
    intro c'
    obtain ⟨Rc, hRc, cc, n₂, hf⟩ := h1.1 c'.1 c'.2
    exact ⟨(Rc, cc, n₂), hRc, hf⟩
  let q : Fin (2 ^ 4) → Prog A × ℕ × ℕ := fun c' => (hp c').choose
  have hq : ∀ c', chk c'.1 = some (q c').1 ∧
      FamProg letter answer (q c').1 (ck c'.1) ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b (q c').2.1 (q c').2.2 :=
    fun c' => (hp c').choose_spec
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, ck, 1 + ∑ c', (q c').2.1,
    n₃ + ∑ c', (q c').2.2, bigBias, termBias, Nat.le_add_right 1 _, ?_⟩
  intro x hxn
  refine ⟨?_, hequiv x (le_trans (Nat.le_add_right _ _) hxn)⟩
  intro c' hc'
  have hc := hq ⟨c', hc'⟩
  refine ⟨_, hc.1, ?_⟩
  have hn2 : (q ⟨c', hc'⟩).2.2 ≤ x.length :=
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le ((q j).2.2)) (Finset.mem_univ _))
      (le_trans (Nat.le_add_left _ _) hxn)
  obtain ⟨bnd, hbnd, hans'⟩ := hc.2 x hn2
  have hcc : (q ⟨c', hc'⟩).2.1 ≤ 1 + ∑ c'', (q c'').2.1 :=
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le ((q j).2.1)) (Finset.mem_univ _))
      (Nat.le_add_left _ _)
  intro u ρ hρ
  exact P1Count.progAnswers_mono (hans' u ρ hρ)
    (le_trans hbnd (lpCost2_le_chkBudget hcc _ a b x.length))

end

/-- **The one open input in family form**, for the data of every port. -/
def OpenChecksFam : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ChecksFam Bt κ hκ bs l

theorem openChecksRec_of_fam (h : OpenChecksFam) : OpenChecksRec :=
  openChecksRec_of_bool (fun S Bt F _ _ _ _ κ hκ D bs l hl hlane hgrow =>
    checksBool_of_fam Bt κ hκ bs l (h S Bt F κ hκ D bs l hl hlane hgrow))

end P11

end P1Int

#print axioms P1Int.P11.checksBool_of_fam
#print axioms P1Int.P11.openChecksRec_of_fam
