import P1Int.WitfillGlue
import P1Wrap.ProgDet
import P1Count.Dispatch

/-!
# P1Int.Compose: composition of the checks, layer 1 (programs -> Bool families) (owner: P1-lean-integ)

`ChecksRec` (Interfaces/P1Int/WitfillLink.lean) speaks about the 16 check programs `chk c'` (D5: family bits `c' < 16`,
index bits `ρ` of length `lpK2 - 4`). The check lanes deliver each family as a program that answers
`ck c' x u (bval ρ)` (in their files `decide (CkF ..)`) within the budget. `ChecksBool` is `ChecksRec` with:
* the PROGRAM FACTS per family as one named conjunct (every family `c' < 16` has a program that answers
  `ck c' x u (bval ρ)` within `chkBudget`), and
* the EQUIVALENCE at the level of the Bool families: all `ck c' x u i` with `c' < 16`, `i < 2 ^ (lpK2 - 4)` are true
  iff `u` is the code of a valid tuple (witfill's code with the records `H`).
`checksRec_of_bool : ChecksBool → ChecksRec` (index words by `P1Count.exists_bval`, `P1Count.bval_lt`; answers are
unique, `P1Wrap.progAnswers_unique`). Layer 2 (the Bool equivalence from the stage lemmas of the check lanes,
`P1Count.pass_iff_of_groups`) is the next file.
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

open scoped Classical in
/-- **`ChecksRec` in Bool-family form.** -/
def ChecksBool : Prop :=
  ∀ (L : List Bool → Bool) (V : C1Challenge.Machine) (a b n₀ : ℕ), 1 ≤ b →
    ParDecidesFrom V L (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) n₀ →
  ∃ (A : Type) (_ : Fintype A) (bit : Option A → Bool) (letter : Bool → A)
    (_ : Function.Injective letter) (_ : ∀ v, bit (some (letter v)) = v) (answer : Option A → Bool)
    (_ : answer (some (letter true)) = true) (chk : ℕ → Option (Prog A))
    (ck : ℕ → List Bool → List Bool → ℕ → Bool) (c n₁ bigBias termBias : ℕ), 1 ≤ c ∧
    ∀ x : List Bool, n₁ ≤ x.length →
      (∀ c' < 2 ^ 4, ∃ Rc, chk c' = some Rc ∧
        ∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
        ∀ ρ : List Bool, ρ.length = lpK2 a b x.length - 4 →
          ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) (ck c' x (List.ofFn u) (P1Count.bval ρ))
            (chkBudget c ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length)) ∧
      ∃ H : FixedRecords Bt κ hκ V a b x D bigBias termBias,
        ∀ u : Fin (lpM2 ((2 : ℝ) ^ (-((portConsts Bt).j : ℤ))) a b x.length) → Bool,
          (∀ c' < 2 ^ 4, ∀ i < 2 ^ (lpK2 a b x.length - 4), ck c' x (List.ofFn u) i = true) ↔
          ∃ t, (netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (fixedOrd Bt κ hκ V a b x)).toCountData.Valid bs l t ∧
            fixedEnc Bt κ hκ V a b x D bigBias termBias H t = u

/-- **Layer 1: `ChecksRec` from the Bool-family form.** (`Exists.elim` instead of `rcases`: with a goal that
contains `FixedRecords`, `cases` on the existential chain hits the heartbeat limit, p1intB-53..59.) -/
theorem checksRec_of_bool (h : ChecksBool Bt κ hκ bs l) : ChecksRec Bt κ hκ bs l := by
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
  refine Exists.elim h1 (fun c h1 => ?_)
  refine Exists.elim h1 (fun n₁ h1 => ?_)
  refine Exists.elim h1 (fun bigBias h1 => ?_)
  refine Exists.elim h1 (fun termBias h1 => ?_)
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, c, n₁, bigBias, termBias, h1.1, ?_⟩
  intro x hxn
  have hprog := (h1.2 x hxn).1
  refine Exists.elim (h1.2 x hxn).2 (fun H hequiv => ?_)
  refine ⟨?_, ?_⟩
  · intro u c' hc' Rc hRc ρ hρ
    refine Exists.elim (hprog c' hc') (fun Rc' hR => ?_)
    have e0 : Rc' = Rc := Option.some.inj (hR.1.symm.trans hRc)
    subst e0
    exact ⟨_, hR.2 u ρ hρ⟩
  · refine ⟨H, fun u => Iff.trans ?_ (hequiv u)⟩
    constructor
    · intro hall c' hc' i hi
      refine Exists.elim (P1Count.exists_bval (lpK2 a b x.length - 4) i hi) (fun ρ hρ => ?_)
      refine Exists.elim (hprog c' hc') (fun Rc hR => ?_)
      have e1 := hR.2 u ρ hρ.1
      have e2 := hall c' hc' Rc hR.1 ρ hρ.1
      rw [hρ.2] at e1
      exact P1Wrap.progAnswers_unique e1 e2
    · intro hall c' hc' Rc hRc ρ hρ
      refine Exists.elim (hprog c' hc') (fun Rc' hR => ?_)
      have e0 : Rc' = Rc := Option.some.inj (hR.1.symm.trans hRc)
      subst e0
      have e1 := hR.2 u ρ hρ
      have hlt : P1Count.bval ρ < 2 ^ (lpK2 a b x.length - 4) := by
        rw [← hρ]
        exact P1Count.bval_lt ρ
      rw [hall c' hc' (P1Count.bval ρ) hlt] at e1
      exact e1

end

/-- **The one open input in Bool-family form**, for the data of every port. -/
def OpenChecksBool : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ChecksBool Bt κ hκ bs l

theorem openChecksRec_of_bool (h : OpenChecksBool) : OpenChecksRec := by
  intro S Bt F _ _ _ _ κ hκ D bs l hl hlane hgrow
  exact checksRec_of_bool Bt κ hκ bs l (h S Bt F κ hκ D bs l hl hlane hgrow)

end P11

end P1Int

#print axioms P1Int.P11.checksRec_of_bool
#print axioms P1Int.P11.openChecksRec_of_bool
