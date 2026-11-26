import P1Int.ComposeFam

/-!
# P1Int.ComposeStage: composition layer 2, the Bool equivalence from STAGES (owner: P1-lean-integ)

The Bool equivalence of `ChecksFam` ("all 16 families accept `u` for every index `i < 2^(k-4)`" iff "`u` is the code
of a valid tuple") in the stage form of decision D5 (`P1Count.pass_iff_of_groups`):

* `StagedEquiv enc Good ck nf ni`: there are a number of stages `K`, a stage function `stg c' i < K` for every check
  `(c', i)` (`c' < nf`, `i < ni`), and predicates `Tr j u` ("the fields that the first `j` stages read are true")
  with `Tr 0` trivial, the STEP (`Tr j u` → (stage `j` passes ↔ `Tr (j+1) u`): the form of the lanes' `Ck_true` /
  `Ck_unique` stage lemmas), monotone, and the FORM (`Tr K u` ↔ `u = enc t` for a good `t`).
* `pass_iff_of_staged`: then all checks pass iff `u` is the code of a good tuple.
* `ChecksStaged` = `ChecksFam` with the Bool equivalence replaced by `StagedEquiv` for the code `fixedEnc .. H`;
  `checksFam_of_staged`, `openChecksFam_of_staged : OpenChecksStaged → OpenChecksFam`.

The concrete stages (D5 order C1-C3, C14, C4, per level C5-C9 then C10, C11, C12, C13; `Tr` from the sections of
witfill's code) are layer 3 (`P1Int.ComposeStages`).
-/

namespace P1Int

namespace P11

open Module OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

/-- **Staged form of the Bool equivalence** for one input: checks `ck c' u i` (`c' < nf`, `i < ni`), each in a
stage `stg c' i < K`; `Tr j u`: the fields read by the stages `< j` are true. -/
def StagedEquiv {U Tup : Type*} (enc : Tup → U) (Good : Tup → Prop) (ck : ℕ → U → ℕ → Bool) (nf ni : ℕ) :
    Prop :=
  ∃ (K : ℕ) (stg : ℕ → ℕ → ℕ) (Tr : ℕ → U → Prop),
    (∀ c' < nf, ∀ i < ni, stg c' i < K) ∧
    (∀ u, Tr 0 u) ∧
    (∀ j < K, ∀ u, Tr j u →
      ((∀ c' < nf, ∀ i < ni, stg c' i = j → ck c' u i = true) ↔ Tr (j + 1) u)) ∧
    (∀ j < K, ∀ u, Tr (j + 1) u → Tr j u) ∧
    (∀ u, Tr K u ↔ ∃ t, Good t ∧ enc t = u)

/-- **Layer 2, abstract.** -/
theorem pass_iff_of_staged {U Tup : Type*} {enc : Tup → U} {Good : Tup → Prop} {ck : ℕ → U → ℕ → Bool}
    {nf ni : ℕ} (h : StagedEquiv enc Good ck nf ni) (u : U) :
    (∀ c' < nf, ∀ i < ni, ck c' u i = true) ↔ ∃ t, Good t ∧ enc t = u := by
  obtain ⟨K, stg, Tr, hlt, h0, hstep, hmono, hform⟩ := h
  have key := P1Count.pass_iff_of_groups enc Good
    (fun (p : {p : ℕ × ℕ // p.1 < nf ∧ p.2 < ni}) (u : U) => ck p.1.1 u p.1.2 = true)
    (fun j p => stg p.1.1 p.1.2 = j) K (fun p => ⟨_, hlt p.1.1 p.2.1 p.1.2 p.2.2, rfl⟩) Tr h0
    (fun j hj u hu => by
      rw [← hstep j hj u hu]
      exact ⟨fun hg c' hc' i hi hs => hg ⟨(c', i), hc', hi⟩ hs, fun hg p hs => hg p.1.1 p.2.1 p.1.2 p.2.2 hs⟩)
    hmono hform u
  rw [← key]
  exact ⟨fun hall p => hall p.1.1 p.2.1 p.1.2 p.2.2, fun hall c' hc' i hi => hall ⟨(c', i), hc', hi⟩⟩

/-- **Group form** (the form of the lanes' stage lemmas): `P j u` = "group `j` of fields is true" in the lane's own
vocabulary (e.g. `P1ChkDir.DirTrue`); STEP: if the groups `< j` are true, stage `j` passes iff group `j` is true;
FORM (integration): all groups true iff `u` is the code of a good tuple. -/
def GroupEquiv {U Tup : Type*} (enc : Tup → U) (Good : Tup → Prop) (ck : ℕ → U → ℕ → Bool) (nf ni : ℕ) :
    Prop :=
  ∃ (K : ℕ) (stg : ℕ → ℕ → ℕ) (P : ℕ → U → Prop),
    (∀ c' < nf, ∀ i < ni, stg c' i < K) ∧
    (∀ j < K, ∀ u, (∀ k < j, P k u) →
      ((∀ c' < nf, ∀ i < ni, stg c' i = j → ck c' u i = true) ↔ P j u)) ∧
    (∀ u, (∀ k < K, P k u) ↔ ∃ t, Good t ∧ enc t = u)

theorem stagedEquiv_of_groups {U Tup : Type*} {enc : Tup → U} {Good : Tup → Prop} {ck : ℕ → U → ℕ → Bool}
    {nf ni : ℕ} (h : GroupEquiv enc Good ck nf ni) : StagedEquiv enc Good ck nf ni := by
  obtain ⟨K, stg, P, hlt, hstep, hform⟩ := h
  refine ⟨K, stg, fun j u => ∀ k < j, P k u, hlt, fun u k hk => absurd hk (Nat.not_lt_zero k), ?_, ?_, hform⟩
  · intro j hj u hu
    rw [hstep j hj u hu]
    constructor
    · intro hP k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
      · exact hu k hk'
      · subst hk'; exact hP
    · intro h'
      exact h' j (Nat.lt_succ_self j)
  · intro j _ u hu k hk
    exact hu k (Nat.lt_succ_of_lt hk)

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  {D : ℕ} (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)

open scoped Classical in
/-- **`ChecksFam` with the Bool equivalence in stage form.** -/
def ChecksStaged : Prop :=
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
        StagedEquiv (fixedEnc Bt κ hκ V a b x D bigBias termBias H)
          ((netData Bt κ hκ V a x (P1Wrap.Params.B (lpTime a b x.length))
            (P1Wrap.Params.I 1 (lpTime a b x.length))
            (P1Wrap.Params.T (portConsts Bt) (lpTime a b x.length))
            (lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) (lpTime a b x.length))
            (fixedOrd Bt κ hκ V a b x)).toCountData.Valid bs l)
          (fun c' u i => ck c' x (List.ofFn u) i) (2 ^ 4) (2 ^ (lpK2 a b x.length - 4))

/-- **Layer 2: `ChecksFam` from `ChecksStaged`.** -/
theorem checksFam_of_staged (h : ChecksStaged Bt κ hκ bs l) : ChecksFam Bt κ hκ bs l := by
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
  refine ⟨A, hA, bit, letter, hlet, hbit, answer, hans, chk, ck, bigBias, termBias, h1.1, ?_⟩
  refine Exists.elim h1.2 (fun n₃ hst => ⟨n₃, fun x hx => ?_⟩)
  refine Exists.elim (hst x hx) (fun H hH => ⟨H, fun u => ?_⟩)
  exact pass_iff_of_staged hH u

end

/-- **The one open input in stage form**, for the data of every port. -/
def OpenChecksStaged : Prop :=
  ∀ (S : BlockSchedule (AlgebraicClosure (ZMod 2))) (Bt : S.Templates) (F : Type) [CommRing F]
    [Algebra (ZMod 2) F] [Finite F] [IsDomain F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (D : ℕ)
    (bs : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2), l 1 = 1 → 0 < S.laneBits →
    2 ≤ Bt.growthConstant → ChecksStaged Bt κ hκ bs l

theorem openChecksFam_of_staged (h : OpenChecksStaged) : OpenChecksFam :=
  fun S Bt F _ _ _ _ κ hκ D bs l hl hlane hgrow =>
    checksFam_of_staged Bt κ hκ bs l (h S Bt F κ hκ D bs l hl hlane hgrow)

theorem openChecksRec_of_staged (h : OpenChecksStaged) : OpenChecksRec :=
  openChecksRec_of_fam (openChecksFam_of_staged h)

end P11

end P1Int

#print axioms P1Int.P11.pass_iff_of_staged
#print axioms P1Int.P11.stagedEquiv_of_groups
#print axioms P1Int.P11.checksFam_of_staged
#print axioms P1Int.P11.openChecksRec_of_staged
