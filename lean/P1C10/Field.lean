import P1C10.Code
import P1C10.Targets
import P1Int.TrueH
import P1Int.FormDefs

/-!
# P1C10.Field: the field `c10` of `P1Int.P11.D5Steps` (lane P1-lean-c10wire, 2026-11-25)

Vocabulary of the integration (Interfaces/P1Int/FormDefs.lean, p1intB-77): `G.greedy l = greedyG .. H l`,
`G.c10 l = c10G .. H l`. Family 9 is `ck 9 u i = decide (C10w fx dims x (List.ofFn u) i)` with `dims x.length =
fixedDims ..`, index count `X.cnt 9 = P1ChkGreedy.cntBase D` and level `X.lev 9 i = i % 2 ^ P1ChkGreedy.levBits D`.

* `c10_idx_iff` (proved): the D5 index form of family 9 at level `l` = C10 on codes at every address of level `l+1`.
* `C10CoreStmt H fx` (statement): for every tuple `t` whose level-`l` sections agree with `u`, C10 at level `l` passes
  at every address of level `l + 1` iff the panel sections of level `l + 1` agree with `t`.
* `C10CoreTarget` (the Sol target): `C10CoreStmt` holds for the true records `trueH` and every `fx` that is right at
  every shrinking substep and at the refresh substep of the schedule.
* `d5_c10_field` (proved): the core gives the field `c10` of `D5Steps` in the integration's vocabulary.
-/

namespace P1C10

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.IntegerMultiplication OAI.DepthThreeLowerBound Module
open P1Wit

/-! ## The index form of family 9 at one level -/

/-- **Family 9 at level `l` in the D5 index form** (`cnt = P1ChkGreedy.cntBase`, `lev i = i % 2^L`) is C10 on codes at every
address of level `l + 1`. -/
theorem c10_idx_iff (fx : C10Fix) (dims : ℕ → Dims) (x w : List Bool) (ni cnt : ℕ) (lev : ℕ → ℕ)
    (hcnt : cnt = P1ChkGreedy.cntBase (dims x.length)) (hlev : ∀ i, lev i = i % 2 ^ P1ChkGreedy.levBits (dims x.length))
    (hni : P1ChkGreedy.cntBase (dims x.length) ≤ ni) (P : ℕ → Prop) (hP : ∀ i, P i ↔ C10w fx dims x w i)
    {l : ℕ} (hl : l < (dims x.length).top) :
    (∀ i < ni, i < cnt → lev i = l → P i) ↔
      ∀ Y < ((dims x.length).lv (l + 1)).bases, C10at fx (dims x.length) w l Y := by
  rw [← C10w_level fx dims x w hl]
  have hL : l < 2 ^ P1ChkGreedy.levBits (dims x.length) := P1ChkGreedy.lev_lt (dims x.length) (Nat.le_of_lt hl)
  constructor
  · intro h Y hY
    have hb := P1ChkGreedy.bases_le_maxBases (dims x.length) (show l + 1 ≤ (dims x.length).top by omega)
    have hi : P1ChkGreedy.encIdx (dims x.length) l Y < P1ChkGreedy.cntBase (dims x.length) := by
      unfold P1ChkGreedy.encIdx P1ChkGreedy.cntBase
      have h1 : 2 ^ P1ChkGreedy.levBits (dims x.length) * (Y + 1) ≤ 2 ^ P1ChkGreedy.levBits (dims x.length) * P1ChkGreedy.maxBases (dims x.length) :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    exact (hP _).1 (h _ (by omega) (by omega) (by rw [hlev, P1ChkGreedy.encIdx_mod _ (Nat.le_of_lt hl)]))
  · intro h i _ _ hlv
    have hmod : i % 2 ^ P1ChkGreedy.levBits (dims x.length) = l := by rw [← hlev]; exact hlv
    rw [hP]
    by_cases hidx : C10Idx (dims x.length) i
    · have hY : i / 2 ^ P1ChkGreedy.levBits (dims x.length) < ((dims x.length).lv (l + 1)).bases := by
        have h' := hidx
        unfold C10Idx at h'
        rw [← hmod]
        exact h'.2
      have he : P1ChkGreedy.encIdx (dims x.length) l (i / 2 ^ P1ChkGreedy.levBits (dims x.length)) = i := by
        unfold P1ChkGreedy.encIdx
        rw [← hmod]
        exact Nat.mod_add_div i _
      have h2 := h _ hY
      rw [he] at h2
      exact h2
    · exact fun h' => absurd h' hidx

/-! ## The core statement at the fixed parameters -/

noncomputable section

section Core

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **The core of the step `c10`.** For every level `l < top`, every witness `u` and every tuple `t` whose level-`l`
sections all agree with `u`: check C10 at level `l` passes at every address of level `l + 1` iff the panel sections
(`panelKind`) of level `l + 1` agree with `t`. -/
def C10CoreStmt (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) (fx : C10Fix) : Prop :=
  ∀ l < (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).top,
  ∀ (u : Fin (P1Int.P11.fixedM Bt a b x) → Bool) (t : (P1Int.P11.fixedCD Bt κ hκ V a b x).Tup d),
    (∀ kk : Mem, P1Int.P11.SecEq Bt κ hκ V a b x d bigBias termBias H u t (secLev l kk)) →
    ((∀ Y < ((P1Int.P11.fixedDims Bt V a b x d bigBias termBias).lv (l + 1)).bases,
        C10at fx (P1Int.P11.fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) l Y) ↔
      ∀ kk : Mem, P1Int.P11.panelKind kk = true →
        P1Int.P11.SecEq Bt κ hκ V a b x d bigBias termBias H u t (secLev (l + 1) kk))

end Core

theorem schedule_hD' {k : Type*} [Field k] (S : BlockSchedule k) :
    1 < 2 ^ S.degreeExponent (Fin.last S.steps) := by
  have := S.port_order
  omega

theorem schedule_hd' {k : Type*} [Field k] (S : BlockSchedule k) :
    2 ^ S.expanderExponent + 1 ≤ 2 ^ S.degreeExponent 0 :=
  S.degree_bounds.2

/-- **The Sol target of the step `c10`**: the core holds for the true records and for every `fx` that is right at
every shrinking substep (`ShrinkCodeOK` at the keys `(degreeExponent i, degreeExponent (i+1))`) and at the refresh
substep (`RefreshCodeOK` at the schedule's port graph and refresh template, expander degree `2 ^ expanderExponent`). -/
def C10CoreTarget : Prop :=
  ∀ {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias) (fx : C10Fix),
    (∀ i : Fin S.steps, ShrinkCodeOK Bt.shrink (S.shrink i)
      (fx.rcS (S.degreeExponent i.castSucc) (S.degreeExponent i.succ))) →
    RefreshCodeOK (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD' S) (schedule_hd' S) fx.rcR →
    fx.dH = 2 ^ S.expanderExponent →
    C10CoreStmt Bt κ hκ V a b x d bigBias termBias (P1Int.P11.trueH Bt κ hκ V a b x d bigBias termBias hH) fx

/-! ## The field `c10` of `D5Steps` from the core -/

section FieldStep

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **The field `c10` of `P1Int.P11.D5Steps`** (ComposeD5.lean:224) for the integration's groups
(`G.greedy l ↔ greedyG l`, `G.c10 l ↔ c10G l`) and family 9 = `C10w fx dims` with `dims |x| = fixedDims`, from the core. -/
theorem d5_c10_field (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) (fx : C10Fix)
    (hcore : C10CoreStmt Bt κ hκ V a b x d bigBias termBias H fx)
    (dims : ℕ → Dims) (hD : dims x.length = P1Int.P11.fixedDims Bt V a b x d bigBias termBias)
    (X : P1Int.P11.D5Index) (G : P1Int.P11.D5Groups (Fin (P1Int.P11.fixedM Bt a b x) → Bool)) (ni : ℕ)
    (ck : ℕ → (Fin (P1Int.P11.fixedM Bt a b x) → Bool) → ℕ → Bool)
    (htop : X.top = (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).top)
    (hcnt : X.cnt 9 = P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias))
    (hlev : ∀ i, X.lev 9 i = i % 2 ^ P1ChkGreedy.levBits (P1Int.P11.fixedDims Bt V a b x d bigBias termBias))
    (hni : P1ChkGreedy.cntBase (P1Int.P11.fixedDims Bt V a b x d bigBias termBias) ≤ ni)
    (hck : ∀ u i, ck 9 u i = true ↔ C10w fx dims x (List.ofFn u) i)
    (hgr : ∀ l u, G.greedy l u ↔ P1Int.P11.greedyG Bt κ hκ V a b x d bigBias termBias H l u)
    (hc10 : ∀ l u, G.c10 l u ↔ P1Int.P11.c10G Bt κ hκ V a b x d bigBias termBias H l u) :
    ∀ l < X.top, ∀ u, (∀ j < 5 + 2 * l, G.P X.top j u) →
      ((∀ i < ni, i < X.cnt 9 → X.lev 9 i = l → ck 9 u i = true) ↔ G.c10 l u) := by
  intro l hl u hu
  have hgreedy : G.greedy l u := by
    have h := hu (4 + 2 * l) (by omega)
    rwa [G.P_greedy hl] at h
  have hl' : l < (dims x.length).top := by rw [hD, ← htop]; exact hl
  rw [hc10, c10_idx_iff fx dims x (List.ofFn u) ni (X.cnt 9) (X.lev 9) (by rw [hcnt, hD]) (by rw [hD]; exact hlev)
    (by rw [hD]; exact hni) (fun i => ck 9 u i = true) (hck u) hl', hD]
  have hlt : l < (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).top := by rw [← htop]; exact hl
  obtain ⟨t, htrit, hlv⟩ := (hgr l u).1 hgreedy
  constructor
  · intro hY
    exact ⟨t, htrit, hlv, (hcore l hlt u t (fun kk => hlv l (Nat.lt_succ_self l) kk)).1 hY⟩
  · rintro ⟨t', _, h2, h3⟩
    exact (hcore l hlt u t' (fun kk => h2 l (Nat.lt_succ_self l) kk)).2 h3

end FieldStep

end

/-- Statement check: the conclusion of `d5_c10_field` is the type of the field `c10` of `D5Steps`. -/
example {U Tup : Type} (enc : Tup → U) (Good : Tup → Prop) (ck : ℕ → U → ℕ → Bool) (ni : ℕ)
    (X : P1Int.P11.D5Index) (G : P1Int.P11.D5Groups U) (h : P1Int.P11.D5Steps enc Good ck ni X G) :
    ∀ l < X.top, ∀ u, (∀ j < 5 + 2 * l, G.P X.top j u) →
      ((∀ i < ni, i < X.cnt 9 → X.lev 9 i = l → ck 9 u i = true) ↔ G.c10 l u) :=
  h.c10

end P1C10

#print axioms P1C10.c10_idx_iff
#print axioms P1C10.d5_c10_field
