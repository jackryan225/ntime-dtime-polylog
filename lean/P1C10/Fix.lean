import P1C10.ProgClosed
import P1C10.ShrinkClosed
import P1C10.RefreshClosed

/-!
# P1C10.Fix: the fixed data of check C10 for a block schedule (lane P1-lean-c10wire, 2026-11-25)

`fx10 Bt : C10Fix` for the templates `Bt : S.Templates` of a block schedule `S`:
* `rcS := rcCases (shrinkList Bt)`: one entry per shrinking substep `i`, key `(degreeExponent i, degreeExponent (i+1))`,
  value the recomputation of `shrinkProgram_proved Bt.shrink (S.shrink i)` (Sol c10sa, c10-24);
* `rcR := rcRefresh Bt`: the recomputation of `refreshProgram_proved` (Astra c10, c10-18) at the schedule's port graph
  `S.graph` and refresh template `Bt.refresh`;
* `dH := 2 ^ S.expanderExponent`.
Proved here: `fx10_rcS_poly`, `fx10_rcR_poly` (the hypotheses `hS`, `hR` of `ProgC10Target`), `fx10_shrink_ok i`
(the first entry with the key of substep `i` is right for substep `i`: `Ready` is a `Prop`) and `fx10_refresh_ok`.
-/

namespace P1C10

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.SpectralGeometry
open OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.VPVNP.Compression.DegreeRefresh
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1P7 P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-- `ShrinkCodeOK` depends on the `Ready` proof only through the exponents (`Ready` is a `Prop`). -/
theorem shrinkCodeOK_congr {a b a' b' : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
    (B : FixedBlock k demandSource demandTarget supply
      (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
    (ha : a = a') (hb : b = b') (r : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (r' : Ready (2 ^ a') (2 * 2 ^ a' + 1) (2 ^ b') δ) (rc : ShrinkIn → Option PanelCode)
    (h : ShrinkCodeOK B r rc) : ShrinkCodeOK B r' rc := by
  subst ha
  subst hb
  exact h

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)

/-- The shrink recomputation of substep `i` (Sol c10sa's program). -/
def rcShrinkAt (i : Fin S.steps) : ShrinkIn → Option PanelCode :=
  Classical.choose (shrinkProgram_proved Bt.shrink (S.shrink i))

theorem rcShrinkAt_poly (i : Fin S.steps) : Poly (rcShrinkAt Bt i) :=
  (Classical.choose_spec (shrinkProgram_proved Bt.shrink (S.shrink i))).1

theorem rcShrinkAt_ok (i : Fin S.steps) : ShrinkCodeOK Bt.shrink (S.shrink i) (rcShrinkAt Bt i) :=
  (Classical.choose_spec (shrinkProgram_proved Bt.shrink (S.shrink i))).2

/-- The case list: one entry per shrinking substep, key `(degreeExponent i, degreeExponent (i + 1))`. -/
def shrinkList : List ((ℕ × ℕ) × (ShrinkIn → Option PanelCode)) :=
  (List.finRange S.steps).map fun i =>
    ((S.degreeExponent i.castSucc, S.degreeExponent i.succ), rcShrinkAt Bt i)

theorem schedule_hD (S : BlockSchedule k) : 1 < 2 ^ S.degreeExponent (Fin.last S.steps) := by
  have := S.port_order
  omega

theorem schedule_hd (S : BlockSchedule k) : 2 ^ S.expanderExponent + 1 ≤ 2 ^ S.degreeExponent 0 :=
  S.degree_bounds.2

/-- The refresh recomputation (Astra c10's program) at the schedule's port graph and refresh template. -/
def rcRefresh : RefreshIn → Option PanelCode :=
  Classical.choose (refreshProgram_proved (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD S) (schedule_hd S))

theorem rcRefresh_spec :
    Poly (rcRefresh Bt) ∧ RefreshCodeOK (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD S) (schedule_hd S) (rcRefresh Bt) :=
  Classical.choose_spec (refreshProgram_proved (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
    (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD S) (schedule_hd S))

/-- **The fixed data of check C10 for the templates `Bt`.** -/
def fx10 : C10Fix where
  dH := 2 ^ S.expanderExponent
  rcS := rcCases (shrinkList Bt)
  rcR := rcRefresh Bt

/-- Hypothesis `hS` of `ProgC10Target` for `fx10`. -/
theorem fx10_rcS_poly : Poly (fun q : (ℕ × ℕ) × ShrinkIn => (fx10 Bt).rcS q.1.1 q.1.2 q.2) := by
  refine rcCases_proved (shrinkList Bt) ?_
  intro e he
  simp only [shrinkList, List.mem_map, List.mem_finRange, true_and] at he
  obtain ⟨i, rfl⟩ := he
  exact rcShrinkAt_poly Bt i

/-- Hypothesis `hR` of `ProgC10Target` for `fx10`. -/
theorem fx10_rcR_poly : Poly (fx10 Bt).rcR := (rcRefresh_spec Bt).1

/-- **`fx10` is right at every shrinking substep `i`** (the first entry with the key of `i`). -/
theorem fx10_shrink_ok (i : Fin S.steps) :
    ShrinkCodeOK Bt.shrink (S.shrink i)
      ((fx10 Bt).rcS (S.degreeExponent i.castSucc) (S.degreeExponent i.succ)) := by
  show ShrinkCodeOK Bt.shrink (S.shrink i) (rcCases (shrinkList Bt) _ _)
  match hf : (shrinkList Bt).find? (fun e => e.1 == (S.degreeExponent i.castSucc, S.degreeExponent i.succ)) with
  | none =>
    exfalso
    have hmem : ((S.degreeExponent i.castSucc, S.degreeExponent i.succ), rcShrinkAt Bt i) ∈ shrinkList Bt := by
      simp only [shrinkList, List.mem_map, List.mem_finRange, true_and]
      exact ⟨i, rfl⟩
    have h := List.find?_eq_none.1 hf _ hmem
    simp at h
  | some e =>
    have hmem := List.mem_of_find?_eq_some hf
    have hkey := List.find?_some hf
    simp only [shrinkList, List.mem_map, List.mem_finRange, true_and] at hmem
    obtain ⟨j, rfl⟩ := hmem
    simp only [beq_iff_eq, Prod.mk.injEq] at hkey
    have hrc : rcCases (shrinkList Bt) (S.degreeExponent i.castSucc) (S.degreeExponent i.succ) = rcShrinkAt Bt j := by
      funext z
      unfold rcCases
      rw [hf]
    rw [hrc]
    exact shrinkCodeOK_congr Bt.shrink hkey.1 hkey.2 (S.shrink j) (S.shrink i) _ (rcShrinkAt_ok Bt j)

/-- **`fx10` is right at the refresh substep.** -/
theorem fx10_refresh_ok :
    RefreshCodeOK (a₀ := S.degreeExponent 0) S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh (schedule_hD S) (schedule_hd S) (fx10 Bt).rcR :=
  (rcRefresh_spec Bt).2

theorem fx10_dH : (fx10 Bt).dH = 2 ^ S.expanderExponent := rfl

end

end P1C10
