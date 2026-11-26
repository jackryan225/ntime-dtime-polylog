import P1SolCone.ExecutionCone
import P1Wrap.ParamTask
import P1P5.KWRefresh

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif OAI.Computability.VPVNP.Compression.Refresh
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10

private theorem equalConstant_poly (m : ℕ) : Poly (fun n : ℕ => decide (n = m)) := by
  have hbin : Easy binary := Task.self
  have h := P1Wrap.W3.PT.poly_eqW hbin.poly (Code.Poly.const (binary m))
  convert h using 1
  funext n
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, P1Wrap.W3.PT.eqW_iff, value_binary]

/-- Dispatch among finitely many fixed programs by a binary integer key. -/
def dispatchKernel {X A : Type} (fallback : A) : List (ℕ × (X → A)) → ℕ × X → A
  | [], _ => fallback
  | (k, f) :: rest, q => bif decide (q.1 = k) then f q.2 else dispatchKernel fallback rest q

theorem dispatchKernel_poly {X A : Type} [Codec X] [Codec A] (fallback : A)
    (table : List (ℕ × (X → A))) (h : ∀ e ∈ table, Poly e.2) : Poly (dispatchKernel fallback table) := by
  induction table with
  | nil => exact Code.Poly.const fallback
  | cons e es ih =>
    exact Poly.choose (Easy.fst.poly.compose (equalConstant_poly e.1))
      (Easy.snd.poly.compose (h e List.mem_cons_self))
      (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem dispatchKernel_on {X A : Type} (fallback : A) (table : List (ℕ × (X → A)))
    (hn : (table.map Prod.fst).Nodup) {k : ℕ} {f : X → A} (hf : (k, f) ∈ table) (x : X) :
    dispatchKernel fallback table (k, x) = f x := by
  induction table with
  | nil => exact False.elim (List.not_mem_nil hf)
  | cons e es ih =>
    obtain ⟨hnhead, htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hf with rfl | hm
    · simp only [dispatchKernel, decide_true, Bool.cond_true]
    · have hne : k ≠ e.1 := by
        intro he
        apply hnhead
        rw [← he]
        exact List.mem_map_of_mem hm
      simp only [dispatchKernel, decide_eq_false hne, Bool.cond_false]
      exact ih htail hm

private theorem shrink_increases_degree {a b : ℕ} (ready : AllowsShrink a b) : a < b := by
  have ha : 0 < 2 ^ a := Nat.two_pow_pos _
  have hc : 2 ≤ 2 * 2 ^ a + 1 := by omega
  have hpow : 4 ≤ 2 ^ (2 * 2 ^ a + 1) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hc
  have hp : 0 < PackingData.pieceCount (2 ^ a) (2 * 2 ^ a + 1) := by
    unfold PackingData.pieceCount
    have hm := Nat.le_mul_of_pos_right (2 ^ (2 * 2 ^ a + 1)) ha
    omega
  have hsum : 2 ≤ ∑ e, subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) e := by
    calc
      2 ≤ ∑ _ : Fin 4, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => ready.count_pos i)
  have h := (Nat.mul_le_mul (Nat.le_mul_of_pos_right (2 ^ a) hp) hsum).trans ready.degree_budget
  have hlt : 2 ^ a < 2 ^ b := by rw [Nat.mul_two] at h; omega
  by_contra! hab
  exact (not_le_of_gt hlt) (Nat.pow_le_pow_right (by decide) hab)

theorem schedule_exp_injective {k : Type} [Field k] (S : BlockSchedule k) :
    Function.Injective (fun i : Fin S.steps => S.degreeExponent i.castSucc) := by
  have hs : StrictMono S.degreeExponent := Fin.strictMono_iff_lt_succ.mpr fun i =>
    shrink_increases_degree (S.shrink i)
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin (S.steps + 1) => q.val) (hs.injective h))

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type} [CommRing R] [Fintype R] (κ : B.Entry → R) (hκ : B.IsSolution κ)

local notation "Hpos" => Nat.two_pow_pos S.expanderExponent
local notation "Hconn" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "SolS" => And.left (Iff.mp (B.solution_iff κ) hκ)
local notation "SolR" => And.right (Iff.mp (B.solution_iff κ) hκ)

/-- The exact posted writers give one uniform evaluator for the two kinds of phase. -/
theorem scheduleKernels_poly
    (hs : ∀ i : Fin S.steps, ShrinkKernelProgram B.shrink (S.shrink i)) :
    ∃ (shrink : ℕ × ShrinkKIn → Label R) (refresh : RefreshKIn → Label R),
      Poly shrink ∧ Poly refresh ∧ ScheduleKernelsOK B κ hκ
        ⟨fun a _ input => (shrink (a, input)).val, fun input => (refresh input).val⟩ := by
  classical
  have shr i := shrinkKernel_poly B.shrink (S.shrink i) (κ ∘ Sum.inl) SolS (hs i)
  choose ev hPoly hval using shr
  obtain ⟨rev, hrp, hrval⟩ := refreshKernel_poly S.graph Hpos Hconn B.refresh S.port_order
    S.degree_bounds.2 (κ ∘ Sum.inr) SolR
    (P1ProgEng.refreshKernelProgram S.graph Hpos Hconn B.refresh S.port_order S.degree_bounds.2)
  let table := List.ofFn fun i : Fin S.steps => (S.degreeExponent i.castSucc, ev i)
  let eval := dispatchKernel (⟨0⟩ : Label R) table
  have hn : (table.map Prod.fst).Nodup := by
    simp only [table, List.map_ofFn, Function.comp_def]
    exact List.nodup_ofFn_ofInjective (schedule_exp_injective S)
  have allPoly : ∀ q ∈ table, Poly q.2 := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hPoly i
  refine ⟨eval, rev, dispatchKernel_poly _ table allPoly, hrp, ?_⟩
  constructor
  · intro i g X s x j l p t pa z ps pad hp hpad
    have hm : (S.degreeExponent i.castSucc, ev i) ∈ table := List.mem_ofFn.mpr ⟨i, rfl⟩
    have hw := dispatchKernel_on (⟨0⟩ : Label R) table hn hm
      (paddedShrinkInput B.shrink (S.shrink i) X s x j l ps z pad)
    have hv := hval i g X s x j l pa z ps pad hp hpad
    exact (congrArg Label.val hw).trans hv
  · exact hrval

end

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.scheduleKernels_poly
