import P1C1U.Resolve
import P1C1U.DisplayLower
import P1Case1.CoTransDone

namespace P1C1U.AstraC1U

open C1Challenge P1Case1
open OAI.Computability.MultitapeWeakETH (Word PriceTwo)

noncomputable def transLang (x : List Bool) : Bool := !coTRANS x

theorem trans_upper : coNTIMELinLog transLang := by
  apply (C1UGuards.coNTIMELinLog_iff _).2
  simpa only [transLang, Bool.not_not] using P1Case1.ntime_coTRANS

def squareInput {N : ℕ} (x y : Word (N * N)) : List Bool := List.ofFn x ++ List.ofFn y

theorem square_length {N : ℕ} (x y : Word (N * N)) :
    (squareInput x y).length = 2 * N * N := by
  simp only [squareInput, List.length_append, List.length_ofFn]
  ring

theorem square_iff {N : ℕ} (x y : Word (N * N)) :
    transLang (squareInput x y) = true ↔ y = transposeWord x := by
  have h : squareInput x y = transEncode (Display.matOf x) (Display.matOf y) := by
    simp only [squareInput, transEncode, Display.rowMajor_matOf]
  rw [h, transLang, coTRANS_transEncode, Bool.not_not]
  exact Display.transAnswer_matOf x y

def Accepts (M : NMachine) (z : List Bool) : Prop :=
  ∃ t c, M.Reach (M.init z) t c ∧ M.Halted c ∧ M.accept c.q = true

theorem accepts_iff (M : NMachine) (z : List Bool) : Accepts M z ↔ Nonempty (M.AccComp z) := by
  constructor
  · rintro ⟨t, d, h, hh, ha⟩
    obtain ⟨os, hs, _, hd⟩ := C1UGuards.reach_run M t _ d h
    exact ⟨⟨os, hs, hd.symm ▸ hh, hd.symm ▸ ha⟩⟩
  · rintro ⟨a⟩
    exact ⟨a.val.length, _, C1UGuards.run_reach M a.val _ a.property.1, a.property.2⟩

/-- Completeness uses one short accepting computation. Soundness covers every accepting computation. -/
def RecognizesTrans (M : NMachine) (N T : ℕ) : Prop :=
  ∀ x : Word (N * N),
    (∃ s : M.AccComp (squareInput x (transposeWord x)), s.val.length ≤ T) ∧
    ∀ y : Word (N * N), M.AccComp (squareInput x y) → y = transposeWord x

theorem recognizes_of_clock (M : NMachine) (C : ℝ) (f : ℕ → ℝ)
    (hM : ∀ z, ∃ T : ℕ, (T : ℝ) ≤ C * (f z.length + 1) ∧
      (∀ d, ¬ M.Reach (M.init z) (T + 1) d) ∧ (transLang z = true ↔ Accepts M z))
    (N : ℕ) : RecognizesTrans M N ⌊C * (f (2 * N * N) + 1)⌋₊ := by
  intro x
  constructor
  · obtain ⟨T, hT, hbound, hspec⟩ := hM (squareInput x (transposeWord x))
    obtain ⟨s⟩ := (accepts_iff M _).mp (hspec.mp ((square_iff x _).mpr rfl))
    rw [square_length] at hT
    exact ⟨s, (acc_length_le hbound s).trans (Nat.le_floor hT)⟩
  · intro y s
    obtain ⟨_, _, _, hspec⟩ := hM (squareInput x y)
    exact (square_iff x y).mp (hspec.mpr ((accepts_iff M _).mpr ⟨s⟩))

/-- The machine construction needed for Case A. Its overhead is uniform in the side and the clock. -/
def DisplaySimulation : Prop :=
  ∀ M : NMachine, ∃ (D : OAI.Computability.MultitapeWeakETH.Machine) (a : ℕ), ∀ N T : ℕ,
    RecognizesTrans M N T → Displays D N (T + a * (N * N + 1))

theorem caseA_of_displaySimulation (sim : DisplaySimulation) (price : PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  refine ⟨1/4, by norm_num, transLang, trans_upper, ?_⟩
  rintro ⟨M, C, hM⟩
  obtain ⟨D, a, disp⟩ := sim M
  obtain ⟨c, hc, N₀, lower⟩ := lower_of_displays price D a
  obtain ⟨N, hN, gap⟩ := exists_gap c C hc N₀
  let f : ℕ → ℝ := fun n => (n : ℝ) * Real.logb 2 n ^ (1/4 : ℝ)
  have recN := recognizes_of_clock M C f hM N
  have hlow := lower N hN _ (disp N _ recN)
  let zeroWord : Word (N * N) := fun _ => false
  obtain ⟨T, ht, _, _⟩ := hM (squareInput zeroWord zeroWord)
  rw [square_length] at ht
  have hpos : 0 ≤ C * (f (2 * N * N) + 1) := (Nat.cast_nonneg T).trans ht
  exact (not_le_of_gt gap) (hlow.trans (Nat.floor_le hpos))

end P1C1U.AstraC1U

#print axioms P1C1U.AstraC1U.caseA_of_displaySimulation
