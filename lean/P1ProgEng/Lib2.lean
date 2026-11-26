import P1ProgEng.Lib
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold

/-!
# P1ProgEng.Lib2: generic facts about OpenAI's `Prog.Run` (owner P1-lean-progeng)

* `run_weaken`: a run in scope `Δ` is a run in scope `Δ ++ Γ` (so a run in scope `[]` works in every scope);
* `liftP`, `run_lift`: change of alphabet along `f : A → B` with a left inverse `g` on looked-up letters;
* `Below N p` (all registers of `p` are `< N`), `run_frame` (registers `≥ N` are untouched),
  `exists_below` (every program over a finite alphabet has such an `N`);
* `run_length_le`: a register grows by at most the cost.
-/

namespace P1ProgEng

open OAI.Computability.IntegerMultiplication

section

variable {A B : Type}

/-! ### Scope weakening -/

theorem run_weaken {Δ : Scope A} {p : Prog A} {r : Reg A} {n : ℕ} {s : Reg A}
    (h : Prog.Run Δ p r n s) (Γ : Scope A) : Prog.Run (Δ ++ Γ) p r n s := by
  induction h with
  | pass => exact .pass
  | push => exact .push
  | pop => exact .pop
  | look _ ih => exact .look ih
  | join _ _ ih1 ih2 => exact .join ih1 ih2
  | tie _ ih => exact .tie ih
  | @again Δ i c r n r' hget _ ih =>
    have hi : i < Δ.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
    refine .again (c := c) ?_ ?_
    · rw [List.getElem?_append_left hi]; exact hget
    · rw [List.drop_append_of_le_length hi.le]; exact ih

theorem run_of_nil {p : Prog A} {r : Reg A} {n : ℕ} {s : Reg A}
    (h : Prog.Run [] p r n s) (Γ : Scope A) : Prog.Run Γ p r n s := run_weaken h Γ

/-! ### Change of alphabet -/

/-- Lift a program along `f : A → B`; looked-up letters are read back with `g`. -/
def liftP (f : A → B) (g : Option B → Option A) : Prog A → Prog B
  | .pass => .pass
  | .push i x => .push i (f x)
  | .pop i => .pop i
  | .look i c => .look i fun o => liftP f g (c (g o))
  | .join c d => .join (liftP f g c) (liftP f g d)
  | .tie c => .tie (liftP f g c)
  | .again k => .again k

/-- Lift the registers along `f`. -/
def liftR (f : A → B) (r : Reg A) : Reg B := fun i => (r i).map f

theorem liftR_update (f : A → B) (r : Reg A) (i : ℕ) (l : List A) :
    liftR f (Function.update r i l) = Function.update (liftR f r) i (l.map f) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [liftR]
  · simp [liftR, Function.update_of_ne hj]

theorem run_lift (f : A → B) (g : Option B → Option A) (hg : ∀ o : Option A, g (o.map f) = o)
    {Γ : Scope A} {p : Prog A} {r : Reg A} {n : ℕ} {s : Reg A} (h : Prog.Run Γ p r n s) :
    Prog.Run (Γ.map (liftP f g)) (liftP f g p) (liftR f r) n (liftR f s) := by
  induction h with
  | pass => exact .pass
  | @push Γ i x r =>
    rw [liftR_update]
    exact .push
  | @pop Γ i r =>
    rw [liftR_update, List.map_tail]
    exact .pop
  | @look Γ i c r n r' _ ih =>
    refine .look ?_
    have : g (liftR f r i).head? = (r i).head? := by simp only [liftR, List.head?_map, hg]
    show Prog.Run _ (liftP f g (c (g (liftR f r i).head?))) _ _ _
    rw [this]; exact ih
  | join _ _ ih1 ih2 => exact .join ih1 ih2
  | tie _ ih => exact .tie ih
  | @again Γ i c r n r' hget _ ih =>
    refine .again (c := liftP f g c) ?_ ?_
    · rw [List.getElem?_map, hget]; rfl
    · rw [← List.map_drop]; exact ih

/-! ### Registers touched by a program -/

/-- All registers used by `p` are `< N`. -/
def Below (N : ℕ) : Prog A → Prop
  | .pass => True
  | .push i _ => i < N
  | .pop i => i < N
  | .look i c => i < N ∧ ∀ o, Below N (c o)
  | .join c d => Below N c ∧ Below N d
  | .tie c => Below N c
  | .again _ => True

theorem below_mono {N M : ℕ} (hNM : N ≤ M) {p : Prog A} (h : Below N p) : Below M p := by
  induction p with
  | pass => trivial
  | push _ _ => exact lt_of_lt_of_le h hNM
  | pop _ => exact lt_of_lt_of_le h hNM
  | look _ c ih => exact ⟨lt_of_lt_of_le h.1 hNM, fun o => ih o (h.2 o)⟩
  | join _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | tie _ ih => exact ih h
  | again _ => trivial

theorem exists_below [Fintype A] : ∀ p : Prog A, ∃ N, Below N p
  | .pass => ⟨0, trivial⟩
  | .push i _ => ⟨i + 1, Nat.lt_succ_self i⟩
  | .pop i => ⟨i + 1, Nat.lt_succ_self i⟩
  | .look i c => by
    choose N hN using fun o => exists_below (c o)
    refine ⟨max (i + 1) (Finset.univ.sup N), lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _),
      fun o => below_mono ?_ (hN o)⟩
    exact (Finset.le_sup (Finset.mem_univ o)).trans (le_max_right _ _)
  | .join c d => by
    obtain ⟨N₁, h₁⟩ := exists_below c
    obtain ⟨N₂, h₂⟩ := exists_below d
    exact ⟨max N₁ N₂, below_mono (le_max_left _ _) h₁, below_mono (le_max_right _ _) h₂⟩
  | .tie c => exists_below c
  | .again _ => ⟨0, trivial⟩

theorem run_frame {N : ℕ} {Γ : Scope A} {p : Prog A} {r : Reg A} {n : ℕ} {s : Reg A}
    (h : Prog.Run Γ p r n s) : (∀ q ∈ Γ, Below N q) → Below N p → ∀ l, N ≤ l → s l = r l := by
  induction h with
  | pass => intro _ _ l _; rfl
  | @push Γ i x r =>
    intro _ hp l hl
    have : l ≠ i := by simp only [Below] at hp; omega
    simp [Function.update_of_ne this]
  | @pop Γ i r =>
    intro _ hp l hl
    have : l ≠ i := by simp only [Below] at hp; omega
    simp [Function.update_of_ne this]
  | @look Γ i c r n r' _ ih =>
    intro hΓ hp l hl
    exact ih hΓ (hp.2 _) l hl
  | join _ _ ih1 ih2 =>
    intro hΓ hp l hl
    rw [ih2 hΓ hp.2 l hl, ih1 hΓ hp.1 l hl]
  | @tie Γ c r n r' _ ih =>
    intro hΓ hp l hl
    refine ih ?_ hp l hl
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact hΓ q hq
  | @again Γ i c r n r' hget _ ih =>
    intro hΓ _ l hl
    refine ih (fun q hq => hΓ q (List.mem_of_mem_drop hq)) (hΓ c (List.mem_of_getElem? hget)) l hl

theorem run_length_le {Γ : Scope A} {p : Prog A} {r : Reg A} {n : ℕ} {s : Reg A}
    (h : Prog.Run Γ p r n s) : ∀ l, (s l).length ≤ (r l).length + n := by
  induction h with
  | pass => intro l; omega
  | @push Γ i x r =>
    intro l
    by_cases hl : l = i
    · subst hl; simp only [Function.update_self, List.length_cons]; omega
    · simp only [Function.update_of_ne hl]; omega
  | @pop Γ i r =>
    intro l
    by_cases hl : l = i
    · subst hl; simp only [Function.update_self, List.length_tail]; omega
    · simp only [Function.update_of_ne hl]; omega
  | look _ ih => intro l; have := ih l; omega
  | join _ _ ih1 ih2 => intro l; have := ih1 l; have := ih2 l; omega
  | tie _ ih => intro l; have := ih l; omega
  | again _ _ ih => intro l; have := ih l; omega

end

end P1ProgEng
