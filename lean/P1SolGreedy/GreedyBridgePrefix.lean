import P1SolGreedy.GreedyBridgeSections
import P1Int.WLinkProof

namespace P1SolGreedy.SolBridge

open OAI.Computability.VPVNP.Compression P1Wit P1Wit.SolWitfill
open private levelFrom levelFrom_head levelFrom_tail from P1Int.WLinkProof

variable {F : Type} [CommRing F] {D : Dims} {a g b n start : ℕ} {X : State a g}

/-- All level fields agree from the current depth up to the exclusive bound. -/
def readsBefore (u : List Bool) (E : StateExecution F b n X)
    (P : ExecutionPanels D E start) (T : ExecutionTerms D E start)
    (c : E.Choices) (stop : ℕ) : Prop :=
  ∀ (j : Fin (D.top + 1)) (hj : start ≤ j.val), j.val < stop →
    ∀ m : Mem, ReadsKind D u j.val (levelFrom E P T c j hj) m

variable {a' g' : ℕ} {p : StatePass F X a' g'} {tail : ∀ i, StateExecution F b n (p.next i)}
def readsHead (u : List Bool) (P : ExecutionPanels D (.more p tail) start)
    (T : ExecutionTerms D (.more p tail) start) (i : p.step.Choice) : Prop :=
  let r : LevelRecords D (D.lv start) :=
    levelRecordsOfState X (P.1.val i).fits ((P.1.val i).step (T.1.encode i))
  ∀ m : Mem, ReadsKind D u start r m

variable (u : List Bool) (P : ExecutionPanels D (.more p tail) start) (T : ExecutionTerms D (.more p tail) start)

theorem readsBefore_more (c : (StateExecution.more p tail).Choices) {stop : ℕ} (hs : start < stop) :
    readsBefore u (.more p tail) P T c stop ↔
      readsHead u P T c.1 ∧ readsBefore u (tail c.1) (P.2 c.1) (T.2 c.1) c.2 stop := by
  constructor
  · intro hc
    constructor
    · have hh := hc ⟨start, T.1.in_range⟩ le_rfl hs
      rw [levelFrom_head] at hh
      exact hh
    · intro j hj hstop
      have hh := hc j (Nat.le_of_succ_le hj) hstop
      rw [levelFrom_tail P T c j hj] at hh
      exact hh
  · rintro ⟨hhead, htail⟩ j hj hstop
    rcases Nat.eq_or_lt_of_le hj with he | hlt
    · have hindex : j = ⟨start, T.1.in_range⟩ := Fin.ext he.symm
      subst j
      rw [levelFrom_head]
      exact hhead
    · rw [levelFrom_tail P T c j hlt]
      exact htail j hlt hstop

/-- The term embedding forces every extension to enter the same child. -/
theorem exists_readsBefore_tail (i : p.step.Choice) (hi : readsHead u P T i)
    {stop : ℕ} (hs : start < stop) :
    (∃ c : (StateExecution.more p tail).Choices, readsBefore u (.more p tail) P T c stop) ↔
      ∃ z : (tail i).Choices, readsBefore u (tail i) (P.2 i) (T.2 i) z stop := by
  constructor
  · rintro ⟨⟨j, z⟩, hr⟩
    obtain ⟨hh, ht⟩ := (readsBefore_more u P T ⟨j, z⟩ hs).mp hr
    have hji : j = i := T.1.encode.injective (terms_eq_of_reads (hh .terms) (hi .terms))
    subst j
    exact ⟨z, ht⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨i, z⟩, (readsBefore_more u P T ⟨i, z⟩ hs).mpr ⟨hi, hz⟩⟩

/-- At the final tested row, any continuation of its matching choice suffices. -/
theorem exists_readsBefore_head (live : ∀ i : p.step.Choice, Nonempty (tail i).Choices) :
    (∃ c : (StateExecution.more p tail).Choices, readsBefore u (.more p tail) P T c (start + 1)) ↔
      ∃ i : p.step.Choice, readsHead u P T i := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, ((readsBefore_more u P T c (Nat.lt_succ_self start)).mp hc).1⟩
  · rintro ⟨i, hi⟩
    obtain ⟨z⟩ := live i
    refine ⟨⟨i, z⟩, (readsBefore_more u P T ⟨i, z⟩ (Nat.lt_succ_self start)).mpr ⟨hi, ?_⟩⟩
    intro j hj hstop
    exact (Nat.not_lt_of_ge hj hstop).elim

end P1SolGreedy.SolBridge

#print axioms P1SolGreedy.SolBridge.exists_readsBefore_tail
#print axioms P1SolGreedy.SolBridge.exists_readsBefore_head
