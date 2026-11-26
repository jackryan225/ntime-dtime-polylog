import C1Challenge.C1UGuards
import P1NTime.Paths

namespace P1C1U.AstraC1U

open C1Challenge

abbrev Conf (M : NMachine) := Cfg M.K M.Γ M.Q
abbrev Out (M : NMachine) := M.Q × (M.K → M.Γ) × (M.K → HeadMove)
abbrev Choice (M : NMachine) := Option (Out M)

open Classical in
noncomputable def pick {α : Type*} (xs : List α) : Option α → Option α
  | none => xs.head?
  | some a => if a ∈ xs then some a else xs.head?

private theorem head_mem {α : Type*} {xs : List α} {a : α} (h : xs.head? = some a) :
    a ∈ xs := by
  cases xs with
  | nil => cases h
  | cons b bs =>
    have hb : b = a := Option.some.inj h
    subst a
    exact List.Mem.head _

theorem pick_mem {α : Type*} {xs : List α} {p : Option α} {a : α}
    (h : pick xs p = some a) : a ∈ xs := by
  classical
  cases p with
  | none => exact head_mem h
  | some b =>
    by_cases hb : b ∈ xs
    · rw [pick, if_pos hb] at h
      exact (Option.some.inj h) ▸ hb
    · rw [pick, if_neg hb] at h
      exact head_mem h

theorem pick_of_mem {α : Type*} {xs : List α} {a : α} (ha : a ∈ xs) :
    pick xs (some a) = some a := by
  classical
  simp only [pick, if_pos ha]

theorem pick_none_iff {α : Type*} (xs : List α) (p : Option α) :
    pick xs p = none ↔ xs = [] := by
  classical
  cases xs with
  | nil => cases p <;> simp [pick]
  | cons b bs =>
    cases p with
    | none => simp [pick]
    | some a =>
      by_cases ha : a ∈ b :: bs <;> simp [pick, ha]

/-- A choice requests a transition. An unavailable request uses the first available transition.
This preserves the halting predicate for every choice. -/
@[reducible] noncomputable def resolve (M : NMachine) (p : Choice M) : Machine where
  K := M.K
  tapeFinite := M.tapeFinite
  tapeDecidableEq := M.tapeDecidableEq
  inputTape := M.inputTape
  Γ := M.Γ
  alphabetInhabited := M.alphabetInhabited
  alphabetFinite := M.alphabetFinite
  Q := M.Q
  stateFinite := M.stateFinite
  initialState := M.initialState
  inputSymbol := M.inputSymbol
  input_injective := M.input_injective
  input_ne_blank := M.input_ne_blank
  code := fun q r => pick (M.code q r) p
  accept := M.accept

theorem resolve_step (M : NMachine) (p : Choice M) (c : Conf M) :
    (resolve M p).step c = (pick (M.code c.q (M.scanned c)) p).map (M.apply c) := rfl

theorem resolve_halt (M : NMachine) (p : Choice M) (c : Conf M) :
    (resolve M p).step c = none ↔ M.Halted c := by
  change (pick (M.code c.q (M.scanned c)) p).map (M.apply c) = (none : Option (Conf M)) ↔
    M.code c.q (M.scanned c) = []
  exact Option.map_eq_none_iff.trans (pick_none_iff _ _)

theorem next_of_resolve {M : NMachine} {p : Choice M} {c d : Conf M}
    (h : (resolve M p).step c = some d) : M.Next c d := by
  rw [resolve_step] at h
  obtain ⟨o, hp, hd⟩ := Option.map_eq_some_iff.mp h
  exact ⟨o, pick_mem hp, hd⟩

theorem resolve_of_mem {M : NMachine} {c : Conf M} {o : Out M}
    (h : o ∈ M.code c.q (M.scanned c)) :
    (resolve M (some o)).step c = some (M.apply c o) := by
  change (pick (M.code c.q (M.scanned c)) (some o)).map (M.apply c) = some (M.apply c o)
  simp only [pick_of_mem h, Option.map_some]

theorem reach_length_le {M : NMachine} {c d : Conf M} {t T : ℕ}
    (bound : ∀ e, ¬ M.Reach c (T + 1) e) (h : M.Reach c t d) : t ≤ T := by
  by_contra! hlt
  have ht : t = (T + 1) + (t - (T + 1)) := by omega
  rw [ht, P1NTime.AstraNTime.reach_add] at h
  obtain ⟨e, he, _⟩ := h
  exact bound e he

theorem acc_length_le {M : NMachine} {x : List Bool} {T : ℕ}
    (bound : ∀ e, ¬ M.Reach (M.init x) (T + 1) e) (a : M.AccComp x) :
    a.val.length ≤ T :=
  reach_length_le bound (C1UGuards.run_reach M a.val (M.init x) a.property.1)

/-- A bounded accepting path is encoded by its length and its ordered tuple of transitions. -/
theorem finite_accComp {M : NMachine} {x : List Bool} {T : ℕ}
    (bound : ∀ e, ¬ M.Reach (M.init x) (T + 1) e) : Finite (M.AccComp x) := by
  let pack (a : M.AccComp x) : Σ i : Fin (T + 1), Fin i.val → Out M :=
    ⟨⟨a.val.length, Nat.lt_succ_of_le (acc_length_le bound a)⟩, a.val.get⟩
  apply Finite.of_injective pack
  intro a b hab
  apply Subtype.ext
  have he := congrArg (fun p : (Σ i : Fin (T + 1), Fin i.val → Out M) => List.ofFn p.2) hab
  simpa only [pack, List.ofFn_get] using he

end P1C1U.AstraC1U

#print axioms P1C1U.AstraC1U.finite_accComp
