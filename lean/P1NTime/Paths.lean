import C1Challenge.NTimeGuards

namespace P1NTime.AstraNTime

open C1Challenge C1Challenge.NTimeGuards

abbrev Conf (M : NMachine) := Cfg M.K M.Γ M.Q

theorem reach_add (M : NMachine) (s t : ℕ) (c d : Conf M) :
    M.Reach c (s + t) d ↔ ∃ a, M.Reach c s a ∧ M.Reach a t d := by
  induction s generalizing c with
  | zero =>
    rw [Nat.zero_add]
    constructor
    · intro h
      exact ⟨c, rfl, h⟩
    · rintro ⟨a, ha, h⟩
      change a = c at ha
      rwa [ha] at h
  | succ s ih =>
    rw [Nat.succ_add]
    change (∃ e, M.Next c e ∧ M.Reach e (s + t) d) ↔
      ∃ a, (∃ e, M.Next c e ∧ M.Reach e s a) ∧ M.Reach a t d
    constructor
    · rintro ⟨e, he, h⟩
      obtain ⟨a, ha, hd⟩ := (ih e).mp h
      exact ⟨a, ⟨e, he, ha⟩, hd⟩
    · rintro ⟨a, ⟨e, he, ha⟩, hd⟩
      exact ⟨e, he, (ih e).mpr ⟨a, ha, hd⟩⟩

theorem noNext_of_halted {M : NMachine} {c d : Conf M} (hh : M.Halted c) : ¬ M.Next c d := by
  rintro ⟨out, hout, _⟩
  change M.code c.q (M.scanned c) = [] at hh
  rw [hh] at hout
  cases hout

/-- A clock for all paths from a configuration and the language of its accepting paths. -/
structure Outcome (M : NMachine) (c : Conf M) (T : ℕ) (p : Prop) : Prop where
  bound : ∀ {t d}, M.Reach c t d → t ≤ T
  accepts : (∃ t d, M.Reach c t d ∧ M.Halted d ∧ M.accept d.q = true) ↔ p

namespace Outcome

variable {M : NMachine} {c : Conf M} {T U : ℕ} {p q : Prop}

theorem mono (h : Outcome M c T p) (hle : T ≤ U) : Outcome M c U p :=
  ⟨fun hr => (h.bound hr).trans hle, h.accepts⟩

theorem congr (h : Outcome M c T p) (hpq : p ↔ q) : Outcome M c T q :=
  ⟨h.bound, h.accepts.trans hpq⟩

theorem halt (hh : M.Halted c) : Outcome M c 0 (M.accept c.q = true) := by
  constructor
  · intro t d hr
    cases t with
    | zero => exact le_rfl
    | succ t =>
      obtain ⟨e, he, _⟩ := hr
      exact (noNext_of_halted hh he).elim
  · constructor
    · rintro ⟨t, d, hr, _, ha⟩
      cases t with
      | zero =>
        change d = c at hr
        rwa [hr] at ha
      | succ t =>
        obtain ⟨e, he, _⟩ := hr
        exact (noNext_of_halted hh he).elim
    · intro ha
      exact ⟨0, c, rfl, hh, ha⟩

theorem choice {P : Conf M → Prop} (hne : ∃ d, M.Next c d)
    (hs : ∀ d, M.Next c d → Outcome M d T (P d)) :
    Outcome M c (T + 1) (∃ d, M.Next c d ∧ P d) := by
  constructor
  · intro t d hr
    cases t with
    | zero => exact Nat.zero_le _
    | succ t =>
      obtain ⟨e, he, h⟩ := hr
      exact Nat.succ_le_succ ((hs e he).bound h)
  · constructor
    · rintro ⟨t, d, hr, hh, ha⟩
      cases t with
      | zero =>
        change d = c at hr
        subst d
        obtain ⟨e, he⟩ := hne
        exact (noNext_of_halted hh he).elim
      | succ t =>
        obtain ⟨e, he, h⟩ := hr
        exact ⟨e, he, (hs e he).accepts.mp ⟨t, d, h, hh, ha⟩⟩
    · rintro ⟨e, he, hp⟩
      obtain ⟨t, d, h, hh, ha⟩ := (hs e he).accepts.mpr hp
      exact ⟨t + 1, d, ⟨e, he, h⟩, hh, ha⟩

theorem step {e : Conf M} (hn : ∀ d, M.Next c d ↔ d = e) (h : Outcome M e T p) :
    Outcome M c (T + 1) p := by
  have he := (hn e).mpr rfl
  apply (choice (P := fun _ => p) ⟨e, he⟩ (fun d hd => (hn d).mp hd ▸ h)).congr
  exact ⟨fun ⟨_, _, hp⟩ => hp, fun hp => ⟨e, he, hp⟩⟩

end Outcome

theorem outcome_of_halts {V : Machine} {x : List Bool} {b : Bool} {T : ℕ}
    (h : HaltsWithin V x b T) : Outcome (toN V) ((toN V).init x) T (b = true) := by
  obtain ⟨s, hsT, a, hs, hh, ha⟩ := h
  constructor
  · intro t d hr
    by_contra! high
    have hr' := (reach_toN V t (V.init x) d).mp hr
    have ht : t = s + 1 + (t - (s + 1)) := by omega
    rw [ht, run_after_halt V hs hh] at hr'
    cases hr'
  · constructor
    · rintro ⟨t, d, hr, hd, hb⟩
      exact halts_unique V ⟨s, hsT, a, hs, hh, ha⟩
        ⟨t, le_rfl, d, (reach_toN V t _ _).mp hr, (halted_toN V d).mp hd, hb⟩
    · intro hb
      exact ⟨s, a, (reach_toN V s _ _).mpr hs, (halted_toN V a).mpr hh, ha.trans hb⟩

theorem ntime_of_outcomes {L : List Bool → Bool} (M : NMachine) (C : ℕ)
    (h : ∀ x : List Bool, Outcome M (M.init x) (C * (x.length + 1)) (L x = true)) :
    NTIMEIn L (fun n => (n : ℝ)) := by
  refine ⟨M, (C : ℝ), fun x => ⟨C * (x.length + 1), ?_, ?_, (h x).accepts.symm⟩⟩
  · simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, le_refl]
  · intro d hr
    have hle := (h x).bound hr
    omega

end P1NTime.AstraNTime

#print axioms P1NTime.AstraNTime.ntime_of_outcomes
