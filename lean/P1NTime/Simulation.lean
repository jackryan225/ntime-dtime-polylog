import P1NTime.Composite

namespace P1NTime.AstraNTime.Composite

open C1Challenge C1Challenge.NTimeGuards

abbrev NativeCfg (A : Machine) := Cfg A.K A.Γ A.Q

def nativeResult (A : Machine) (c : NativeCfg A) (o : NativeOut A) : NativeCfg A :=
  ⟨o.1, updateBank c.tapes (fun k => (o.2.1 k, o.2.2 k))⟩

theorem step_eq (A : Machine) (c : NativeCfg A) :
    A.step c = (A.code c.q (heads c.tapes)).map (nativeResult A c) := rfl

/-- Every source step has a unique successor in the composite machine. -/
theorem follow_run {A : Machine} {N : NMachine} (F : NativeCfg A → Conf N)
    (one : ∀ a b, A.step a = some b → ∀ y, N.Next (F a) y ↔ y = F b)
    {a b : NativeCfg A} {t U : ℕ} {p : Prop} (hr : (toN A).Reach a t b)
    (finish : Outcome N (F b) U p) : Outcome N (F a) (U + t) p := by
  induction t generalizing a with
  | zero =>
    change b = a at hr
    subst a
    exact finish
  | succ t ih =>
    obtain ⟨a', hstep, htail⟩ := hr
    exact Outcome.step (one a a' ((next_toN A a a').mp hstep)) (ih (a := a') htail)

theorem follow_halts {A : Machine} {N : NMachine} (F : NativeCfg A → Conf N)
    (one : ∀ a b, A.step a = some b → ∀ y, N.Next (F a) y ↔ y = F b)
    {x : List Bool} {b : Bool} {T U : ℕ} {p : Prop} (h : HaltsWithin A x b T)
    (finish : ∀ c, A.step c = none → A.accept c.q = b → Outcome N (F c) U p) :
    Outcome N (F (A.init x)) (U + T) p := by
  obtain ⟨t, ht, c, hrun, hhalt, hacc⟩ := h
  have path := (reach_toN A t (A.init x) c).mpr hrun
  exact (follow_run F one path (finish c hhalt hacc)).mono (Nat.add_le_add_left ht U)

variable (D V : Machine) (src : Turing.Tape (Sym D V))

noncomputable def inCheck (v : Tapes V) (c : NativeCfg D) : Conf (machine D V) :=
  pack D V (.inr (.inl c.q)) src c.tapes v

noncomputable def inVerify (d : Tapes D) (c : NativeCfg V) : Conf (machine D V) :=
  pack D V (.inr (.inr c.q)) src d c.tapes

theorem next_check (v : Tapes V) (a b : NativeCfg D) (hs : D.step a = some b)
    (y : Conf (machine D V)) :
    (machine D V).Next (inCheck D V src v a) y ↔ y = inCheck D V src v b := by
  rw [step_eq] at hs
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hi : program D V (.inr (.inl a.q)) src.head (heads a.tapes) (heads v) =
      [checkInstr D V src.head (heads v) o] := by simp only [program, ho]
  simpa only [inCheck, result, checkInstr, act_hold, update_hold, nativeResult] using
    next_one D V _ src a.tapes v hi y

theorem next_verify (d : Tapes D) (a b : NativeCfg V) (hs : V.step a = some b)
    (y : Conf (machine D V)) :
    (machine D V).Next (inVerify D V src d a) y ↔ y = inVerify D V src d b := by
  rw [step_eq] at hs
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hi : program D V (.inr (.inr a.q)) src.head (heads d) (heads a.tapes) =
      [verifyInstr D V src.head (heads d) o] := by simp only [program, ho]
  simpa only [inVerify, result, verifyInstr, act_hold, update_hold, nativeResult] using
    next_one D V _ src d a.tapes hi y

theorem code_none (A : Machine) (c : NativeCfg A) (h : A.step c = none) :
    A.code c.q (heads c.tapes) = none := by
  rw [step_eq] at h
  exact Option.map_eq_none_iff.mp h

theorem verify_outcome (d : Tapes D) {z : List Bool} {b : Bool} {T : ℕ}
    (h : HaltsWithin V z b T) :
    Outcome (machine D V) (inVerify D V src d (V.init z)) T (b = true) := by
  have finish (c : NativeCfg V) (hh : V.step c = none) (hb : V.accept c.q = b) :
      Outcome (machine D V) (inVerify D V src d c) 0 (b = true) := by
    have stop := halted_empty D V (.inr (.inr c.q)) src d c.tapes
      (by simp only [program, code_none V c hh])
    apply (Outcome.halt stop).congr
    change (V.accept c.q = true) ↔ b = true
    rw [hb]
  simpa only [Nat.zero_add] using
    follow_halts (inVerify D V src d) (next_verify D V src d) h finish

/-- A rejected candidate halts in the checker. An accepted candidate takes one
    transition to the initial state of the verifier. -/
theorem check_outcome (v : Tapes V) {z : List Bool} {b : Bool} {T U : ℕ} {p : Prop}
    (h : HaltsWithin D z b T)
    (pass : b = true → ∀ d : Tapes D,
      Outcome (machine D V) (inVerify D V src d ⟨V.initialState, v⟩) U p) :
    Outcome (machine D V) (inCheck D V src v (D.init z)) (U + 1 + T) (b = true ∧ p) := by
  apply follow_halts (inCheck D V src v) (next_check D V src v) h
  intro c hh hb
  have hc := code_none D c hh
  cases b with
  | false =>
    have stop := halted_empty D V (.inr (.inl c.q)) src c.tapes v (by simp [program, hc, hb])
    apply ((Outcome.halt stop).mono (Nat.zero_le (U + 1))).congr
    change (false = true) ↔ false = true ∧ p
    simp
  | true =>
    have hi : program D V (.inr (.inl c.q)) src.head (heads c.tapes) (heads v) =
        [idle D V (.inr (.inr V.initialState)) (src.head, .stay) (heads c.tapes) (heads v)] := by
      simp [program, hc, hb]
    have hn (y : Conf (machine D V)) :
        (machine D V).Next (inCheck D V src v c) y ↔
          y = inVerify D V src c.tapes ⟨V.initialState, v⟩ := by
      simpa only [inCheck, inVerify, result, idle, act_hold, update_hold] using
        next_one D V _ src c.tapes v hi y
    exact (Outcome.step hn (pass rfl c.tapes)).congr (by simp)

end P1NTime.AstraNTime.Composite

#print axioms P1NTime.AstraNTime.Composite.check_outcome
