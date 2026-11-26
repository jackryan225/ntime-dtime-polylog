import P1C1U.Resolve
import P1Case1.Display

namespace P1C1U.AstraC1U.Physical

open C1Challenge P1Case1
open OAI.Computability.IntegerMultiplication
open OAI.Computability.MultitapeWeakETH (Word initial run writes)

noncomputable section

abbrev model (M : NMachine) (p : Choice M) := toOAI (resolve M p)
abbrev PCfg (M : NMachine) := Display.Cf (model M none)
abbrev Coin (M : NMachine) := Bool × Choice M

@[reducible] def machine (M : NMachine) : OAI.Computability.MultitapeWeakETH.Machine :=
  { Display.machine (model M none) with
    Choice := Coin M
    choiceFintype := Fintype.ofFinite _
    choiceNonempty := ⟨(false, none)⟩
    rule := fun p => Display.rule (model M p.2) p.1 }

abbrev bits {M : NMachine} (cs : ℕ → Coin M) (i : ℕ) : Bool := (cs i).1

abbrev path (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M) (t : ℕ) :
    Option (PCfg M) := run (machine M) cs (initial (machine M) x y) t

abbrev Agree (M : NMachine) (n : ℕ) (b : ℕ → Bool) (d : PCfg M) (c : Conf M) : Prop :=
  Display.Agrees (model M none) (n := n) b d (cfgOAI (resolve M none) c)

theorem prefix_advance (M : NMachine) (d : PCfg M) (b : Bool) (hd : d.pc = .inl b)
    (p : Coin M) : TM.advance ((machine M).rule p) d =
      TM.advance (Display.rule (model M none) p.1) d := by
  unfold TM.advance
  rw [hd] <;> cases b <;> rfl

theorem prefix_eq (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M) (t : ℕ)
    (ht : t ≤ 3 * n + 2) :
    path M x y cs t = run (Display.machine (model M none)) (bits cs)
      (initial (Display.machine (model M none)) x y) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨d, hd, b, hb⟩ := Display.prefix_states (model M none) x y (bits cs) t (by omega)
    change (path M x y cs t).bind _ =
      (run (Display.machine (model M none)) (bits cs)
        (initial (Display.machine (model M none)) x y) t).bind _
    rw [ih (by omega), hd]
    exact prefix_advance M d b hb (cs t)

theorem prefix_run (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M) :
    ∃ d, path M x y cs (3 * n + 2) = some d ∧
      Agree M n (bits cs) d (M.init (List.ofFn x ++ List.ofFn (fun j : Fin n => bits cs j.val))) := by
  obtain ⟨d, hd, hag⟩ := Display.prefix_run (model M none) x y (bits cs)
  exact ⟨d, (prefix_eq M x y cs _ le_rfl).trans hd, hag⟩

theorem after_prefix_of_accept (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M)
    {t : ℕ} {d : PCfg M} (hd : path M x y cs t = some d)
    (ha : (machine M).accepts d.pc = true) : 3 * n + 2 ≤ t := by
  by_contra! hlt
  obtain ⟨d', hd', b, hb⟩ := Display.prefix_states (model M none) x y (bits cs) t hlt
  have he : d = d' := Option.some.inj (hd.symm.trans ((prefix_eq M x y cs t hlt.le).trans hd'))
  subst d'
  rw [hb] at ha
  exact Bool.false_ne_true ha

private theorem pull_rel {α β γ : Type*} {R : α → γ → Prop} (f : β → γ)
    (a : Option α) (b : Option β) (h : Option.Rel R a (b.map f)) :
    Option.Rel (fun x y => R x (f y)) a b := by
  cases a <;> cases b <;> cases h <;> constructor <;> assumption

theorem step_rel (M : NMachine) {n : ℕ} (b : ℕ → Bool) {d : PCfg M} {c : Conf M}
    (ag : Agree M n b d c) (p : Coin M) :
    Option.Rel (Agree M n b) (TM.advance ((machine M).rule p) d) ((resolve M p.2).step c) := by
  have h := Display.step_agrees (model M p.2) (n := n) b (c := cfgOAI (resolve M p.2) c)
    (cfg := d) ag p.1
  rw [step_cfgOAI] at h
  exact pull_rel (cfgOAI (resolve M p.2)) _ _ h

private theorem rel_halt {α β : Type*} {R : α → β → Prop} {a : Option α} {b : Option β}
    (h : Option.Rel R a b) : a = none ↔ b = none := by cases h <;> simp

private theorem rel_right {α β : Type*} {R : α → β → Prop} {a : Option α} {v : β}
    (h : Option.Rel R a (some v)) : ∃ u, a = some u ∧ R u v := by
  cases h with
  | some hv => exact ⟨_, rfl, hv⟩

private theorem rel_left {α β : Type*} {R : α → β → Prop} {a : Option α} {b : Option β} {u : α}
    (h : Option.Rel R a b) (ha : a = some u) : ∃ v, b = some v ∧ R u v := by
  subst a
  cases h with
  | some hu => exact ⟨_, rfl, hu⟩

theorem halt_iff (M : NMachine) {n : ℕ} {b : ℕ → Bool} {d : PCfg M} {c : Conf M}
    (ag : Agree M n b d c) (p : Coin M) :
    TM.advance ((machine M).rule p) d = none ↔ M.Halted c :=
  (rel_halt (step_rel M b ag p)).trans (resolve_halt M p.2 c)

theorem forward_step (M : NMachine) {n : ℕ} {b : ℕ → Bool} {d : PCfg M} {c c' : Conf M}
    (ag : Agree M n b d c) (p : Coin M) (hc : (resolve M p.2).step c = some c') :
    ∃ d', TM.advance ((machine M).rule p) d = some d' ∧ Agree M n b d' c' := by
  have h := step_rel M b ag p
  rw [hc] at h
  exact rel_right h

theorem backward_step (M : NMachine) {n : ℕ} {b : ℕ → Bool} {d d' : PCfg M} {c : Conf M}
    (ag : Agree M n b d c) (p : Coin M) (hd : TM.advance ((machine M).rule p) d = some d') :
    ∃ c', M.Next c c' ∧ Agree M n b d' c' := by
  obtain ⟨c', hc, hrel⟩ := rel_left (step_rel M b ag p) hd
  exact ⟨c', next_of_resolve (M := M) (p := p.2) hc, hrel⟩

theorem answer (M : NMachine) {n : ℕ} {b : ℕ → Bool} {d : PCfg M} {c : Conf M}
    (ag : Agree M n b d c) : (machine M).accepts d.pc = M.accept c.q := by
  rw [ag.1]
  rfl

theorem written (M : NMachine) {n : ℕ} {b : ℕ → Bool} {d : PCfg M} {c : Conf M}
    (ag : Agree M n b d c) : writes (machine M) d (fun i : Fin n => b i.val) := by
  intro i
  have hi : (i.val : ℤ) < (n : ℤ) := by exact_mod_cast i.isLt
  have h := ag.2.2.2 ((n : ℤ) + i.val)
  have hz : (n : ℤ) ≤ (n : ℤ) + i.val ∧ (n : ℤ) + i.val < 2 * n := by omega
  have hz' : ((n : ℤ) + i.val - n).toNat = i.val := by omega
  change (d.tape none).absolute ((n : ℤ) + i.val) = Display.bitS (model M none) (b i.val)
  simpa only [Display.outCell, if_pos hz, hz'] using h

end
end P1C1U.AstraC1U.Physical

#print axioms P1C1U.AstraC1U.Physical.step_rel
