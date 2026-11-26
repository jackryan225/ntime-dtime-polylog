import C1Challenge.C1U
import C1Challenge.NTimeGuards

/-!
# Guards for the C1-U statement (C1U.lean), before any proof builds on it (P1-lean-integ, 2026-11-25)

* `coNTIMELinLog_iff`: `coNTIMELinLog L ↔ NTIMELinLog (fun x => !L x)` (it is the complement class).
* `dtime_sub_coNTIMELinLog`: DTIME(n) ⊆ coNTIME[n; 2 log n]; `coNTIME_nonconstant`: it contains `!firstBit`.
* `acc_toN`, `par_of_dtime`: a deterministic machine has exactly one accepting computation when it accepts and none when
  it rejects; so DTIME(f) ⊆ ⊕TIME(f); `par_firstBit`: ⊕TIME(n) contains a language that depends on its input.
* `acc_halt`, `par_const`: small case T = 0 (a machine with no transition): acc = 1 or 0.
* `acc_fork`: the branching machine of NTimeGuards has acc = 2 on every input (two different accepting computations), so
  it accepts in NTIME (`ntime_fork`) and rejects in ⊕TIME: `acc` counts computations and the two classes differ.
* `run_reach`, `reach_run`: computations as transition sequences are the same as `Reach`.
-/

namespace C1Challenge
namespace C1UGuards

open NTimeGuards

/-! ## Transition sequences and `Reach` -/

theorem run_reach (M : NMachine) : ∀ (os : List (M.Q × (M.K → M.Γ) × (M.K → HeadMove))) (c : Cfg M.K M.Γ M.Q),
    M.Run c os → M.Reach c os.length (M.after c os)
  | [], _, _ => rfl
  | o :: os, c, h => by
    show ∃ c₁, M.Next c c₁ ∧ M.Reach c₁ os.length (M.after (M.apply c o) os)
    exact ⟨M.apply c o, ⟨o, h.1, rfl⟩, run_reach M os (M.apply c o) h.2⟩

theorem reach_run (M : NMachine) : ∀ (t : ℕ) (c d : Cfg M.K M.Γ M.Q), M.Reach c t d →
    ∃ os, M.Run c os ∧ os.length = t ∧ M.after c os = d
  | 0, _, _, h => ⟨[], trivial, rfl, Eq.symm h⟩
  | t + 1, c, d, h => by
    obtain ⟨c₁, ⟨o, ho, hc₁⟩, h2⟩ := h
    subst hc₁
    obtain ⟨os, hs, hl, hd⟩ := reach_run M t (M.apply c o) d h2
    exact ⟨o :: os, And.intro ho hs, by simp [hl], hd⟩

theorem not_run_cons_of_halted (M : NMachine) {c : Cfg M.K M.Γ M.Q} (hh : M.Halted c)
    {o : M.Q × (M.K → M.Γ) × (M.K → HeadMove)} {os : List (M.Q × (M.K → M.Γ) × (M.K → HeadMove))} :
    ¬ M.Run c (o :: os) := by
  intro h
  have h1 : o ∈ M.code c.q (M.scanned c) := h.1
  have h2 : M.code c.q (M.scanned c) = [] := hh
  rw [h2] at h1
  cases h1

/-! ## G1: coNTIMELinLog is the complement class of NTIMELinLog -/

/-- `V` with its answers swapped. -/
def flip (V : Machine) : Machine := { V with accept := fun q => !V.accept q }

theorem haltsWithin_flip {V : Machine} {z : List Bool} {b : Bool} {T : ℕ} :
    HaltsWithin (flip V) z b T ↔ HaltsWithin V z (!b) T := by
  constructor
  · rintro ⟨t, ht, c, hc, hs, hb⟩
    refine ⟨t, ht, c, hc, hs, ?_⟩
    have hb' : (!V.accept c.q) = b := hb
    rw [← hb', Bool.not_not]
  · rintro ⟨t, ht, c, hc, hs, hb⟩
    refine ⟨t, ht, c, hc, hs, ?_⟩
    show (!V.accept c.q) = b
    rw [hb, Bool.not_not]

theorem coNTIMELinLog_iff (L : List Bool → Bool) : coNTIMELinLog L ↔ NTIMELinLog (fun x => !L x) := by
  constructor
  · rintro ⟨V, c, hV⟩
    refine ⟨flip V, c, fun x => ⟨fun w hw => ?_, ?_⟩⟩
    · obtain ⟨b, hb⟩ := (hV x).1 w hw
      exact ⟨!b, haltsWithin_flip.2 (by rw [Bool.not_not]; exact hb)⟩
    · show (!L x) = true ↔ _
      constructor
      · intro hL
        have hL' : ¬ L x = true := by
          intro h
          rw [h] at hL
          exact absurd hL (by decide)
        rw [(hV x).2] at hL'
        push Not at hL'
        obtain ⟨w, hw, hnot⟩ := hL'
        obtain ⟨b, hb⟩ := (hV x).1 w hw
        cases b
        · exact ⟨w, hw, haltsWithin_flip.2 hb⟩
        · exact absurd hb hnot
      · rintro ⟨w, hw, hf⟩
        have hfalse := haltsWithin_flip.1 hf
        cases hLx : L x
        · rfl
        · have htrue := ((hV x).2.1 hLx) w hw
          exact absurd (halts_unique V htrue hfalse) (by decide)
  · rintro ⟨V, c, hV⟩
    refine ⟨flip V, c, fun x => ⟨fun w hw => ?_, ?_⟩⟩
    · obtain ⟨b, hb⟩ := (hV x).1 w hw
      exact ⟨!b, haltsWithin_flip.2 (by rw [Bool.not_not]; exact hb)⟩
    · constructor
      · intro hL w hw
        obtain ⟨b, hb⟩ := (hV x).1 w hw
        cases b
        · exact haltsWithin_flip.2 hb
        · exfalso
          have h1 : (!L x) = true := (hV x).2.2 ⟨w, hw, hb⟩
          rw [hL] at h1
          exact absurd h1 (by decide)
      · intro hall
        cases hLx : L x
        · exfalso
          have h1 : (fun x => !L x) x = true := by
            show (!L x) = true
            rw [hLx]
            rfl
          obtain ⟨w, hw, hv⟩ := (hV x).2.1 h1
          have h2 := haltsWithin_flip.1 (hall w hw)
          exact absurd (halts_unique V hv h2) (by decide)
        · rfl

theorem dtime_flip {L : List Bool → Bool} {f : ℕ → ℝ} (h : DTIMEIn L f) : DTIMEIn (fun x => !L x) f := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨flip M, C, fun x => ?_⟩
  obtain ⟨T, hT, hH⟩ := hM x
  exact ⟨T, hT, haltsWithin_flip.2 (by rw [Bool.not_not]; exact hH)⟩

/-- DTIME(n) ⊆ coNTIME[n; 2 log n]. -/
theorem dtime_sub_coNTIMELinLog {L : List Bool → Bool} (h : DTIMEIn L (fun n => (n : ℝ))) : coNTIMELinLog L :=
  (coNTIMELinLog_iff L).2 (ntime_of_dtime_linear _ (dtime_flip h))

/-- coNTIME[n; 2 log n] contains a language that depends on its input. -/
theorem coNTIME_nonconstant : coNTIMELinLog (fun x => !firstBit x) ∧ (!firstBit [true]) ≠ (!firstBit []) := by
  refine ⟨(coNTIMELinLog_iff _).2 ?_, by decide⟩
  have : (fun x => !(fun x => !firstBit x) x) = firstBit := funext fun x => Bool.not_not _
  rw [this]
  exact C1Challenge.ntime_firstBit

/-! ## G2: DTIME(f) ⊆ ⊕TIME(f): a deterministic machine has at most one accepting computation -/

theorem mem_toList_unique {α : Type} {u : Option α} {a b : α} (ha : a ∈ u.toList) (hb : b ∈ u.toList) :
    a = b := by
  cases u with
  | none => cases ha
  | some v =>
    have h1 : a = v := List.mem_singleton.1 ha
    have h2 : b = v := List.mem_singleton.1 hb
    rw [h1, h2]

theorem run_unique (M : Machine) : ∀ (os os' : List (M.Q × (M.K → M.Γ) × (M.K → HeadMove)))
    (c : Cfg M.K M.Γ M.Q),
    (toN M).Run c os → (toN M).Halted ((toN M).after c os) →
    (toN M).Run c os' → (toN M).Halted ((toN M).after c os') → os = os'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, hh, hp', _ => absurd hp' (not_run_cons_of_halted (toN M) hh)
  | _ :: _, [], _, hp, _, _, hh' => absurd hp (not_run_cons_of_halted (toN M) hh')
  | o :: os, o' :: os', c, hp, hh, hp', hh' => by
    have ho : o = o' := mem_toList_unique (u := M.code c.q (fun k => (c.tapes k).head)) hp.1 hp'.1
    subst ho
    rw [run_unique M os os' ((toN M).apply c o) hp.2 hh hp'.2 hh']

instance accComp_toN_subsingleton (M : Machine) (x : List Bool) : Subsingleton ((toN M).AccComp x) :=
  ⟨fun a b => Subtype.ext (run_unique M a.1 b.1 _ a.2.1 a.2.2.1 b.2.1 b.2.2.1)⟩

/-- A deterministic machine that answers `b`: one accepting computation if `b`, none otherwise. -/
theorem acc_toN {M : Machine} {x : List Bool} {b : Bool} {T : ℕ} (h : HaltsWithin M x b T) :
    (toN M).acc x = if b then 1 else 0 := by
  obtain ⟨t, -, c, hc, hstop, hb⟩ := h
  have hr : (toN M).Reach ((toN M).init x) t c := (reach_toN M t (M.init x) c).2 hc
  obtain ⟨s, hs, -, hl⟩ := reach_run (toN M) t _ c hr
  have hhalt : (toN M).Halted ((toN M).after ((toN M).init x) s) := by
    rw [hl]
    exact (halted_toN M c).2 hstop
  cases b
  · have : IsEmpty ((toN M).AccComp x) := ⟨fun a => by
      have heq := run_unique M a.1 s _ a.2.1 a.2.2.1 hs hhalt
      have h3 := a.2.2.2
      rw [heq, hl] at h3
      have h4 : M.accept c.q = true := h3
      rw [hb] at h4
      cases h4⟩
    show Nat.card ((toN M).AccComp x) = 0
    exact Nat.card_of_isEmpty
  · have hne : Nonempty ((toN M).AccComp x) := ⟨⟨s, hs, hhalt, by rw [hl]; exact hb⟩⟩
    show Nat.card ((toN M).AccComp x) = 1
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, hne⟩

/-- **G2.** DTIME(f) ⊆ ⊕TIME(f). -/
theorem par_of_dtime {L : List Bool → Bool} {f : ℕ → ℝ} (h : DTIMEIn L f) : ParTIMEIn L f := by
  obtain ⟨M, C, hM⟩ := h
  refine ⟨toN M, C, fun x => ?_⟩
  obtain ⟨T, hT, hH⟩ := hM x
  refine ⟨T, hT, fun c' hr => ?_, ?_⟩
  · obtain ⟨t, htT, c, hc, hstop, -⟩ := hH
    have hr' := (reach_toN M (T + 1) (M.init x) c').1 hr
    obtain ⟨k, hk⟩ : ∃ k, T + 1 = t + 1 + k := ⟨T - t, by omega⟩
    rw [hk, run_after_halt M hc hstop k] at hr'
    cases hr'
  · rw [acc_toN hH]
    cases L x <;> simp [Nat.odd_iff]

theorem par_firstBit : ParTIMEIn firstBit (fun n => (n : ℝ)) :=
  par_of_dtime (dtime_firstBit _ (fun n => Nat.cast_nonneg n))

/-! ## G4: small cases (time 0) -/

theorem run_halt (b : Bool) (x : List Bool) :
    ∀ os, (haltMachine b).Run ((haltMachine b).init x) os → os = []
  | [], _ => rfl
  | _ :: _, h => absurd h (not_run_cons_of_halted (haltMachine b) rfl)

theorem acc_halt (b : Bool) (x : List Bool) : (haltMachine b).acc x = if b then 1 else 0 := by
  have hsub : Subsingleton ((haltMachine b).AccComp x) :=
    ⟨fun a a' => Subtype.ext ((run_halt b x a.1 a.2.1).trans (run_halt b x a'.1 a'.2.1).symm)⟩
  cases b
  · have : IsEmpty ((haltMachine false).AccComp x) := ⟨fun a => by
      have h3 := a.2.2.2
      rw [run_halt false x a.1 a.2.1] at h3
      cases h3⟩
    show Nat.card ((haltMachine false).AccComp x) = 0
    exact Nat.card_of_isEmpty
  · have hne : Nonempty ((haltMachine true).AccComp x) := ⟨⟨[], trivial, rfl, rfl⟩⟩
    show Nat.card ((haltMachine true).AccComp x) = 1
    exact Nat.card_eq_one_iff_unique.2 ⟨hsub, hne⟩

theorem par_const (b : Bool) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) : ParTIMEIn (fun _ => b) f := by
  refine ⟨haltMachine b, 1, fun x => ⟨0, ?_, ?_, ?_⟩⟩
  · have := hf x.length
    push_cast
    linarith
  · rintro c ⟨c₁, ⟨out, hout, -⟩, -⟩
    cases hout
  · rw [acc_halt]
    cases b <;> simp [Nat.odd_iff]

/-! ## G5: `acc` counts computations; NTIME and ⊕TIME accept differently -/

/-- The accepting computations of the branching machine: one transition, to `some (some b)`. -/
def forkComp (x : List Bool) (b : Bool) : forkMachine.AccComp x :=
  ⟨[(some (some b), forkMachine.scanned (forkMachine.init x), fun _ => HeadMove.stay)],
    And.intro (by
      show (some (some b), forkMachine.scanned (forkMachine.init x), fun _ => HeadMove.stay) ∈
        forkMachine.code none (forkMachine.scanned (forkMachine.init x))
      rw [fork_code_none]
      cases b
      · exact List.Mem.tail _ (List.Mem.head _)
      · exact List.Mem.head _) trivial, rfl, rfl⟩

theorem forkComp_surj (x : List Bool) (a : forkMachine.AccComp x) : ∃ b, forkComp x b = a := by
  obtain ⟨os, hrun, hh, hacc⟩ := a
  match os, hrun, hh, hacc with
  | [], _, hh, _ =>
    exfalso
    have h1 : forkMachine.code none (forkMachine.scanned (forkMachine.init x)) = [] := hh
    rw [fork_code_none] at h1
    exact List.cons_ne_nil _ _ h1
  | o :: os, hrun, hh, hacc =>
    have hmem : o ∈ forkMachine.code none (forkMachine.scanned (forkMachine.init x)) := hrun.1
    rw [fork_code_none] at hmem
    rcases List.mem_cons.1 hmem with h1 | h1
    · subst h1
      match os, hrun, hh, hacc with
      | [], _, _, _ => exact ⟨true, rfl⟩
      | _ :: _, hrun, _, _ => exact absurd hrun.2 (not_run_cons_of_halted forkMachine (by exact rfl))
    rcases List.mem_cons.1 h1 with h2 | h2
    · subst h2
      match os, hrun, hh, hacc with
      | [], _, _, _ => exact ⟨false, rfl⟩
      | _ :: _, hrun, _, _ => exact absurd hrun.2 (not_run_cons_of_halted forkMachine (by exact rfl))
    rcases List.mem_cons.1 h2 with h3 | h3
    · subst h3
      match os, hrun, hh, hacc with
      | [], _, _, hacc => cases hacc
      | _ :: _, hrun, _, _ => exact absurd hrun.2 (not_run_cons_of_halted forkMachine (by exact rfl))
    cases h3

/-- The branching machine has exactly two accepting computations on every input. -/
theorem acc_fork (x : List Bool) : forkMachine.acc x = 2 := by
  have he : Function.Bijective (forkComp x) := by
    constructor
    · intro b b' hbb
      have h1 := congrArg (fun a => (a.1.head?.map (fun o => o.1))) hbb
      have h2 : (some (some (some b)) : Option (Option (Option Bool))) = some (some (some b')) := h1
      simpa using h2
    · exact forkComp_surj x
  show Nat.card (forkMachine.AccComp x) = 2
  rw [← Nat.card_eq_of_bijective (forkComp x) he]
  simp

theorem fork_not_par (x : List Bool) : ¬ Odd (forkMachine.acc x) := by
  rw [acc_fork]
  decide

end C1UGuards
end C1Challenge

#print axioms C1Challenge.C1UGuards.coNTIMELinLog_iff
#print axioms C1Challenge.C1UGuards.dtime_sub_coNTIMELinLog
#print axioms C1Challenge.C1UGuards.coNTIME_nonconstant
#print axioms C1Challenge.C1UGuards.par_of_dtime
#print axioms C1Challenge.C1UGuards.par_firstBit
#print axioms C1Challenge.C1UGuards.par_const
#print axioms C1Challenge.C1UGuards.acc_fork
#print axioms C1Challenge.C1UGuards.fork_not_par
