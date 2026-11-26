import P1C1U.Physical

namespace P1C1U.AstraC1U.Physical

open C1Challenge
open OAI.Computability.IntegerMultiplication
open OAI.Computability.MultitapeWeakETH (Word initial run writes timely)

noncomputable section

theorem follow (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M) :
    ∀ (os : List (Out M)) (c : Conf M) (i : ℕ) (d : PCfg M),
      M.Run c os → path M x y cs i = some d → Agree M n (bits cs) d c →
      (∀ j : Fin os.length, (cs (i + j.val)).2 = some (os.get j)) →
      ∃ d', path M x y cs (i + os.length) = some d' ∧ Agree M n (bits cs) d' (M.after c os)
  | [], _, _, d, _, hd, ag, _ => ⟨d, hd, ag⟩
  | o :: os, c, i, d, hr, hd, ag, picks => by
    have h0 : (cs i).2 = some o := by simpa using picks (0 : Fin (o :: os).length)
    have hc : (resolve M (cs i).2).step c = some (M.apply c o) := by
      rw [h0]
      exact resolve_of_mem hr.1
    obtain ⟨d₁, hs, ag₁⟩ := forward_step M ag (cs i) hc
    have hr₁ : path M x y cs (i + 1) = some d₁ := by
      change (path M x y cs i).bind _ = some d₁
      rw [hd]
      exact hs
    have tailpicks : ∀ j : Fin os.length, (cs (i + 1 + j.val)).2 = some (os.get j) := by
      intro j
      have e : i + 1 + j.val = i + j.succ.val := by simp only [Fin.val_succ]; omega
      rw [e]
      exact picks j.succ
    have e : i + (o :: os).length = i + 1 + os.length := by simp only [List.length_cons]; omega
    rw [e]
    exact follow M x y cs os (M.apply c o) (i + 1) d₁ hr.2 hr₁ ag₁ tailpicks

theorem extract (M : NMachine) {n : ℕ} (x y : Word n) (cs : ℕ → Coin M)
    {i : ℕ} {d : PCfg M} {c : Conf M} (hi : path M x y cs i = some d)
    (ag : Agree M n (bits cs) d c) (t : ℕ) :
    ∀ d', path M x y cs (i + t) = some d' →
    ∃ c', M.Reach c t c' ∧ Agree M n (bits cs) d' c' := by
  induction t with
  | zero =>
    intro d' hd
    have he : d = d' := Option.some.inj (hi.symm.trans hd)
    subst d'
    exact ⟨c, rfl, ag⟩
  | succ t ih =>
    intro d' hd
    change (path M x y cs (i + t)).bind (TM.advance ((machine M).rule (cs (i + t)))) = some d' at hd
    cases hp : path M x y cs (i + t) with
    | none => rw [hp] at hd; cases hd
    | some p =>
      have hs : TM.advance ((machine M).rule (cs (i + t))) p = some d' := by
        change @Eq (Option (PCfg M)) (TM.advance ((machine M).rule (cs (i + t))) p) (some d')
        rw [hp] at hd
        exact hd
      obtain ⟨c₀, reach₀, ag₀⟩ := ih p hp
      obtain ⟨c', hnext, ag'⟩ := backward_step M ag₀ (cs (i + t)) hs
      exact ⟨c', (P1NTime.AstraNTime.reach_add M t 1 c c').mpr ⟨c₀, reach₀, c', hnext, rfl⟩, ag'⟩

private theorem run_coins_eq (D : OAI.Computability.MultitapeWeakETH.Machine)
    (d : OAI.Computability.MultitapeWeakETH.Config D) (cs cs' : ℕ → D.Choice) (t : ℕ)
    (he : ∀ i < t, cs i = cs' i) : run D cs d t = run D cs' d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (run D cs d t).bind (TM.advance (D.rule (cs t))) =
      (run D cs' d t).bind (TM.advance (D.rule (cs' t)))
    rw [ih (fun i hi => he i (by omega)), he t (by omega)]

private theorem timely_of_path (M : NMachine) {n U t : ℕ} (x y w : Word n) (cs : ℕ → Coin M)
    (d : PCfg M) (ht : t ≤ U) (hd : path M x y cs t = some d)
    (hs : TM.advance ((machine M).rule (cs t)) d = none) (ha : (machine M).accepts d.pc = true)
    (hw : writes (machine M) d w) :
    ∃ seed : Fin (U + 1) → Coin M, timely (machine M) U seed x y w := by
  let seed : Fin (U + 1) → Coin M := fun j => cs j.val
  refine ⟨seed, t, ht, d, ?_, hs, ha, hw⟩
  refine (run_coins_eq (machine M) (initial (machine M) x y) _ cs t ?_).trans hd
  intro j hj
  change cs (min j U) = cs j
  rw [min_eq_left (by omega)]

/-- A chosen accepting sequence supplies every transition choice after the guessing prefix. -/
theorem realize (M : NMachine) {n U : ℕ} (x y w : Word n)
    (s : M.AccComp (List.ofFn x ++ List.ofFn w)) (ht : 3 * n + 2 + s.val.length ≤ U) :
    ∃ seed : Fin (U + 1) → Coin M, timely (machine M) U seed x y w := by
  let start := 3 * n + 2
  let cs (i : ℕ) : Coin M :=
    (if hi : i < n then w ⟨i, hi⟩ else false, s.val[i - start]?)
  have hb : (fun j : Fin n => bits cs j.val) = w := by
    funext j
    simp only [bits, cs, dif_pos j.isLt]
  have picks : ∀ j : Fin s.val.length, (cs (start + j.val)).2 = some (s.val.get j) := by
    intro j
    simp [cs, j.isLt]
  obtain ⟨d, hd, ag⟩ := prefix_run M x y cs
  rw [hb] at ag
  obtain ⟨d', hd', ag'⟩ := follow M x y cs s.val _ start d s.property.1 hd ag picks
  have hw := written M ag'
  rw [hb] at hw
  exact timely_of_path M x y w cs d' ht hd'
    ((halt_iff M ag' _).mpr s.property.2.1) ((answer M ag').trans s.property.2.2) hw

/-- Every timely output has an accepting computation on the concatenation of the input and that output. -/
theorem reflects (M : NMachine) {n T : ℕ} (x y w : Word n) (seed : Fin (T + 1) → Coin M)
    (h : timely (machine M) T seed x y w) : Nonempty (M.AccComp (List.ofFn x ++ List.ofFn w)) := by
  let cs (i : ℕ) : Coin M := seed ⟨min i T, Nat.lt_succ_of_le (min_le_right ..)⟩
  obtain ⟨t, ht, d, hd, hs, ha, hw⟩ := h
  have hd' : path M x y cs t = some d := hd
  have hlate := after_prefix_of_accept M x y cs hd' ha
  obtain ⟨d₀, h₀, ag₀⟩ := prefix_run M x y cs
  have hend : 3 * n + 2 + (t - (3 * n + 2)) = t := by omega
  obtain ⟨c, hr, ag⟩ := extract M x y cs h₀ ag₀ (t - (3 * n + 2)) d (by rwa [hend])
  have heq : w = fun j : Fin n => bits cs j.val := by
    funext j
    apply (machine M).bit_injective
    exact (hw j).symm.trans (written M ag j)
  have hh := (halt_iff M ag (seed ⟨t, Nat.lt_succ_of_le ht⟩)).mp hs
  have hv := (answer M ag).symm.trans ha
  obtain ⟨os, hrun, _, he⟩ := C1UGuards.reach_run M _ _ _ hr
  rw [heq]
  exact ⟨⟨os, hrun, he.symm ▸ hh, he.symm ▸ hv⟩⟩

end
end P1C1U.AstraC1U.Physical

#print axioms P1C1U.AstraC1U.Physical.realize
#print axioms P1C1U.AstraC1U.Physical.reflects
