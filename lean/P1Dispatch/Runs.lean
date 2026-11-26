import P1Dispatch.Defs

/-!
# P1Dispatch.Runs: exact runs of `moveRev`, `build`, `conv`; the length lower bound of a run

Owner: P1-lean-dispatch. Register states are written `regs L` (register `k` holds `L.getD k []`).
-/

namespace P1Dispatch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Int

/-! ## Generic facts about runs -/

theorem run_of_eq {A : Type} {Γ : Scope A} {c : Prog A} {r : Reg A} {n m : ℕ} {r' r'' : Reg A}
    (h : Prog.Run Γ c r n r') (hn : n = m) (hr : r' = r'') : Prog.Run Γ c r m r'' := by
  subst hn; subst hr; exact h

/-- **Length bound.** One step changes the length of a register by at most one letter. -/
theorem run_len_le {A : Type} {Γ : Scope A} {c : Prog A} {r : Reg A} {n : ℕ} {r' : Reg A}
    (h : Prog.Run Γ c r n r') (j : ℕ) : (r j).length ≤ (r' j).length + n := by
  induction h with
  | pass => omega
  | @push Γ i x r =>
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, List.length_cons]; omega
    · simp [Function.update_of_ne hj]
  | @pop Γ i r =>
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self, List.length_tail]; omega
    · simp [Function.update_of_ne hj]
  | look _ ih => omega
  | join _ _ ih1 ih2 => omega
  | tie _ ih => omega
  | again _ _ ih => omega

/-! ## Register states -/

/-- Register `k` holds `L.getD k []`. -/
def regs (L : List (List Ltr)) : Reg Ltr := fun k => L.getD k []

theorem regs_apply (L : List (List Ltr)) (k : ℕ) : regs L k = L.getD k [] := rfl

theorem regs_update (L : List (List Ltr)) (s : ℕ) (hs : s < L.length) (V : List Ltr) :
    Function.update (regs L) s V = regs (L.set s V) := by
  funext k
  rw [Function.update_apply, regs_apply, regs_apply]
  by_cases h : k = s
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self hs]
    rfl
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm h)]

/-! ## One round of the loops -/

theorem mvBody_nil {Γ : Env} {s d : ℕ} {r : Reg Ltr} (he : (r s).head? = none) :
    Prog.Run Γ (mvBody s d) r (1 + 1) r := by
  unfold mvBody
  exact Prog.Run.look (by rw [he]; exact Prog.Run.pass)

theorem mvBody_bit {Γ : Env} {s d : ℕ} {r : Reg Ltr} {b : Bool} {n : ℕ} {r' : Reg Ltr}
    (he : (r s).head? = some (Ltr.bit b))
    (h : Prog.Run Γ (.join (.pop s) (.join (.push d (.bit b)) (.again 0))) r n r') :
    Prog.Run Γ (mvBody s d) r (1 + n) r' := by
  unfold mvBody
  exact Prog.Run.look (by rw [he]; exact h)

theorem bdBody_nil {Γ : Env} {s d : ℕ} {r : Reg Ltr} (he : (r s).head? = none) :
    Prog.Run Γ (bdBody s d) r (1 + 1) r := by
  unfold bdBody
  exact Prog.Run.look (by rw [he]; exact Prog.Run.pass)

theorem bdBody_bit {Γ : Env} {s d : ℕ} {r : Reg Ltr} {b : Bool} {n : ℕ} {r' : Reg Ltr}
    (he : (r s).head? = some (Ltr.bit b))
    (h : Prog.Run Γ (.join (.pop s) (.join (.push d (.bit b)) (.join (.push d .node) (.again 0)))) r n r') :
    Prog.Run Γ (bdBody s d) r (1 + n) r' := by
  unfold bdBody
  exact Prog.Run.look (by rw [he]; exact h)

/-! ## `moveRev` -/

theorem mvBody_run (s d : ℕ) (hsd : s ≠ d) (Γ : Env) : ∀ (l : List Bool) (r : Reg Ltr),
    r s = l.map Ltr.bit →
    Prog.Run (mvBody s d :: Γ) (mvBody s d) r (8 * l.length + 2)
      (Function.update (Function.update r s []) d (l.reverse.map Ltr.bit ++ r d))
  | [], r, hr => by
    have hlook : Prog.Run (mvBody s d :: Γ) (mvBody s d) r (1 + 1) r :=
      mvBody_nil (by rw [hr]; rfl)
    refine run_of_eq hlook (by simp) ?_
    funext k
    simp only [List.reverse_nil, List.map_nil, List.nil_append, Function.update_apply]
    by_cases hkd : k = d
    · rw [if_pos hkd, hkd]
    · rw [if_neg hkd]
      by_cases hks : k = s
      · rw [if_pos hks, hks, hr, List.map_nil]
      · rw [if_neg hks]
  | b :: l, r, hr => by
    have hds : d ≠ s := Ne.symm hsd
    have h2s : (Function.update (Function.update r s (r s).tail) d
        (Ltr.bit b :: (Function.update r s (r s).tail) d)) s = l.map Ltr.bit := by
      rw [Function.update_of_ne hsd, Function.update_self, hr]; rfl
    have ih := mvBody_run s d hsd Γ l _ h2s
    have hj := Prog.Run.join (Γ := mvBody s d :: Γ) (Prog.Run.pop (i := s) (r := r))
      (Prog.Run.join (Prog.Run.push (i := d) (x := Ltr.bit b)) (Prog.Run.again (i := 0) rfl ih))
    have hlook := mvBody_bit (by rw [hr]; rfl) hj
    refine run_of_eq hlook (by simp only [List.length_cons]; omega) ?_
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append]
    by_cases hkd : k = d
    · subst hkd; simp [hds]
    · by_cases hks : k = s
      · subst hks; simp [hsd]
      · simp [hkd, hks]

/-- `moveRev s d` moves the bits `l` of register `s` (reversed) on top of register `d`. -/
theorem moveRev_run (s d : ℕ) (hsd : s ≠ d) (Γ : Env) (l : List Bool) (r : Reg Ltr)
    (hr : r s = l.map Ltr.bit) :
    Prog.Run Γ (moveRev s d) r (8 * l.length + 3)
      (Function.update (Function.update r s []) d (l.reverse.map Ltr.bit ++ r d)) :=
  run_of_eq (Prog.Run.tie (mvBody_run s d hsd Γ l r hr)) (by omega) rfl

theorem moveRev_regs (Γ : Env) (L : List (List Ltr)) (s d : ℕ) (hsd : s ≠ d) (hs : s < L.length)
    (hd : d < L.length) (l : List Bool) (hl : L.getD s [] = l.map Ltr.bit) :
    Prog.Run Γ (moveRev s d) (regs L) (8 * l.length + 3)
      (regs ((L.set s []).set d (l.reverse.map Ltr.bit ++ L.getD d []))) := by
  refine run_of_eq (moveRev_run s d hsd Γ l (regs L) hl) rfl ?_
  rw [regs_update L s hs, regs_update _ d (by rw [List.length_set]; exact hd), regs_apply]

/-! ## `build` -/

/-- The spelling of a bit list: `node, bit b₁, node, bit b₂, …, bit false`. -/
theorem spell_send_list : ∀ l : List Bool,
    Tree.spell (send l) = l.flatMap (fun b => [Ltr.node, Ltr.bit b]) ++ [Ltr.bit false]
  | [] => rfl
  | b :: l => by
    rw [send_cons, List.flatMap_cons]
    show Ltr.node :: (Tree.spell (Tree.atom b) ++ Tree.spell (send l)) = _
    rw [spell_send_list l]
    rfl

theorem bdBody_run (s d : ℕ) (hsd : s ≠ d) (Γ : Env) : ∀ (l : List Bool) (r : Reg Ltr),
    r s = l.map Ltr.bit →
    Prog.Run (bdBody s d :: Γ) (bdBody s d) r (11 * l.length + 2)
      (Function.update (Function.update r s []) d
        (l.reverse.flatMap (fun b => [Ltr.node, Ltr.bit b]) ++ r d))
  | [], r, hr => by
    have hlook : Prog.Run (bdBody s d :: Γ) (bdBody s d) r (1 + 1) r :=
      bdBody_nil (by rw [hr]; rfl)
    refine run_of_eq hlook (by simp) ?_
    funext k
    simp only [List.reverse_nil, List.flatMap_nil, List.nil_append, Function.update_apply]
    by_cases hkd : k = d
    · rw [if_pos hkd, hkd]
    · rw [if_neg hkd]
      by_cases hks : k = s
      · rw [if_pos hks, hks, hr, List.map_nil]
      · rw [if_neg hks]
  | b :: l, r, hr => by
    have hds : d ≠ s := Ne.symm hsd
    have h3s : (Function.update (Function.update (Function.update r s (r s).tail) d
        (Ltr.bit b :: (Function.update r s (r s).tail) d)) d
        (Ltr.node :: (Function.update (Function.update r s (r s).tail) d
        (Ltr.bit b :: (Function.update r s (r s).tail) d)) d)) s = l.map Ltr.bit := by
      rw [Function.update_of_ne hsd, Function.update_of_ne hsd, Function.update_self, hr]; rfl
    have ih := bdBody_run s d hsd Γ l _ h3s
    have hj := Prog.Run.join (Γ := bdBody s d :: Γ) (Prog.Run.pop (i := s) (r := r))
      (Prog.Run.join (Prog.Run.push (i := d) (x := Ltr.bit b))
        (Prog.Run.join (Prog.Run.push (i := d) (x := Ltr.node)) (Prog.Run.again (i := 0) rfl ih)))
    have hlook := bdBody_bit (by rw [hr]; rfl) hj
    refine run_of_eq hlook (by simp only [List.length_cons]; omega) ?_
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    by_cases hkd : k = d
    · subst hkd; simp [hds]
    · by_cases hks : k = s
      · subst hks; simp [hsd]
      · simp [hkd, hks]

/-- If register `s` holds `l` reversed, `build s d` writes `spell (send l)` on register `d`. -/
theorem build_run (s d : ℕ) (hsd : s ≠ d) (Γ : Env) (l : List Bool) (r : Reg Ltr)
    (hr : r s = l.reverse.map Ltr.bit) :
    Prog.Run Γ (build s d) r (11 * l.length + 6)
      (Function.update (Function.update r s []) d (Tree.spell (send l) ++ r d)) := by
  have hr0 : (Function.update r d (Ltr.bit false :: r d)) s = l.reverse.map Ltr.bit := by
    rw [Function.update_of_ne hsd, hr]
  have hb := bdBody_run s d hsd Γ l.reverse _ hr0
  have hrun := Prog.Run.join (Prog.Run.push (Γ := Γ) (i := d) (x := Ltr.bit false) (r := r))
    (Prog.Run.tie hb)
  refine run_of_eq hrun (by simp only [List.length_reverse]; omega) ?_
  funext k
  rw [spell_send_list, List.reverse_reverse]
  simp only [Function.update_apply]
  by_cases hkd : k = d
  · subst hkd; simp
  · by_cases hks : k = s
    · subst hks; simp [hsd]
    · simp [hkd, hks]

theorem build_regs (Γ : Env) (L : List (List Ltr)) (s d : ℕ) (hsd : s ≠ d) (hs : s < L.length)
    (hd : d < L.length) (l : List Bool) (hl : L.getD s [] = l.reverse.map Ltr.bit) :
    Prog.Run Γ (build s d) (regs L) (11 * l.length + 6)
      (regs ((L.set s []).set d (Tree.spell (send l) ++ L.getD d []))) := by
  refine run_of_eq (build_run s d hsd Γ l (regs L) hl) rfl ?_
  rw [regs_update L s hs, regs_update _ d (by rw [List.length_set]; exact hd), regs_apply]

theorem push_regs (Γ : Env) (L : List (List Ltr)) (d : ℕ) (hd : d < L.length) (e : Ltr) :
    Prog.Run Γ (.push d e) (regs L) 1 (regs (L.set d (e :: L.getD d []))) := by
  refine run_of_eq (Prog.Run.push (Γ := Γ) (i := d) (x := e) (r := regs L)) rfl ?_
  rw [regs_update L d hd, regs_apply]

/-! ## The conversion -/

theorem inputRegs_eq_regs (x u ρ : List Bool) :
    inputRegs Ltr.bit x u ρ = regs [x.map Ltr.bit, u.map Ltr.bit, ρ.map Ltr.bit, [], []] := by
  funext k
  rcases k with _ | _ | _ | _ | _ | k <;> simp [inputRegs, regs]

theorem letters_pile_eq_regs (z : Tree) :
    letters (pile 0 z (fun _ => [])) = regs [Tree.spell z, [], [], [], []] := by
  funext k
  rcases k with _ | _ | _ | _ | _ | k <;> simp [letters, pile, regs, Function.update_apply]

/-- **The conversion.** From the raw registers `x, u, ρ` to the tree `send (x, u, ρ)` on register 0 with
every other register empty, in `19 (|x| + |u| + |ρ|) + 43` steps. -/
theorem conv_run (Γ : Env) (x u ρ : List Bool) :
    Prog.Run Γ conv (inputRegs Ltr.bit x u ρ) (19 * (x.length + u.length + ρ.length) + 43)
      (letters (pile 0 (send (x, u, ρ)) (fun _ => []))) := by
  rw [inputRegs_eq_regs, letters_pile_eq_regs]
  have h1 := moveRev_regs Γ [x.map Ltr.bit, u.map Ltr.bit, ρ.map Ltr.bit, [], []] 0 3 (by decide)
    (by simp) (by simp) x (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h1
  have h2 := moveRev_regs Γ [[], u.map Ltr.bit, ρ.map Ltr.bit, x.reverse.map Ltr.bit, []] 2 4
    (by decide) (by simp) (by simp) ρ (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h2
  have h3 := build_regs Γ [[], u.map Ltr.bit, [], x.reverse.map Ltr.bit, ρ.reverse.map Ltr.bit] 4 0
    (by decide) (by simp) (by simp) ρ (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h3
  have h4 := moveRev_regs Γ [Tree.spell (send ρ), u.map Ltr.bit, [], x.reverse.map Ltr.bit, []] 1 4
    (by decide) (by simp) (by simp) u (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h4
  have h5 := build_regs Γ [Tree.spell (send ρ), [], [], x.reverse.map Ltr.bit, u.reverse.map Ltr.bit]
    4 0 (by decide) (by simp) (by simp) u (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h5
  have h6 := push_regs Γ [Tree.spell (send u) ++ Tree.spell (send ρ), [], [], x.reverse.map Ltr.bit, []]
    0 (by simp) Ltr.node
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h6
  have h7 := build_regs Γ [Ltr.node :: (Tree.spell (send u) ++ Tree.spell (send ρ)), [], [],
    x.reverse.map Ltr.bit, []] 3 0 (by decide) (by simp) (by simp) x (by simp)
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h7
  have h8 := push_regs Γ [Tree.spell (send x) ++ Ltr.node :: (Tree.spell (send u) ++
    Tree.spell (send ρ)), [], [], [], []] 0 (by simp) Ltr.node
  simp only [List.set_cons_zero, List.set_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    List.append_nil] at h8
  have hall := Prog.Run.join h1 (Prog.Run.join h2 (Prog.Run.join h3 (Prog.Run.join h4
    (Prog.Run.join h5 (Prog.Run.join h6 (Prog.Run.join h7 h8))))))
  refine run_of_eq hall (by omega) ?_
  rfl

end P1Dispatch
