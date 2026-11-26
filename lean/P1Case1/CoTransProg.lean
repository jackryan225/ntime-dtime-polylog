import OAI.Computability.MultitapeWeakETH.ProgramDecision

/-!
# P1, Case 1, task C1: a small library for OpenAI's register programs `Prog`

`Runs Γ p r r' B`: the program `p` runs in scope `Γ` from registers `r` to `r'` with cost at most `B`
(OpenAI's `Prog.Run` with an exact cost). Generic loops:
* `pushes l`: straight-line pushes;
* `forEach src act`: pop the register `src` element by element and run `act a` on each element `a`
  (`act` must not touch `src`); a potential `Φ` allows non-uniform costs.
-/

set_option linter.unusedSimpArgs false

namespace P1Case1.CoTrans

open OAI.Computability.IntegerMultiplication

abbrev Rg := Reg Bool
abbrev Pg := Prog Bool
abbrev Sc := Scope Bool

/-- `p` runs from `r` to `r'` in scope `Γ` with cost at most `B`. -/
def Runs (Γ : Sc) (p : Pg) (r r' : Rg) (B : ℕ) : Prop := ∃ n, Prog.Run Γ p r n r' ∧ n ≤ B

namespace Runs

variable {Γ : Sc} {p q : Pg} {r s t : Rg} {B B' : ℕ}

theorem mono (h : Runs Γ p r s B) (hB : B ≤ B') : Runs Γ p r s B' := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨n, hr, hn.trans hB⟩

theorem pass : Runs Γ .pass r r 1 := ⟨1, .pass, le_rfl⟩

theorem push (i : ℕ) (x : Bool) : Runs Γ (.push i x) r (Function.update r i (x :: r i)) 1 :=
  ⟨1, .push, le_rfl⟩

theorem pop (i : ℕ) : Runs Γ (.pop i) r (Function.update r i (r i).tail) 1 := ⟨1, .pop, le_rfl⟩

theorem pop' {i : ℕ} {a : Bool} {l : List Bool} (h : r i = a :: l) :
    Runs Γ (.pop i) r (Function.update r i l) 1 := by
  have := pop (Γ := Γ) (r := r) i
  rwa [h, List.tail_cons] at this

theorem look {i : ℕ} {c : Option Bool → Pg} (h : Runs Γ (c (r i).head?) r s B) :
    Runs Γ (.look i c) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .look hr, by omega⟩

theorem join (h1 : Runs Γ p r s B) (h2 : Runs Γ q s t B') : Runs Γ (.join p q) r t (B + B' + 2) := by
  obtain ⟨n, hr, hn⟩ := h1
  obtain ⟨m, hm, hm'⟩ := h2
  exact ⟨1 + n + 1 + m, .join hr hm, by omega⟩

theorem tie {body : Pg} (h : Runs (body :: Γ) body r s B) : Runs Γ (.tie body) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .tie hr, by omega⟩

theorem again0 {body : Pg} (h : Runs (body :: Γ) body r s B) :
    Runs (body :: Γ) (.again 0) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .again rfl hr, by omega⟩

end Runs

/-! ## Straight-line pushes -/

/-- Push the pairs `(register, bit)` in order. -/
def pushes : List (ℕ × Bool) → Pg
  | [] => .pass
  | (i, x) :: l => .join (.push i x) (pushes l)

def pushesF : List (ℕ × Bool) → Rg → Rg
  | [], r => r
  | (i, x) :: l, r => pushesF l (Function.update r i (x :: r i))

theorem runs_pushes {Γ : Sc} (l : List (ℕ × Bool)) (r : Rg) :
    Runs Γ (pushes l) r (pushesF l r) (3 * l.length + 1) := by
  induction l generalizing r with
  | nil => exact Runs.pass
  | cons p l ih =>
    obtain ⟨i, x⟩ := p
    exact ((Runs.push i x).join (ih _)).mono (by simp; omega)

theorem pushesF_append (l₁ l₂ : List (ℕ × Bool)) (r : Rg) :
    pushesF (l₁ ++ l₂) r = pushesF l₂ (pushesF l₁ r) := by
  induction l₁ generalizing r with
  | nil => rfl
  | cons p l ih => obtain ⟨i, x⟩ := p; exact ih _

theorem pushesF_map (os : List ℕ) (a : Bool) (r : Rg) (j : ℕ) :
    pushesF (os.map fun o => (o, a)) r j = List.replicate (os.count j) a ++ r j := by
  induction os generalizing r with
  | nil => simp [pushesF]
  | cons o os ih =>
    simp only [List.map_cons, pushesF, ih, List.count_cons, Function.update_apply]
    by_cases h : j = o
    · subst h; simp [List.replicate_succ', List.append_assoc]
    · have : (o == j) = false := by simpa [beq_iff_eq] using fun e => h e.symm
      simp [h, this]

/-! ## Loops over a register -/

/-- Body of `forEach`: if `src` is empty stop, else pop its top `a`, run `act a`, repeat. -/
def eachBody (src : ℕ) (act : Bool → Pg) : Pg :=
  .look src fun o => match o with
    | none => .pass
    | some a => .join (.pop src) (.join (act a) (.again 0))

def forEach (src : ℕ) (act : Bool → Pg) : Pg := .tie (eachBody src act)

/-- One step of `forEach` on the register contents. -/
def eachStep (src : ℕ) (actF : Bool → Rg → Rg) (r : Rg) : Rg :=
  match r src with
  | [] => r
  | a :: l => actF a (Function.update r src l)

theorem eachStep_cons {src : ℕ} {actF : Bool → Rg → Rg} {r : Rg} {a : Bool} {l : List Bool}
    (h : r src = a :: l) : eachStep src actF r = actF a (Function.update r src l) := by
  simp [eachStep, h]

/-- **forEach with an invariant and a potential.** Each action, from a state with the invariant,
costs at most `C + Φ before - Φ after`; `Φ` does not grow under the actions or under popping `src`. -/
theorem runs_forEach_gen (src : ℕ) (act : Bool → Pg) (actF : Bool → Rg → Rg) (C : ℕ)
    (Φ : Rg → ℕ) (Inv : Rg → Prop)
    (hact : ∀ Γ a r, Inv r → Runs Γ (act a) r (actF a r) (C + Φ r - Φ (actF a r)))
    (hmono : ∀ a r, Inv r → Φ (actF a r) ≤ Φ r)
    (hpop : ∀ (r : Rg) (l : List Bool), Inv r → Φ (Function.update r src l) ≤ Φ r)
    (hinvA : ∀ a r, Inv r → Inv (actF a r))
    (hinvP : ∀ (r : Rg) (l : List Bool), Inv r → Inv (Function.update r src l))
    (hsrc : ∀ a r, actF a r src = r src) (Γ : Sc) (r : Rg) (hr0 : Inv r) :
    Runs Γ (forEach src act) r ((eachStep src actF)^[(r src).length] r)
      ((r src).length * (C + 7) + Φ r + 3) := by
  have key : ∀ (l : List Bool) (r : Rg), r src = l → Inv r →
      Runs (eachBody src act :: Γ) (eachBody src act) r ((eachStep src actF)^[l.length] r)
        (l.length * (C + 7) + Φ r + 2) := by
    intro l
    induction l with
    | nil =>
      intro r hr _
      have h : Runs (eachBody src act :: Γ) (eachBody src act) r r 2 := by
        refine Runs.look (c := fun o => match o with
          | none => .pass
          | some a => .join (.pop src) (.join (act a) (.again 0))) ?_
        rw [hr]
        exact Runs.pass
      exact h.mono (by omega)
    | cons a l ih =>
      intro r hr hinv
      have h2 : actF a (Function.update r src l) src = l := by rw [hsrc]; simp
      have hinv1 := hinvP r l hinv
      have hrest := ih _ h2 (hinvA a _ hinv1)
      have hstep : (eachStep src actF)^[(a :: l).length] r =
          (eachStep src actF)^[l.length] (actF a (Function.update r src l)) := by
        rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons hr]
      rw [hstep]
      have hΦ1 := hmono a (Function.update r src l) hinv1
      have hΦ2 := hpop r l hinv
      have h : Runs (eachBody src act :: Γ) (eachBody src act) r
          ((eachStep src actF)^[l.length] (actF a (Function.update r src l)))
          ((1 + (C + Φ (Function.update r src l) - Φ (actF a (Function.update r src l)) +
            ((l.length * (C + 7) + Φ (actF a (Function.update r src l)) + 2) + 1) + 2) + 2) + 1) := by
        refine Runs.look (c := fun o => match o with
          | none => .pass
          | some a => .join (.pop src) (.join (act a) (.again 0))) ?_
        rw [hr]
        exact (Runs.pop' hr).join ((hact _ a _ hinv1).join (Runs.again0 hrest))
      refine h.mono ?_
      simp only [List.length_cons]
      have e : (l.length + 1) * (C + 7) = l.length * (C + 7) + C + 7 := by ring
      rw [e]
      omega
  exact ((key _ r rfl hr0).tie).mono (by omega)

/-- **forEach with a potential.** -/
theorem runs_forEach_pot (src : ℕ) (act : Bool → Pg) (actF : Bool → Rg → Rg) (C : ℕ)
    (Φ : Rg → ℕ)
    (hact : ∀ Γ a r, Runs Γ (act a) r (actF a r) (C + Φ r - Φ (actF a r)))
    (hmono : ∀ a r, Φ (actF a r) ≤ Φ r)
    (hpop : ∀ (r : Rg) (l : List Bool), Φ (Function.update r src l) ≤ Φ r)
    (hsrc : ∀ a r, actF a r src = r src) (Γ : Sc) (r : Rg) :
    Runs Γ (forEach src act) r ((eachStep src actF)^[(r src).length] r)
      ((r src).length * (C + 7) + Φ r + 3) :=
  runs_forEach_gen src act actF C Φ (fun _ => True) (fun Γ a r _ => hact Γ a r)
    (fun a r _ => hmono a r) (fun r l _ => hpop r l) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    hsrc Γ r trivial

/-- **forEach with an invariant** and a uniform cost bound. -/
theorem runs_forEach_inv (src : ℕ) (act : Bool → Pg) (actF : Bool → Rg → Rg) (C : ℕ)
    (Inv : Rg → Prop)
    (hact : ∀ Γ a r, Inv r → Runs Γ (act a) r (actF a r) C)
    (hinvA : ∀ a r, Inv r → Inv (actF a r))
    (hinvP : ∀ (r : Rg) (l : List Bool), Inv r → Inv (Function.update r src l))
    (hsrc : ∀ a r, actF a r src = r src) (Γ : Sc) (r : Rg) (hr0 : Inv r) :
    Runs Γ (forEach src act) r ((eachStep src actF)^[(r src).length] r)
      ((r src).length * (C + 7) + 3) := by
  have := runs_forEach_gen src act actF C (fun _ => 0) Inv
    (fun Γ a r h => by simpa using hact Γ a r h) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
    hinvA hinvP hsrc Γ r hr0
  simpa using this

/-- **forEach** with a uniform cost bound `C` for each action. -/
theorem runs_forEach (src : ℕ) (act : Bool → Pg) (actF : Bool → Rg → Rg) (C : ℕ)
    (hact : ∀ Γ a r, Runs Γ (act a) r (actF a r) C)
    (hsrc : ∀ a r, actF a r src = r src) (Γ : Sc) (r : Rg) :
    Runs Γ (forEach src act) r ((eachStep src actF)^[(r src).length] r)
      ((r src).length * (C + 7) + 3) := by
  have := runs_forEach_pot src act actF C (fun _ => 0) (fun Γ a r => by simpa using hact Γ a r)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) hsrc Γ r
  simpa using this

/-- Iterating `eachStep` when the actions do not touch `src`: the source is consumed. -/
theorem eachStep_iterate_src (src : ℕ) (actF : Bool → Rg → Rg)
    (hsrc : ∀ a r, actF a r src = r src) (l : List Bool) :
    ∀ r : Rg, r src = l → ((eachStep src actF)^[l.length] r) src = [] := by
  induction l with
  | nil => intro r hr; simpa using hr
  | cons a l ih =>
    intro r hr
    rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons hr]
    exact ih _ (by rw [hsrc]; simp)

/-! ## Transfers -/

theorem flatMap_single (l : List Bool) : l.flatMap (fun a => [a]) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem flatMap_rep (l : List Bool) (k : ℕ) :
    l.flatMap (fun _ => List.replicate k true) = List.replicate (k * l.length) true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, ih, ← List.replicate_add]
    congr 1
    simp only [List.length_cons]
    ring

/-- Pop every element `a` of `src`; push `a` on each register of `outs` and `true` on each register
of `extras`. -/
def xfer (src : ℕ) (outs extras : List ℕ) : Pg :=
  forEach src fun a => pushes (outs.map (fun o => (o, a)) ++ extras.map (fun e => (e, true)))

def xferAct (outs extras : List ℕ) (a : Bool) : Rg → Rg :=
  pushesF (outs.map (fun o => (o, a)) ++ extras.map (fun e => (e, true)))

theorem xferAct_apply (outs extras : List ℕ) (a : Bool) (r : Rg) (j : ℕ) :
    xferAct outs extras a r j =
      List.replicate (extras.count j) true ++ List.replicate (outs.count j) a ++ r j := by
  rw [xferAct, pushesF_append, pushesF_map, pushesF_map, List.append_assoc]

/-- Result of `xfer`. -/
def xferF (src : ℕ) (outs extras : List ℕ) (r : Rg) : Rg := fun j =>
  if j = src then [] else
    ((r src).reverse.flatMap fun a =>
      List.replicate (extras.count j) true ++ List.replicate (outs.count j) a) ++ r j

theorem xfer_iterate (src : ℕ) (outs extras : List ℕ) (hs : src ∉ outs) (he : src ∉ extras)
    (l : List Bool) : ∀ r : Rg, r src = l →
      (eachStep src (xferAct outs extras))^[l.length] r = xferF src outs extras r := by
  induction l with
  | nil =>
    intro r hr
    funext j
    simp only [List.length_nil, Function.iterate_zero, id, xferF, hr, List.reverse_nil,
      List.flatMap_nil, List.nil_append]
    split_ifs with h
    · subst h; exact hr
    · rfl
  | cons a l ih =>
    intro r hr
    have h1 : xferAct outs extras a (Function.update r src l) src = l := by
      rw [xferAct_apply, List.count_eq_zero_of_not_mem hs, List.count_eq_zero_of_not_mem he]
      simp
    rw [List.length_cons, Function.iterate_succ_apply, eachStep_cons hr, ih _ h1]
    funext j
    simp only [xferF, h1, hr]
    split_ifs with h
    · rfl
    · rw [xferAct_apply, Function.update_of_ne h]
      simp [List.flatMap_append, List.append_assoc]

theorem runs_xfer (src : ℕ) (outs extras : List ℕ) (hs : src ∉ outs) (he : src ∉ extras)
    (Γ : Sc) (r : Rg) :
    Runs Γ (xfer src outs extras) r (xferF src outs extras r)
      ((r src).length * (3 * (outs.length + extras.length) + 8) + 3) := by
  have h := runs_forEach src _ (xferAct outs extras) (3 * (outs.length + extras.length) + 1)
    (fun Γ a r => (runs_pushes _ r).mono (by simp)) (fun a r => by
      rw [xferAct_apply, List.count_eq_zero_of_not_mem hs, List.count_eq_zero_of_not_mem he]
      simp) Γ r
  rw [xfer_iterate src outs extras hs he _ r rfl] at h
  exact h.mono (le_of_eq (by ring))

/-! ## Flags and single steps -/

/-- Register 8 is the flag register: any failure pushes `true` there. -/
def flag : Pg := .push 8 true

def flagF (r : Rg) : Rg := Function.update r 8 (true :: r 8)

theorem runs_flag {Γ : Sc} (r : Rg) : Runs Γ flag r (flagF r) 1 := Runs.push 8 true

/-- Pop `X`; flag if `X` is empty. -/
def popOrFlag (X : ℕ) : Pg := .look X fun o => match o with
  | none => flag
  | some _ => .pop X

def popOrFlagF (X : ℕ) (r : Rg) : Rg :=
  match r X with
  | [] => flagF r
  | _ :: l => Function.update r X l

theorem runs_popOrFlag {Γ : Sc} (X : ℕ) (r : Rg) : Runs Γ (popOrFlag X) r (popOrFlagF X r) 2 := by
  unfold popOrFlag
  cases h : r X with
  | nil =>
    have : popOrFlagF X r = flagF r := by simp [popOrFlagF, h]
    rw [this]
    refine Runs.look (c := fun o => match o with | none => flag | some _ => .pop X) ?_
    rw [h]; exact (runs_flag r).mono (by omega)
  | cons a l =>
    have : popOrFlagF X r = Function.update r X l := by simp [popOrFlagF, h]
    rw [this]
    refine Runs.look (c := fun o => match o with | none => flag | some _ => .pop X) ?_
    rw [h]; exact (Runs.pop' h).mono (by omega)

end P1Case1.CoTrans
