import P1ChkFinal.C7RTarget
import P1ProgEng.Lib2

/-!
The first program can consume a prefix of each input without copying its unread suffix.
The second program gets the original inputs back by replaying the three consumption logs.
-/

namespace P1SolFamAnd.Sol

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1ProgEng P1Int

variable {A : Type}

/-- The first program uses the even registers starting at 6 for its work stacks. -/
def work (i : ℕ) : ℕ := 2 * i + 6

def suffix (w : Reg A) (i : ℕ) : List A := if i < 3 then w i else []

/-- The working stack lies above the as yet unconsumed input suffix. -/
def decode (w : Reg A) : Reg A := fun i => w (work i) ++ suffix w i

/-- Registers 3 through 5 hold the consumed input prefixes in reverse order. -/
def Saved (orig w : Reg A) : Prop :=
  ∀ i, i < 3 → (w (i + 3)).reverse ++ w i = orig i

def Fresh (w : Reg A) : Prop :=
  ∀ j, 7 ≤ j → j % 2 = 1 → w j = []

def peek (i : ℕ) (c : Option A → Prog A) : Prog A :=
  if i < 3 then
    .look (work i) fun
    | none => .look i c
    | some a => c (some a)
  else .look (work i) c

def popInput (i : ℕ) : Prog A :=
  .look i fun
  | none => .pass
  | some a => .join (.pop i) (.push (i + 3) a)

def shadowPop (i : ℕ) : Prog A :=
  if i < 3 then
    .look (work i) fun
    | none => popInput i
    | some _ => .pop (work i)
  else .pop (work i)

def shadow : Prog A → Prog A
  | .pass => .pass
  | .push i a => .push (work i) a
  | .pop i => shadowPop i
  | .look i c => peek i (fun o => shadow (c o))
  | .join c d => .join (shadow c) (shadow d)
  | .tie c => .tie (shadow c)
  | .again k => .again k

theorem decode_work (w : Reg A) (i : ℕ) (l : List A) :
    decode (Function.update w (work i) l) =
      Function.update (decode w) i (l ++ suffix w i) := by
  funext j
  have hsub : suffix (Function.update w (work i) l) j = suffix w j := by
    by_cases hj : j < 3
    · have hne : j ≠ work i := by unfold work; omega
      simp only [suffix, ite_eq_left hj, Function.update_of_ne hne]
    · simp only [suffix, ite_eq_right hj]
  by_cases hji : j = i
  · subst j
    rw [Function.update_self]
    simp only [decode, Function.update_self, hsub]
  · have hne : work j ≠ work i := by unfold work; omega
    simp only [decode, Function.update_of_ne hji, Function.update_of_ne hne, hsub]

theorem saved_work {orig w : Reg A} (h : Saved orig w) (i : ℕ) (l : List A) :
    Saved orig (Function.update w (work i) l) := by
  intro j hj
  have hj₁ : j + 3 ≠ work i := by unfold work; omega
  have hj₂ : j ≠ work i := by unfold work; omega
  simpa only [Function.update_of_ne hj₁, Function.update_of_ne hj₂] using h j hj

theorem fresh_work {w : Reg A} (h : Fresh w) (i : ℕ) (l : List A) :
    Fresh (Function.update w (work i) l) := by
  intro j hj ho
  have hne : j ≠ work i := by unfold work; omega
  simpa only [Function.update_of_ne hne] using h j hj ho

theorem run_peek {Γ : Scope A} {w t : Reg A} {i B : ℕ} {c : Option A → Prog A}
    (h : Runs Γ (c (decode w i).head?) w t B) : Runs Γ (peek i c) w t (B + 2) := by
  by_cases hi : i < 3
  · rw [peek, ite_eq_left hi]
    cases hw : w (work i) with
    | nil =>
      have hs : (decode w i).head? = (w i).head? := by
        simp only [decode, suffix, ite_eq_left hi, hw, List.nil_append]
      rw [hs] at h
      refine Runs.look ?_
      rw [hw, List.head?_nil]
      exact Runs.look h
    | cons a l =>
      have hs : (decode w i).head? = some a := by
        simp only [decode, hw, List.cons_append, List.head?_cons]
      rw [hs] at h
      have hb : Runs Γ (c (some a)) w t (B + 1) := h.mono (by omega)
      refine Runs.look ?_
      rw [hw, List.head?_cons]
      exact hb
  · rw [peek, ite_eq_right hi]
    have hs : decode w i = w (work i) := by simp only [decode, suffix, ite_eq_right hi, List.append_nil]
    rw [hs] at h
    exact (Runs.look h).mono (by omega)

theorem pop_work_state {w : Reg A} {i : ℕ}
    (h : w (work i) ≠ [] ∨ ¬ i < 3) :
    decode (Function.update w (work i) (w (work i)).tail) =
      Function.update (decode w) i (decode w i).tail := by
  rw [decode_work]
  congr 1
  rcases h with h | h
  · cases hw : w (work i) with
    | nil => exact (h hw).elim
    | cons a l => simp only [decode, hw, List.cons_append, List.tail_cons]
  · simp only [decode, suffix, ite_eq_right h, List.append_nil]

theorem log_input {orig w : Reg A} {i : ℕ} {a : A} {l : List A}
    (hi : i < 3) (hw : w (work i) = []) (hv : w i = a :: l)
    (hs : Saved orig w) (hf : Fresh w) :
    let t := Function.update (Function.update w i l) (i + 3) (a :: w (i + 3))
    decode t = Function.update (decode w) i (decode w i).tail ∧
      Saved orig t ∧ Fresh t := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · funext j
    have hj₁ : work j ≠ i + 3 := by unfold work; omega
    have hj₂ : work j ≠ i := by unfold work; omega
    simp only [decode, Function.update_of_ne hj₁, Function.update_of_ne hj₂]
    by_cases hji : j = i
    · subst j
      have hne : i ≠ i + 3 := by omega
      simp only [Function.update_self, suffix, ite_eq_left hi, Function.update_of_ne hne,
        hw, hv, List.nil_append, List.tail_cons]
    · by_cases hj : j < 3
      · have hne : j ≠ i + 3 := by omega
        simp only [Function.update_of_ne hji, decode, suffix, ite_eq_left hj, Function.update_of_ne hne]
      · simp only [Function.update_of_ne hji, decode, suffix, ite_eq_right hj]
  · intro j hj
    have hne : j ≠ i + 3 := by omega
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self, Function.update_of_ne hne, List.reverse_cons,
        List.append_assoc, List.singleton_append, hv] using hs i hj
    · have hne' : j + 3 ≠ i + 3 := by omega
      have hne'' : j + 3 ≠ i := by omega
      simpa only [Function.update_of_ne hne', Function.update_of_ne hne'',
        Function.update_of_ne hne, Function.update_of_ne hji] using hs j hj
  · intro j hj ho
    have hj₁ : j ≠ i + 3 := by omega
    have hj₂ : j ≠ i := by omega
    simpa only [Function.update_of_ne hj₁, Function.update_of_ne hj₂] using hf j hj ho

theorem run_shadowPop {Γ : Scope A} {orig w : Reg A} (i : ℕ)
    (hs : Saved orig w) (hf : Fresh w) :
    ∃ t, Runs Γ (shadowPop i) w t 6 ∧
      decode t = Function.update (decode w) i (decode w i).tail ∧ Saved orig t ∧ Fresh t := by
  by_cases hi : i < 3
  · rw [shadowPop, ite_eq_left hi]
    cases hw : w (work i) with
    | nil =>
      cases hv : w i with
      | nil =>
        refine ⟨w, ?_, ?_, hs, hf⟩
        · have hr : Runs Γ (popInput i) w w 2 := by
            unfold popInput
            refine Runs.look ?_
            rw [hv, List.head?_nil]
            exact Runs.pass
          have hh : Runs Γ (.look (work i) (fun
              | none => popInput i
              | some _ => .pop (work i))) w w (2 + 1) := by
            refine Runs.look ?_
            rw [hw, List.head?_nil]
            exact hr
          exact hh.mono (by omega)
        · have he : (decode w i).tail = decode w i := by
            simp only [decode, suffix, ite_eq_left hi, hw, hv, List.nil_append, List.tail_nil]
          rw [he, Function.update_eq_self]
      | cons a l =>
        let v := Function.update w i l
        let t := Function.update v (i + 3) (a :: w (i + 3))
        refine ⟨t, ?_, log_input hi hw hv hs hf⟩
        have ha : Runs Γ (.pop i) w v 1 := by
          simpa only [v, hv, List.tail_cons] using (Runs.pop (Γ := Γ) (r := w) i)
        have hne : i + 3 ≠ i := by omega
        have hb : Runs Γ (.push (i + 3) a) v t 1 := by
          simpa only [t, v, Function.update_of_ne hne] using
            (Runs.push (Γ := Γ) (r := v) (i + 3) a)
        have hc : Runs Γ (popInput i) w t 5 := by
          unfold popInput
          refine Runs.look ?_
          rw [hv, List.head?_cons]
          exact ha.join hb
        refine Runs.look ?_
        rw [hw, List.head?_nil]
        exact hc
    | cons a l =>
      refine ⟨_, ?_, pop_work_state (Or.inl (by rw [hw]; exact List.cons_ne_nil _ _)),
        saved_work hs i _, fresh_work hf i _⟩
      have hh : Runs Γ (.look (work i) (fun
          | none => popInput i
          | some _ => .pop (work i))) w
          (Function.update w (work i) (w (work i)).tail) (1 + 1) := by
        refine Runs.look ?_
        rw [hw, List.head?_cons]
        simpa only [hw] using (Runs.pop (Γ := Γ) (r := w) (work i))
      exact hh.mono (by omega)
  · rw [shadowPop, ite_eq_right hi]
    exact ⟨_, (Runs.pop (work i)).mono (by omega), pop_work_state (Or.inr hi),
      saved_work hs i _, fresh_work hf i _⟩

theorem run_shadow {Γ : Scope A} {p : Prog A} {r s : Reg A} {n : ℕ}
    (h : Prog.Run Γ p r n s) {orig w : Reg A}
    (hw : decode w = r) (hs : Saved orig w) (hf : Fresh w) :
    ∃ t, Runs (Γ.map shadow) (shadow p) w t (6 * n) ∧
      decode t = s ∧ Saved orig t ∧ Fresh t := by
  induction h generalizing w with
  | pass =>
    exact ⟨w, Runs.pass.mono (by omega), hw, hs, hf⟩
  | @push Γ i a r =>
    let l := a :: w (work i)
    refine ⟨Function.update w (work i) l, (Runs.push (work i) a).mono (by omega),
      ?_, saved_work hs i l, fresh_work hf i l⟩
    rw [decode_work, ← hw]
    rfl
  | @pop Γ i r =>
    simpa only [shadow, ← hw] using (run_shadowPop (Γ := Γ.map shadow) i hs hf)
  | @look Γ i c r n s h ih =>
    obtain ⟨t, ht, hdec, hsave, hfresh⟩ := ih hw hs hf
    refine ⟨t, ?_, hdec, hsave, hfresh⟩
    rw [shadow]
    have hb : Runs (Γ.map shadow) (shadow (c (decode w i).head?)) w t (6 * n) := by
      rw [hw]
      exact ht
    exact (run_peek hb).mono (by omega)
  | join _ _ ih₁ ih₂ =>
    obtain ⟨v, hv, hdv, hsv, hfv⟩ := ih₁ hw hs hf
    obtain ⟨t, ht, hdt, hst, hft⟩ := ih₂ hdv hsv hfv
    exact ⟨t, (hv.join ht).mono (by omega), hdt, hst, hft⟩
  | tie _ ih =>
    obtain ⟨t, ht, hdt, hst, hft⟩ := ih hw hs hf
    exact ⟨t, ht.tie.mono (by omega), hdt, hst, hft⟩
  | @again Γ i p r n s hget _ ih =>
    obtain ⟨t, ht, hdt, hst, hft⟩ := ih hw hs hf
    obtain ⟨m, hm, hmn⟩ := ht
    refine ⟨t, ⟨1 + m, ?_, by omega⟩, hdt, hst, hft⟩
    refine Prog.Run.again (c := shadow p) ?_ ?_
    · rw [List.getElem?_map, hget]; rfl
    · rw [← List.map_drop]
      exact hm

/-- Move a reversed prefix from its log back to the front of the input. -/
def restoreBody (src dst : ℕ) : Prog A :=
  .look src fun
  | none => .pass
  | some a => .join (.pop src) (.join (.push dst a) (.again 0))

def restoreState (w : Reg A) (src dst : ℕ) : Reg A :=
  Function.update (Function.update w src []) dst ((w src).reverse ++ w dst)

theorem run_restoreBody {src dst : ℕ} (hne : src ≠ dst) (Γ : Scope A)
    (l : List A) (w : Reg A) (hl : w src = l) :
    Runs (restoreBody src dst :: Γ) (restoreBody src dst) w
      (restoreState w src dst) (8 * l.length + 2) := by
  induction l generalizing w with
  | nil =>
    have he : restoreState w src dst = w := by
      funext j
      by_cases hd : j = dst
      · subst j
        simp only [restoreState, Function.update_self, hl, List.reverse_nil, List.nil_append]
      · by_cases hs : j = src
        · subst j
          simp only [restoreState, Function.update_of_ne hne, Function.update_self, hl]
        · simp only [restoreState, Function.update_of_ne hd, Function.update_of_ne hs]
    rw [he, restoreBody]
    refine Runs.look ?_
    rw [hl, List.head?_nil]
    exact Runs.pass
  | cons a l ih =>
    let v := Function.update w src l
    let t := Function.update v dst (a :: w dst)
    have hsrc : t src = l := by
      simp only [t, v, Function.update_of_ne hne, Function.update_self]
    have hdst : t dst = a :: w dst := by simp only [t, Function.update_self]
    have he : restoreState t src dst = restoreState w src dst := by
      funext j
      by_cases hd : j = dst
      · subst j
        simp only [restoreState, Function.update_self, hsrc, hdst, hl, List.reverse_cons,
          List.append_assoc, List.singleton_append]
      · by_cases hs : j = src
        · subst j
          simp only [restoreState, Function.update_of_ne hne, Function.update_self]
        · simp only [restoreState, t, v, Function.update_of_ne hd, Function.update_of_ne hs]
    have hp : Runs (restoreBody src dst :: Γ) (.pop src) w v 1 := by
      simpa only [v, hl, List.tail_cons] using
        (Runs.pop (Γ := restoreBody src dst :: Γ) (r := w) src)
    have hq : Runs (restoreBody src dst :: Γ) (.push dst a) v t 1 := by
      simpa only [t, v, Function.update_of_ne hne.symm] using
        (Runs.push (Γ := restoreBody src dst :: Γ) (r := v) dst a)
    have hr := ((ih t hsrc).congr_out he).again0
    have hb : Runs (restoreBody src dst :: Γ)
        (.join (.pop src) (.join (.push dst a) (.again 0))) w
        (restoreState w src dst) (8 * (a :: l).length + 1) := by
      exact (hp.join (hq.join hr)).mono (by simp only [List.length_cons]; omega)
    unfold restoreBody
    refine Runs.look ?_
    rw [hl, List.head?_cons]
    exact hb

theorem run_restore {src dst : ℕ} (hne : src ≠ dst) (w : Reg A) :
    Runs [] (.tie (restoreBody src dst)) w
      (restoreState w src dst) (8 * (w src).length + 3) :=
  (run_restoreBody hne [] (w src) w rfl).tie

def restoreAll : Prog A :=
  .join (.tie (restoreBody 3 0)) (.join (.tie (restoreBody 4 1)) (.tie (restoreBody 5 2)))

def restored (w : Reg A) : Reg A :=
  restoreState (restoreState (restoreState w 3 0) 4 1) 5 2

theorem run_restoreAll (w : Reg A) :
    Runs [] restoreAll w (restored w)
      (8 * ((w 3).length + (w 4).length + (w 5).length) + 13) := by
  let w₁ := restoreState w 3 0
  let w₂ := restoreState w₁ 4 1
  have h₁ := run_restore (src := 3) (dst := 0) (by decide) w
  have h₂ := run_restore (src := 4) (dst := 1) (by decide) w₁
  have h₃ := run_restore (src := 5) (dst := 2) (by decide) w₂
  have h4 : w₁ 4 = w 4 := by norm_num [w₁, restoreState, Function.update_apply]
  have h5 : w₂ 5 = w 5 := by norm_num [w₁, w₂, restoreState, Function.update_apply]
  rw [h4] at h₂
  rw [h5] at h₃
  exact (h₁.join (h₂.join h₃)).mono (by omega)

/-- The second program uses the restored inputs and a disjoint set of work registers. -/
def second (i : ℕ) : ℕ := if i < 3 then i else 2 * i + 1

theorem second_injective : Function.Injective second := by
  intro i j h
  dsimp only [second] at h
  split at h <;> split at h <;> omega

theorem input_empty (x u ρ : List Bool) {i : ℕ} (hi : 3 ≤ i) :
    inputRegs Ltr.bit x u ρ i = [] := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  simp only [inputRegs, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]

theorem restored_second {x u ρ : List Bool} {w : Reg Ltr}
    (hs : Saved (inputRegs Ltr.bit x u ρ) w) (hf : Fresh w) (i : ℕ) :
    restored w (second i) = inputRegs Ltr.bit x u ρ i := by
  by_cases hi : i < 3
  · rw [second, ite_eq_left hi]
    have h := hs i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl <;>
      simpa [restored, restoreState, Function.update_apply] using h
  · rw [second, ite_eq_right hi, input_empty x u ρ (by omega)]
    have h0 : 2 * i + 1 ≠ 0 := by omega
    have h1 : 2 * i + 1 ≠ 1 := by omega
    have h2 : 2 * i + 1 ≠ 2 := by omega
    have h3 : 2 * i + 1 ≠ 3 := by omega
    have h4 : 2 * i + 1 ≠ 4 := by omega
    have h5 : 2 * i + 1 ≠ 5 := by omega
    simpa only [restored, restoreState, Function.update_of_ne h0, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
      Function.update_of_ne h5] using hf (2 * i + 1) (by omega) (by omega)

theorem paint_restored {x u ρ : List Bool} {w : Reg Ltr}
    (hs : Saved (inputRegs Ltr.bit x u ρ) w) (hf : Fresh w) :
    Prog.paint second (inputRegs Ltr.bit x u ρ) (restored w) = restored w := by
  funext j
  by_cases h : ∃ i, j = second i
  · obtain ⟨i, rfl⟩ := h
    rw [Prog.paint_at second_injective, restored_second hs hf]
  · exact Prog.paint_else _ _ _ (fun i hi => h ⟨i, hi⟩)

def finish : Prog Ltr := .look 0 fun o => .push 0 (.bit (P1Dispatch.answer o))

def andTail (q : Prog Ltr) (o : Option Ltr) : Prog Ltr :=
  if P1Dispatch.answer o then .join restoreAll (.join (Prog.rename second q) finish)
  else .push 0 (.bit false)

def andProg (p q : Prog Ltr) : Prog Ltr := .join (shadow p) (peek 0 (andTail q))

theorem initial_decode (x u ρ : List Bool) : decode (inputRegs Ltr.bit x u ρ) = inputRegs Ltr.bit x u ρ := by
  funext i
  simp only [decode, suffix, input_empty x u ρ (i := work i) (by unfold work; omega),
    List.nil_append]
  by_cases hi : i < 3
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, input_empty x u ρ (by omega)]

/-- The budget charges six steps per simulated step and eight per log entry. Each of
the three logs grows by at most the cost of the first simulation. -/
theorem progAnswers_and {p q : Prog Ltr} {x u ρ : List Bool} {b₁ b₂ : Bool} {B₁ B₂ : ℕ}
    (h₁ : ProgAnswers p P1Dispatch.answer (inputRegs Ltr.bit x u ρ) b₁ B₁)
    (h₂ : ProgAnswers q P1Dispatch.answer (inputRegs Ltr.bit x u ρ) b₂ B₂) :
    ProgAnswers (andProg p q) P1Dispatch.answer (inputRegs Ltr.bit x u ρ)
      (b₁ && b₂) (150 * B₁ + B₂ + 23) := by
  let orig := inputRegs Ltr.bit x u ρ
  obtain ⟨n₁, hn₁, s₁, hr₁, ha₁⟩ := h₁
  obtain ⟨n₂, hn₂, s₂, hr₂, ha₂⟩ := h₂
  have hs : Saved orig orig := by
    intro i hi
    simp only [orig, input_empty x u ρ (i := i + 3) (by omega),
      List.reverse_nil, List.nil_append]
  have hf : Fresh orig := fun j hj _ => input_empty x u ρ (by omega)
  obtain ⟨w, hw, hd, hs', hf'⟩ := run_shadow hr₁ (initial_decode x u ρ) hs hf
  have hw' : Runs [] (shadow p) orig w (6 * n₁) := hw
  have hab : P1Dispatch.answer (decode w 0).head? = b₁ := by rw [hd, ha₁]
  have htail : ∃ t, Runs [] (andTail q (decode w 0).head?) w t (144 * n₁ + B₂ + 19) ∧
      P1Dispatch.answer (t 0).head? = (b₁ && b₂) := by
    cases b₁ with
    | false =>
      refine ⟨Function.update w 0 (Ltr.bit false :: w 0), ?_, ?_⟩
      · rw [andTail, hab]
        exact (Runs.push 0 (Ltr.bit false)).mono (by omega)
      · simp only [Function.update_self, List.head?_cons, P1Dispatch.answer, Bool.false_and]
    | true =>
      obtain ⟨m, hm, hmn⟩ := hw'
      have hlen (i : ℕ) (hi : 3 ≤ i) : (w i).length ≤ 6 * n₁ := by
        have h := run_length_le hm i
        change (w i).length ≤ (inputRegs Ltr.bit x u ρ i).length + m at h
        rw [input_empty x u ρ hi, List.length_nil, Nat.zero_add] at h
        exact h.trans hmn
      have hrest := run_restoreAll w
      have h3 := hlen 3 (by decide)
      have h4 := hlen 4 (by decide)
      have h5 := hlen 5 (by decide)
      have hr := hr₂.rename second_injective (restored w)
      change Prog.Run [] (Prog.rename second q) (Prog.paint second orig (restored w)) n₂
        (Prog.paint second s₂ (restored w)) at hr
      rw [paint_restored hs' hf'] at hr
      let v := Prog.paint second s₂ (restored w)
      have hv : v 0 = s₂ 0 := Prog.paint_at second_injective s₂ (restored w) 0
      let t := Function.update v 0 (Ltr.bit (P1Dispatch.answer (v 0).head?) :: v 0)
      have hend : Runs [] finish v t 2 := Runs.look (Runs.push 0 _)
      refine ⟨t, ?_, ?_⟩
      · rw [andTail, hab]
        exact (hrest.join ((Runs.of_run hr).join hend)).mono (by omega)
      · change P1Dispatch.answer (v 0).head? = (true && b₂)
        simpa only [hv, Bool.true_and] using ha₂
  obtain ⟨t, ht, hat⟩ := htail
  have hrun := hw'.join (run_peek ht)
  obtain ⟨m, hm, hbound⟩ := hrun
  exact ⟨m, by omega, t, hm, hat⟩

theorem unit_cost_pos (s : ℝ) (a b n : ℕ) : 1 ≤ lpCost2 1 s a b n := by
  have ht : 1 ≤ lpTime a b n := by unfold lpTime; omega
  let d := 2 ^ lpT2 s a b n
  have hd : 0 < d := Nat.two_pow_pos _
  have hdiv : 1 ≤ (lpTime a b n + d - 1) / d := by
    apply (Nat.le_div_iff_mul_le hd).2
    rw [Nat.one_mul]
    omega
  have hp : 1 ≤ (lpP2 a b n + 1) ^ 6 :=
    Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm : 1 ≤ lpM2 s a b n := by
    unfold lpM2
    exact hp.trans (Nat.le_mul_of_pos_right _ hdiv)
  unfold lpCost2
  rw [Nat.one_mul]
  exact hm.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

theorem cost_factor (c : ℕ) (s : ℝ) (a b n : ℕ) :
    lpCost2 c s a b n = c * lpCost2 1 s a b n := by
  simp only [lpCost2, Nat.one_mul, Nat.mul_assoc]

end P1SolFamAnd.Sol

open P1Int P1SolFamAnd.Sol in
theorem P1SolFamAnd.famProg_and : P1ChkFinal.C7R.FamProgAndTarget := by
  intro Rc₁ Rc₂ ck₁ ck₂ s a b cc₁ cc₂ n₁ n₂ h₁ h₂
  refine ⟨andProg Rc₁ Rc₂, 150 * cc₁ + cc₂ + 23, max n₁ n₂, ?_⟩
  intro x hx
  obtain ⟨B₁, hB₁, H₁⟩ := h₁ x ((le_max_left _ _).trans hx)
  obtain ⟨B₂, hB₂, H₂⟩ := h₂ x ((le_max_right _ _).trans hx)
  refine ⟨150 * B₁ + B₂ + 23, ?_, fun u ρ hρ => progAnswers_and (H₁ u ρ hρ) (H₂ u ρ hρ)⟩
  have hp := unit_cost_pos s a b x.length
  rw [cost_factor] at hB₁ hB₂ ⊢
  let U := lpCost2 1 s a b x.length
  calc
    150 * B₁ + B₂ + 23 ≤ 150 * (cc₁ * U) + cc₂ * U + 23 * U :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 150 hB₁) hB₂)
        (Nat.le_mul_of_pos_right 23 hp)
    _ = (150 * cc₁ + cc₂ + 23) * U := by
      simp only [Nat.add_mul, Nat.mul_assoc]

example : P1ChkFinal.C7R.FamProgAndTarget := P1SolFamAnd.famProg_and

#print axioms P1SolFamAnd.famProg_and
