import P1Hier.TabPhase

/-!
# P1Hier.TapeLoop: one tape pass of the transcript check as a stack program

`colOK t cells` simulates ONE tape along its column of cells (read, write, move). Register layout of
the loop: column on register 0, left part `t.L` on 1, right part `t.R` on 3 (both as list trees, so a
push or pop at the head costs the size of one symbol), `(t.h, ok)` on 4; register 2 is scratch.
Each step costs `O(size cell + size head + size popped symbol)`, so a pass over a column of length
`m` on a tape whose symbols are `≤ B` costs `O(size column + (m + |tape|) (B + 1))`.

Main result: `tape_task`.
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Functional side -/

/-- Run one tape along a column: final tape and accumulated answer. -/
def runT : Tp → Bool → List Cell → Tp × Bool
  | t, ok, [] => (t, ok)
  | t, ok, x :: rest => runT (t.act x.2.1 x.2.2) (ok && (x.1 == t.h)) rest

theorem runT_snd (t : Tp) (ok : Bool) (l : List Cell) : (runT t ok l).2 = (ok && colOK t l) := by
  induction l generalizing t ok with
  | nil => simp [runT, colOK]
  | cons x rest ih => rw [runT, ih, colOK, Bool.and_assoc]

/-- All symbols of a tape are at most `B`. -/
def TpLe (B : ℕ) (t : Tp) : Prop := (∀ s ∈ t.L, s ≤ B) ∧ t.h ≤ B ∧ ∀ s ∈ t.R, s ≤ B

theorem headD_le {B : ℕ} {l : List ℕ} (h : ∀ s ∈ l, s ≤ B) : l.headD 0 ≤ B := by
  cases l with
  | nil => exact Nat.zero_le _
  | cons a l => exact h a List.mem_cons_self

theorem mem_tail_le {B : ℕ} {l : List ℕ} (h : ∀ s ∈ l, s ≤ B) : ∀ s ∈ l.tail, s ≤ B :=
  fun s hs => h s (List.mem_of_mem_tail hs)

theorem tpLe_act {B : ℕ} {t : Tp} (ht : TpLe B t) {w : ℕ} (hw : w ≤ B) (m : Mv) :
    TpLe B (t.act w m) := by
  obtain ⟨hL, -, hR⟩ := ht
  cases m with
  | none => exact ⟨hL, hw, hR⟩
  | some b =>
    cases b with
    | false =>
      refine ⟨mem_tail_le hL, headD_le hL, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hw
      · exact hR s hs
    | true =>
      refine ⟨?_, headD_le hR, mem_tail_le hR⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hw
      · exact hL s hs

/-- Number of stored cells of a tape besides the head. -/
def tlen (t : Tp) : ℕ := t.L.length + t.R.length

theorem tlen_act (t : Tp) (w : ℕ) (m : Mv) : tlen (t.act w m) ≤ tlen t + 1 := by
  cases m with
  | none => simp [Tp.act, tlen]
  | some b => cases b <;> simp [Tp.act, tlen] <;> omega

theorem runT_bound {B : ℕ} (l : List Cell) (hl : ∀ x ∈ l, x.2.1 ≤ B) :
    ∀ (t : Tp) (ok : Bool), TpLe B t →
      TpLe B (runT t ok l).1 ∧ tlen (runT t ok l).1 ≤ tlen t + l.length := by
  induction l with
  | nil => intro t ok ht; exact ⟨ht, by simp [runT]⟩
  | cons x rest ih =>
    intro t ok ht
    have hx := hl x List.mem_cons_self
    have hr : ∀ y ∈ rest, y.2.1 ≤ B := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    obtain ⟨h1, h2⟩ := ih hr (t.act x.2.1 x.2.2) (ok && (x.1 == t.h)) (tpLe_act ht hx _)
    refine ⟨h1, ?_⟩
    have := tlen_act t x.2.1 x.2.2
    simp only [runT, List.length_cons]
    omega

theorem size_natList_le {B : ℕ} (l : List ℕ) (h : ∀ s ∈ l, s ≤ B) :
    size l ≤ l.length * (2 * B + 2) + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [size_cons, size_nat, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-! ## Decks -/

theorem pile_apply (i : ℕ) (z : Tree) (r : Deck) (j : ℕ) :
    pile i z r j = if j = i then z :: r j else r j := by
  by_cases h : j = i
  · subst h; simp
  · simp [pile_else _ _ _ _ h, h]

/-- Equality of two decks built by `pile` on distinct numbered registers. -/
macro "deck_eq" : tactic =>
  `(tactic| (funext j; simp only [pile_apply]; split_ifs <;> first | rfl | omega | simp_all))

theorem _root_.OAI.Computability.IntegerMultiplication.Code.Fits.cast' {env : Env} {c : Cmd} {r r' s s' : Deck} {n : ℕ} (h : Fits env c r s n)
    (hr : r = r') (hs : s = s') : Fits env c r' s' n := hr ▸ hs ▸ h

/-- Loop state. -/
def tdeck (cells : List Cell) (t : Tp) (ok : Bool) (r : Deck) : Deck :=
  pile 0 (send cells) (pile 1 (send t.L) (pile 3 (send t.R) (pile 4 (send (t.h, ok)) r)))

/-- State after the column is used up. -/
def tdone (t : Tp) (ok : Bool) (r : Deck) : Deck :=
  pile 1 (send t.L) (pile 3 (send t.R) (pile 4 (send (t.h, ok)) r))

theorem tdeck_eq (cells : List Cell) (t : Tp) (ok : Bool) (r : Deck) :
    tdeck cells t ok r = pile 0 (send cells) (tdone t ok r) := rfl

/-! ## Moves of the head -/

/-- Pop the head of the list tree on register `i` into register 4 (blank `0` if empty). -/
def popL (i : ℕ) : Cmd := splitRoot i (fun b => (give i b).join (give 4 false)) (move i 4 2)

theorem fits_popL (i : ℕ) (h2 : i ≠ 2) (env : Env) (l : List ℕ) (r : Deck) :
    Fits env (popL i) (pile i (send l) r) (pile 4 (send (l.headD 0)) (pile i (send l.tail) r))
      (42 * size (l.headD 0) + 8) := by
  cases l with
  | nil =>
    have h := (fits_give (env := env) false r i).join
      (fits_give false (pile i (Tree.atom false) r) 4 env)
    refine (fits_bit (b := false) (c := fun b => (give i b).join (give 4 false))
      (d := move i 4 2) h).mono ?_
    have := size_pos (([] : List ℕ).headD 0)
    omega
  | cons a l =>
    have h := fits_move (i := i) (j := 4) (u := 2) h2 (by decide) (send a) env (pile i (send l) r)
    refine (fits_pair (c := fun b => (give i b).join (give 4 false)) h).mono ?_
    simp only [List.headD_cons, size]
    omega

/-- Move the top tree of register 4 onto the list on register `j`. -/
def pushL (j : ℕ) : Cmd := (move 4 j 2).join (pack j)

theorem fits_pushL (j : ℕ) (h2 : j ≠ 2) (env : Env) (w : ℕ) (l : List ℕ) (r : Deck) :
    Fits env (pushL j) (pile 4 (send w) (pile j (send l) r)) (pile j (send (w :: l)) r)
      (42 * size w + 3) := by
  have h1 := fits_move (i := 4) (j := j) (u := 2) (by decide) (Ne.symm h2) (send w) env
    (pile j (send l) r)
  have h2' := fits_pack (send w) (send l) r j env
  exact (h1.join h2').mono (by simp only [size]; omega)

def moveL : Cmd := splitRoot 4 (fun _ => .pass) ((pushL 3).join ((popL 1).join (pack 4)))

def moveR : Cmd := splitRoot 4 (fun _ => .pass) ((pushL 1).join ((popL 3).join (pack 4)))

theorem fits_moveL (env : Env) (t : Tp) (w : ℕ) (ok : Bool) (rest : List Cell) (r : Deck) :
    Fits env moveL (pile 0 (send rest) (tdone ⟨t.L, w, t.R⟩ ok r))
      (tdeck rest (t.act w (some false)) ok r) (42 * size w + 42 * size (t.L.headD 0) + 22) := by
  have a := fits_pushL 3 (by decide) env w t.R
    (pile 4 (send ok) (pile 0 (send rest) (pile 1 (send t.L) r)))
  have b := fits_popL 1 (by decide) env t.L
    (pile 3 (send (w :: t.R)) (pile 4 (send ok) (pile 0 (send rest) r)))
  have c := fits_pack (send (t.L.headD 0)) (send ok)
    (pile 0 (send rest) (pile 1 (send t.L.tail) (pile 3 (send (w :: t.R)) r))) 4 env
  have abc : Fits env ((pushL 3).join ((popL 1).join (pack 4)))
      (pile 4 (send w) (pile 4 (send ok) (pile 0 (send rest) (pile 1 (send t.L) (pile 3 (send t.R) r)))))
      (tdeck rest (t.act w (some false)) ok r) _ :=
    (a.join ((b.cast' (by deck_eq) rfl).join (c.cast' (by deck_eq) rfl))).cast' (by deck_eq)
      (by simp only [tdeck, Tp.act]; deck_eq)
  exact ((fits_pair (c := fun _ => Prog.pass) abc).cast' (by simp only [tdone]; deck_eq) rfl).mono
    (by omega)

theorem fits_moveR (env : Env) (t : Tp) (w : ℕ) (ok : Bool) (rest : List Cell) (r : Deck) :
    Fits env moveR (pile 0 (send rest) (tdone ⟨t.L, w, t.R⟩ ok r))
      (tdeck rest (t.act w (some true)) ok r) (42 * size w + 42 * size (t.R.headD 0) + 22) := by
  have a := fits_pushL 1 (by decide) env w t.L
    (pile 4 (send ok) (pile 0 (send rest) (pile 3 (send t.R) r)))
  have b := fits_popL 3 (by decide) env t.R
    (pile 1 (send (w :: t.L)) (pile 4 (send ok) (pile 0 (send rest) r)))
  have c := fits_pack (send (t.R.headD 0)) (send ok)
    (pile 0 (send rest) (pile 1 (send (w :: t.L)) (pile 3 (send t.R.tail) r))) 4 env
  have abc : Fits env ((pushL 1).join ((popL 3).join (pack 4)))
      (pile 4 (send w) (pile 4 (send ok) (pile 0 (send rest) (pile 1 (send t.L) (pile 3 (send t.R) r)))))
      (tdeck rest (t.act w (some true)) ok r) _ :=
    (a.join ((b.cast' (by deck_eq) rfl).join (c.cast' (by deck_eq) rfl))).cast' (by deck_eq)
      (by simp only [tdeck, Tp.act]; deck_eq)
  exact ((fits_pair (c := fun _ => Prog.pass) abc).cast' (by simp only [tdone]; deck_eq) rfl).mono
    (by omega)

/-- Size of the symbol popped by the move `m`. -/
def popSize (t : Tp) : Mv → ℕ
  | none => 0
  | some false => size (t.L.headD 0)
  | some true => size (t.R.headD 0)

/-- Dispatch on the move (register 0 holds the move). -/
def moveCmd : Cmd :=
  splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun _ => splitRoot 0 (fun b => bif b then moveR else moveL) .pass) .pass)

theorem fits_moveCmd (env : Env) (t : Tp) (w : ℕ) (ok : Bool) (m : Mv) (rest : List Cell)
    (r : Deck) :
    Fits env moveCmd (pile 0 (send m) (pile 0 (send rest) (tdone ⟨t.L, w, t.R⟩ ok r)))
      (tdeck rest (t.act w m) ok r) (42 * size w + 42 * popSize t m + 40) := by
  cases m with
  | none =>
    exact (fits_bit (b := false) (c := fun _ => Prog.pass) (i := 0)
      (Fits.pass (env := env) (pile 0 (send rest) (tdone ⟨t.L, w, t.R⟩ ok r)))).mono (by omega)
  | some b =>
    cases b with
    | false =>
      have hm := fits_moveL env t w ok rest r
      have h1 := fits_bit (b := false) (c := fun b => bif b then moveR else moveL) (d := Prog.pass)
        (env := env) (i := 0) hm
      have h2 := fits_bit (b := true) (c := fun _ => splitRoot 0 (fun b => bif b then moveR else moveL)
        Prog.pass) (d := Prog.pass) (env := env) (i := 0) h1
      have h3 := fits_pair (c := fun _ => Prog.pass) (env := env) (i := 0) h2
      exact h3.mono (by simp only [popSize]; omega)
    | true =>
      have hm := fits_moveR env t w ok rest r
      have h1 := fits_bit (b := true) (c := fun b => bif b then moveR else moveL) (d := Prog.pass)
        (env := env) (i := 0) hm
      have h2 := fits_bit (b := true) (c := fun _ => splitRoot 0 (fun b => bif b then moveR else moveL)
        Prog.pass) (d := Prog.pass) (env := env) (i := 0) h1
      have h3 := fits_pair (c := fun _ => Prog.pass) (env := env) (i := 0) h2
      exact h3.mono (by simp only [popSize]; omega)

/-! ## One step -/

theorem beq_nat (a b : ℕ) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-- The comparison at the head: `(write, read, head, ok) ↦ (write, ok && read == head)`. -/
def cmpF (z : ℕ × ℕ × ℕ × Bool) : ℕ × Bool := (z.1, z.2.2.2 && (z.2.1 == z.2.2.1))

theorem easy_natEq : Easy (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  have h : Easy (fun p : ℕ × ℕ =>
      decide ((List.replicate p.1 ()).length = (List.replicate p.2 ()).length)) :=
    ((Easy.fst.compose easy_tally).pair (Easy.snd.compose easy_tally)).compose Code.Iter.linked
  simpa only [List.length_replicate] using h

theorem easy_cmpF : Easy cmpF := by
  have hok : Easy (fun z : ℕ × ℕ × ℕ × Bool => z.2.2.2) :=
    Easy.sndCompose (Easy.sndCompose Easy.snd)
  have hrd : Easy (fun z : ℕ × ℕ × ℕ × Bool => z.2.1) := Easy.fstCompose Easy.snd
  have hh : Easy (fun z : ℕ × ℕ × ℕ × Bool => z.2.2.1) :=
    Easy.fstCompose (Easy.sndCompose Easy.snd)
  have heq : Easy (fun z : ℕ × ℕ × ℕ × Bool => decide (z.2.1 = z.2.2.1)) :=
    (hrd.pair hh).compose easy_natEq
  have hand : Easy (fun z : ℕ × ℕ × ℕ × Bool => z.2.2.2 && decide (z.2.1 = z.2.2.1)) :=
    (hok.pair heq).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2))
  have h := (Easy.fst (X := ℕ) (Y := ℕ × ℕ × Bool)).pair hand
  have e : (fun z : ℕ × ℕ × ℕ × Bool => (z.1, z.2.2.2 && decide (z.2.1 = z.2.2.1))) = cmpF := by
    funext z; simp only [cmpF, beq_nat]
  rw [e] at h
  exact h

def stepB (cmp : Cmd) : Cmd := (move 0 4 2).join ((pack 4).join (cmp.join moveCmd))

def stepA (cmp : Cmd) : Cmd :=
  (move 0 4 2).join ((pack 4).join (splitRoot 0 (fun _ => .pass) (stepB cmp)))

def step (cmp : Cmd) : Cmd := splitRoot 0 (fun _ => .pass) (stepA cmp)

/-- Cost of one step. -/
def stepCost (C : ℕ) (x : Cell) (t : Tp) : ℕ := (C + 200) * (size x + size t.h + popSize t x.2.2 + 4)

/-- The deck without register 4. -/
def tbase (t : Tp) (rest : List Cell) (r : Deck) : Deck :=
  pile 0 (send rest) (pile 1 (send t.L) (pile 3 (send t.R) r))

theorem popSize_head (t : Tp) (w : ℕ) (m : Mv) : popSize ⟨t.L, w, t.R⟩ m = popSize t m := by
  cases m with
  | none => rfl
  | some b => cases b <;> rfl

theorem fits_step (cmp : Cmd) (C : ℕ)
    (hcmp : ∀ (z : ℕ × ℕ × ℕ × Bool) (env : Env),
      Fits.value env cmp 4 (send z) (send (cmpF z)) (C * (size z + 1)))
    (env : Env) (x : Cell) (rest : List Cell) (t : Tp) (ok : Bool) (r : Deck) :
    Fits env (step cmp) (pile 0 (send x) (pile 0 (send rest) (tdone t ok r)))
      (tdeck rest (t.act x.2.1 x.2.2) (ok && (x.1 == t.h)) r) (stepCost C x t) := by
  obtain ⟨rd, wr, m⟩ := x
  have h3 : Fits env (move 0 4 2) (pile 0 (send wr) (pile 0 (send m)
      (pile 4 (send (rd, t.h, ok)) (tbase t rest r))))
      (pile 4 (send wr) (pile 0 (send m) (pile 4 (send (rd, t.h, ok)) (tbase t rest r))))
      (42 * size wr) := fits_move (by decide) (by decide) (send wr) env _
  have h4 : Fits env (pack 4) (pile 4 (send wr) (pile 4 (send (rd, t.h, ok))
      (pile 0 (send m) (tbase t rest r))))
      (pile 4 (send (wr, rd, t.h, ok)) (pile 0 (send m) (tbase t rest r))) 1 :=
    fits_pack (send wr) (send (rd, t.h, ok)) _ 4 env
  have h5 := hcmp (wr, rd, t.h, ok) env (pile 0 (send m) (tbase t rest r))
  have h6 := fits_moveCmd env t wr (ok && (rd == t.h)) m rest r
  rw [popSize_head] at h6
  have hB : Fits env (stepB cmp) (pile 0 (send wr) (pile 0 (send m)
      (pile 4 (send (rd, t.h, ok)) (tbase t rest r))))
      (tdeck rest (t.act wr m) (ok && (rd == t.h)) r) _ :=
    h3.join ((h4.cast' (by deck_eq) rfl).join (h5.join (h6.cast' (by simp only [tbase, tdone]; deck_eq) rfl)))
  have h1 : Fits env (move 0 4 2) (pile 0 (send rd) (pile 0 (send (wr, m)) (pile 0 (send rest) (tdone t ok r))))
      (pile 4 (send rd) (pile 0 (send (wr, m)) (pile 0 (send rest) (tdone t ok r))))
      (42 * size rd) := fits_move (by decide) (by decide) (send rd) env _
  have h2 : Fits env (pack 4) (pile 4 (send rd) (pile 4 (send (t.h, ok))
      (pile 0 (send (wr, m)) (tbase t rest r))))
      (pile 4 (send (rd, t.h, ok)) (pile 0 (send (wr, m)) (tbase t rest r))) 1 :=
    fits_pack (send rd) (send (t.h, ok)) _ 4 env
  have hA : Fits env (stepA cmp) (pile 0 (send rd) (pile 0 (send (wr, m)) (pile 0 (send rest) (tdone t ok r))))
      (tdeck rest (t.act wr m) (ok && (rd == t.h)) r) _ :=
    h1.join ((h2.cast' (by simp only [tbase, tdone]; deck_eq) rfl).join
      ((fits_pair (c := fun _ => Prog.pass) hB).cast' (by deck_eq) rfl))
  refine (fits_pair (c := fun _ => Prog.pass) hA).mono ?_
  have hz : C * (size (wr, rd, t.h, ok) + 1) ≤ C * (size (rd, wr, m) + size t.h + popSize t m + 4) :=
    Nat.mul_le_mul_left _ (by simp only [size_prod, size_bit]; omega)
  have hx : size wr + size rd ≤ size (rd, wr, m) := by simp only [size_prod]; omega
  simp only [stepCost, Nat.add_mul]
  omega

/-! ## The loop over the column -/

def body (cmp : Cmd) : Cmd := splitRoot 0 (fun _ => .pass) ((step cmp).join (.again 0))

/-- Cost of the loop. -/
def loopCost (C : ℕ) : Tp → List Cell → ℕ
  | _, [] => 5
  | t, x :: rest => stepCost C x t + 7 + loopCost C (t.act x.2.1 x.2.2) rest

theorem fits_loop (cmp : Cmd) (C : ℕ)
    (hcmp : ∀ (z : ℕ × ℕ × ℕ × Bool) (env : Env),
      Fits.value env cmp 4 (send z) (send (cmpF z)) (C * (size z + 1)))
    (E : Env) (r : Deck) : ∀ (cells : List Cell) (t : Tp) (ok : Bool),
      Fits (body cmp :: E) (body cmp) (tdeck cells t ok r)
        (tdone (runT t ok cells).1 (runT t ok cells).2 r) (loopCost C t cells) := by
  intro cells
  induction cells with
  | nil =>
    intro t ok
    exact (fits_bit (b := false) (c := fun _ => Prog.pass) (i := 0)
      (Fits.pass (env := body cmp :: E) (tdone t ok r))).mono (by simp only [loopCost]; omega)
  | cons x rest ih =>
    intro t ok
    have hs := fits_step cmp C hcmp (body cmp :: E) x rest t ok r
    have hl := Fits.again0 (ih (t.act x.2.1 x.2.2) (ok && (x.1 == t.h)))
    refine (fits_pair (c := fun _ => Prog.pass) (hs.join hl)).mono ?_
    simp only [loopCost]
    omega

theorem size_le_of_tpLe {B : ℕ} {n : ℕ} (h : n ≤ B) : size n ≤ 2 * B + 1 := by
  rw [size_nat]; omega

theorem popSize_le {B : ℕ} {t : Tp} (ht : TpLe B t) (m : Mv) : popSize t m ≤ 2 * B + 1 := by
  cases m with
  | none => simp [popSize]
  | some b =>
    cases b with
    | false => exact size_le_of_tpLe (headD_le ht.1)
    | true => exact size_le_of_tpLe (headD_le ht.2.2)

theorem loopCost_le (C B : ℕ) (cells : List Cell) (hc : ∀ x ∈ cells, x.2.1 ≤ B) :
    ∀ t, TpLe B t → loopCost C t cells ≤ (C + 200) * (size cells + cells.length * (4 * B + 7) + 5) := by
  induction cells with
  | nil =>
    intro t _
    simp only [loopCost, size_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
    nlinarith
  | cons x rest ih =>
    intro t ht
    have hx := hc x List.mem_cons_self
    have hr := ih (fun y hy => hc y (List.mem_cons_of_mem _ hy)) (t.act x.2.1 x.2.2)
      (tpLe_act ht hx _)
    have hh := size_le_of_tpLe ht.2.1
    have hp := popSize_le ht x.2.2
    have h1 : (C + 200) * (size x + size t.h + popSize t x.2.2 + 4) ≤
        (C + 200) * (size x + 4 * B + 6) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (C + 200) * (size (x :: rest) + (x :: rest).length * (4 * B + 7) + 5) =
        (C + 200) * (size x + 4 * B + 6) +
          (C + 200) * (size rest + rest.length * (4 * B + 7) + 5) + (C + 200) * 2 := by
      simp only [size_cons, List.length_cons]; ring
    rw [h2]
    simp only [loopCost, stepCost]
    omega

/-! ## Setup, teardown, and the task -/

/-- Input of the tape pass. -/
def tapeIn (t : Tp) (cells : List Cell) : Tree := send ((t.h, true), t.L, t.R, cells)

def setup : Cmd :=
  splitRoot 0 (fun _ => .pass) ((move 0 4 2).join (splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join (splitRoot 0 (fun _ => .pass) (move 0 3 2)))))

theorem fits_setup (env : Env) (t : Tp) (cells : List Cell) (r : Deck) :
    Fits env setup (pile 0 (tapeIn t cells) r) (tdeck cells t true r)
      (42 * (size t.h + size t.L + size t.R) + 120) := by
  have m3 : Fits env (move 0 3 2) (pile 0 (send t.R) (pile 0 (send cells)
      (pile 1 (send t.L) (pile 4 (send (t.h, true)) r))))
      (tdeck cells t true r) (42 * size t.R) :=
    (fits_move (by decide) (by decide) (send t.R) env _).cast' rfl (by simp only [tdeck]; deck_eq)
  have s3 := fits_pair (c := fun _ => Prog.pass) m3
  have m1 : Fits env (move 0 1 2) (pile 0 (send t.L) (pile 0 (send (t.R, cells))
      (pile 4 (send (t.h, true)) r)))
      (pile 1 (send t.L) (pile 0 (send (t.R, cells)) (pile 4 (send (t.h, true)) r)))
      (42 * size t.L) := fits_move (by decide) (by decide) (send t.L) env _
  have s1 := fits_pair (c := fun _ => Prog.pass) (m1.join (s3.cast' (by deck_eq) rfl))
  have m4 : Fits env (move 0 4 2) (pile 0 (send (t.h, true)) (pile 0 (send (t.L, t.R, cells)) r))
      (pile 4 (send (t.h, true)) (pile 0 (send (t.L, t.R, cells)) r))
      (42 * size (t.h, true)) := fits_move (by decide) (by decide) (send (t.h, true)) env _
  have s4 := fits_pair (c := fun _ => Prog.pass) (m4.join (s1.cast' (by deck_eq) rfl))
  refine s4.mono ?_
  simp only [size_prod, size_bit]
  omega

def teardown : Cmd :=
  (discard 1).join ((discard 3).join (splitRoot 4 (fun _ => .pass) ((discard 4).join (move 4 0 2))))

theorem fits_teardown (env : Env) (t : Tp) (ok : Bool) (r : Deck) :
    Fits env teardown (tdone t ok r) (pile 0 (send ok) r)
      (17 * (size t.L + size t.R + size t.h) + 80) := by
  have d1 : Fits env (discard 1) (tdone t ok r) (pile 3 (send t.R) (pile 4 (send (t.h, ok)) r))
      (17 * size t.L) := fits_discard 1 (send t.L) env _
  have d3 : Fits env (discard 3) (pile 3 (send t.R) (pile 4 (send (t.h, ok)) r))
      (pile 4 (send (t.h, ok)) r) (17 * size t.R) := fits_discard 3 (send t.R) env _
  have d4 : Fits env (discard 4) (pile 4 (send t.h) (pile 4 (send ok) r)) (pile 4 (send ok) r)
      (17 * size t.h) := fits_discard 4 (send t.h) env _
  have m : Fits env (move 4 0 2) (pile 4 (send ok) r) (pile 0 (send ok) r) (42 * size ok) :=
    fits_move (by decide) (by decide) (send ok) env r
  have s := fits_pair (c := fun _ => Prog.pass) (d4.join m)
  refine (d1.join (d3.join s)).mono ?_
  simp only [size_bit]
  omega

/-- Domain of the tape pass: all symbols of the tape and all written symbols are `≤ B`. -/
def TapeOK (p : Tp × List Cell × ℕ) : Prop := TpLe p.2.2 p.1 ∧ ∀ x ∈ p.2.1, x.2.1 ≤ p.2.2

/-- Budget of the tape pass. -/
def tapeBudget (p : Tp × List Cell × ℕ) : ℕ :=
  size p.2.1 + (p.2.1.length + tlen p.1 + 2) * (p.2.2 + 1)

theorem tape_task : Task (fun p : {p : Tp × List Cell × ℕ // TapeOK p} => tapeBudget p.val)
    (fun p => tapeIn p.val.1 p.val.2.1) (fun p => send (colOK p.val.1 p.val.2.1)) := by
  obtain ⟨C, hC⟩ := Task.atRegister easy_cmpF
  obtain ⟨cmp, hcmp⟩ := hC 4
  refine ⟨setup.join ((Prog.tie (body cmp)).join teardown), 10 * (C + 300), ?_⟩
  rintro ⟨⟨t, cells, B⟩, ⟨ht, hc⟩⟩ env r
  dsimp only at ht hc
  have h1 := fits_setup env t cells r
  have h2 := Fits.tie (fits_loop cmp C hcmp env r cells t true)
  have h3 := fits_teardown env (runT t true cells).1 (runT t true cells).2 r
  have hall := h1.join (h2.join h3)
  rw [runT_snd, Bool.true_and] at hall
  refine hall.mono ?_
  -- arithmetic
  obtain ⟨hf, hlen⟩ := runT_bound cells hc t true ht
  set t' := (runT t true cells).1
  have hloop := loopCost_le C B cells hc t ht
  set X := (cells.length + tlen t + 2) * (B + 1) with hX
  have hmul : ∀ a, a ≤ cells.length + tlen t + 2 → a * (2 * B + 2) ≤ 2 * X := by
    intro a ha
    have : a * (B + 1) ≤ (cells.length + tlen t + 2) * (B + 1) := Nat.mul_le_mul_right _ ha
    nlinarith
  have hL := size_natList_le t.L ht.1
  have hR := size_natList_le t.R ht.2.2
  have hL' := size_natList_le t'.L hf.1
  have hR' := size_natList_le t'.R hf.2.2
  have hh := size_le_of_tpLe ht.2.1
  have hh' := size_le_of_tpLe hf.2.1
  have aL := hmul t.L.length (by simp only [tlen] at *; omega)
  have aR := hmul t.R.length (by simp only [tlen] at *; omega)
  have aL' := hmul t'.L.length (by simp only [tlen] at *; omega)
  have aR' := hmul t'.R.length (by simp only [tlen] at *; omega)
  have aB : 2 * B + 2 ≤ 2 * X := by
    have := hmul 1 (by omega); omega
  have an : cells.length * (4 * B + 7) ≤ 7 * X := by
    have : cells.length * (B + 1) ≤ X := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  set Q := size cells + X + 1 with hQ
  have hl2 : (C + 200) * (size cells + cells.length * (4 * B + 7) + 5) ≤ 7 * (C * Q) + 1400 * Q := by
    have : (C + 200) * (size cells + cells.length * (4 * B + 7) + 5) ≤ (C + 200) * (7 * Q) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have hrhs : 10 * (C + 300) * (tapeBudget ((t, cells, B) : Tp × List Cell × ℕ) + 1) =
      10 * (C * Q) + 3000 * Q := by
    simp only [tapeBudget, hQ, hX]; ring
  rw [hrhs]
  omega

end P1Hier
