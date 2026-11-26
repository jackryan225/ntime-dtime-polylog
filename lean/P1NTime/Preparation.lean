import P1NTime.PrepMoves

namespace P1NTime.AstraNTime.Composite

open C1Challenge Turing

/-- Future choices are listed in the order in which they will be made. -/
def CanFinish (n : ℕ) (P : List Bool → Prop) (w : List Bool) : Prop :=
  ∃ u : List Bool, u.length ≤ n ∧ P (u.reverse ++ w)

theorem can_zero (P : List Bool → Prop) (w : List Bool) : CanFinish 0 P w ↔ P w := by
  constructor
  · rintro ⟨u, hu, h⟩
    cases u with
    | nil => exact h
    | cons b r => simp only [List.length_cons] at hu; omega
  · exact fun h => ⟨[], le_rfl, h⟩

theorem can_succ (n : ℕ) (P : List Bool → Prop) (w : List Bool) :
    CanFinish (n + 1) P w ↔ P w ∨ CanFinish n P (false :: w) ∨ CanFinish n P (true :: w) := by
  have extend (b : Bool) : CanFinish n P (b :: w) → CanFinish (n + 1) P w := by
    rintro ⟨u, hu, h⟩
    exact ⟨b :: u, Nat.succ_le_succ hu,
      by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h⟩
  constructor
  · rintro ⟨u, hu, hp⟩
    cases u with
    | nil => exact Or.inl hp
    | cons b r =>
      have hlen : r.length ≤ n := by simp only [List.length_cons] at hu; omega
      have h : CanFinish n P (b :: w) :=
        ⟨r, hlen, by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hp⟩
      cases b with
      | false => exact Or.inr (Or.inl h)
      | true => exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨[], Nat.zero_le _, h⟩
    · exact extend false h
    · exact extend true h

theorem can_start (n : ℕ) (P : List Bool → Prop) :
    CanFinish n P [] ↔ ∃ w : List Bool, w.length ≤ n ∧ P w := by
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u.reverse, by simpa only [List.length_reverse] using hu,
      by simpa only [List.append_nil] using h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w.reverse, by simpa only [List.length_reverse] using hw,
      by simpa only [List.reverse_reverse, List.append_nil] using h⟩

/-- Outcomes compose even when two listed successor configurations coincide. -/
theorem three_outcomes {M : NMachine} {c a b d : Conf M} {T : ℕ} {p q r : Prop}
    (steps : ∀ y, M.Next c y ↔ y = a ∨ y = b ∨ y = d)
    (ha : Outcome M a T p) (hb : Outcome M b T q) (hd : Outcome M d T r) :
    Outcome M c (T + 1) (p ∨ q ∨ r) := by
  let A (v : Conf M) := ∃ t e, M.Reach v t e ∧ M.Halted e ∧ M.accept e.q = true
  have canonical {v : Conf M} {s : Prop} (h : Outcome M v T s) : Outcome M v T (A v) :=
    ⟨h.bound, Iff.rfl⟩
  have children (y : Conf M) (hy : M.Next c y) : Outcome M y T (A y) := by
    rcases (steps y).mp hy with h | h | h
    · exact h ▸ canonical ha
    · exact h ▸ canonical hb
    · exact h ▸ canonical hd
  have sa : M.Next c a := (steps a).mpr (Or.inl rfl)
  have sb : M.Next c b := (steps b).mpr (Or.inr (Or.inl rfl))
  have sd : M.Next c d := (steps d).mpr (Or.inr (Or.inr rfl))
  apply (Outcome.choice (P := A) ⟨a, sa⟩ children).congr
  constructor
  · rintro ⟨y, hy, h⟩
    rcases (steps y).mp hy with e | e | e
    · exact Or.inl (ha.accepts.mp (e ▸ h))
    · exact Or.inr (Or.inl (hb.accepts.mp (e ▸ h)))
    · exact Or.inr (Or.inr (hd.accepts.mp (e ▸ h)))
  · rintro (h | h | h)
    · exact ⟨a, sa, ha.accepts.mpr h⟩
    · exact ⟨b, sb, hb.accepts.mpr h⟩
    · exact ⟨d, sd, hd.accepts.mpr h⟩

theorem withGuess_cons (b : Bool) (w x : List Bool) :
    withGuess (b :: w) x = true :: b :: withGuess w x := by simp [withGuess]

variable (D V : Machine)

theorem guess_outcome (x : List Bool) (T : ℕ) (P : List Bool → Prop)
    (done : ∀ w : List Bool, w.length ≤ x.length → ∀ src : Tape (Sym D V),
      Outcome (machine D V) (stopped D V src (withGuess w x)) T (P w))
    (rest w : List Bool) (room : w.length + rest.length ≤ x.length) :
    Outcome (machine D V) (prep D V .guess (cursor (letter D V) [] rest) (withGuess w x))
      (T + 2 * rest.length + 1) (CanFinish rest.length P w) := by
  induction rest generalizing w with
  | nil =>
    let src := cursor (letter D V) [] []
    have hw : w.length ≤ x.length := by simpa only [List.length_nil, Nat.add_zero] using room
    have h := Outcome.step (guess_end D V src (withGuess w x) (cursor_head_nil (letter D V) []))
      (done w hw src)
    simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, can_zero] using h
  | cons a rest ih =>
    let src := cursor (letter D V) [] (a :: rest)
    let tailSrc := cursor (letter D V) [] rest
    let z := withGuess w x
    have hw : w.length ≤ x.length := by simp only [List.length_cons] at room; omega
    have hstop : Outcome (machine D V) (stopped D V src z)
        (T + 2 * rest.length + 1 + 1) (P w) := (done w hw src).mono (by omega)
    have branch (b : Bool) : Outcome (machine D V) (prep D V .mark tailSrc (b :: z))
        (T + 2 * rest.length + 1 + 1) (CanFinish rest.length P (b :: w)) := by
      have fit : (b :: w).length + rest.length ≤ x.length := by
        simp only [List.length_cons] at room ⊢
        omega
      have cont : Outcome (machine D V) (prep D V .guess tailSrc (true :: b :: z))
          (T + 2 * rest.length + 1) (CanFinish rest.length P (b :: w)) := by
        simpa only [withGuess_cons] using ih (w := b :: w) fit
      exact Outcome.step (mark_bit D V tailSrc (b :: z)) cont
    have hn : src.head ≠ default := letter_ne_blank D V a
    have he : act src (default, .right) = tailSrc := erase_right (letter D V) a rest
    have options (y : Conf (machine D V)) :
        (machine D V).Next (prep D V .guess src z) y ↔
          y = stopped D V src z ∨ y = prep D V .mark tailSrc (false :: z) ∨
            y = prep D V .mark tailSrc (true :: z) := by
      simpa only [he] using guess_options D V src z hn y
    have h := three_outcomes options hstop (branch false) (branch true)
    refine (h.congr (can_succ rest.length P w).symm).mono ?_
    simp only [List.length_cons]
    omega

theorem copy_outcome (L R : List Bool) {T : ℕ} {p : Prop}
    (finish : Outcome (machine D V)
      (prep D V .guess (cursor (letter D V) [] (L.reverse ++ R)) (false :: (L.reverse ++ R))) T p) :
    Outcome (machine D V) (prep D V .copy (back (letter D V) L R) R) (T + L.length + 1) p := by
  induction L generalizing R with
  | nil =>
    have cont : Outcome (machine D V)
        (prep D V .guess ((back (letter D V) [] R).move .right) (false :: R)) T p := by
      simpa only [List.reverse_nil, List.nil_append, back_right] using finish
    have h := Outcome.step
      (copy_end D V (back (letter D V) [] R) R (back_head_nil (letter D V) R)) cont
    simpa only [List.length_nil, Nat.add_zero] using h
  | cons b L ih =>
    have finalState : Outcome (machine D V)
        (prep D V .guess (cursor (letter D V) [] (L.reverse ++ b :: R))
          (false :: (L.reverse ++ b :: R))) T p := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using finish
    have cont := ih (R := b :: R) finalState
    have hh : (back (letter D V) (b :: L) R).head = letter D V b := by
      rw [back_cons, cursor_head]
    have nextStep (y : Conf (machine D V)) :
        (machine D V).Next (prep D V .copy (back (letter D V) (b :: L) R) R) y ↔
          y = prep D V .copy (back (letter D V) L (b :: R)) (b :: R) := by
      simpa only [back_left] using copy_bit D V (back (letter D V) (b :: L) R) R b hh y
    refine (Outcome.step nextStep cont).mono ?_
    simp only [List.length_cons]
    omega

theorem scan_outcome (L R : List Bool) {T : ℕ} {p : Prop}
    (finish : Outcome (machine D V)
      (prep D V .copy (back (letter D V) (R.reverse ++ L) []) []) T p) :
    Outcome (machine D V) (prep D V .scan (cursor (letter D V) L R) []) (T + R.length + 1) p := by
  induction R generalizing L with
  | nil =>
    have cont : Outcome (machine D V)
        (prep D V .copy ((cursor (letter D V) L []).move .left) []) T p := by
      simpa only [List.reverse_nil, List.nil_append, back] using finish
    have h := Outcome.step
      (scan_end D V (cursor (letter D V) L []) [] (cursor_head_nil (letter D V) L)) cont
    simpa only [List.length_nil, Nat.add_zero] using h
  | cons b R ih =>
    have finalState : Outcome (machine D V)
        (prep D V .copy (back (letter D V) (R.reverse ++ b :: L) []) []) T p := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using finish
    have cont := ih (L := b :: L) finalState
    have nextStep (y : Conf (machine D V)) :
        (machine D V).Next (prep D V .scan (cursor (letter D V) L (b :: R)) []) y ↔
          y = prep D V .scan (cursor (letter D V) (b :: L) R) [] := by
      simpa only [cursor_right] using
        scan_bit D V (cursor (letter D V) L (b :: R)) [] (letter_ne_blank D V b) y
    refine (Outcome.step nextStep cont).mono ?_
    simp only [List.length_cons]
    omega

theorem prep_outcome (x : List Bool) (T : ℕ) (P : List Bool → Prop)
    (done : ∀ w : List Bool, w.length ≤ x.length → ∀ src : Tape (Sym D V),
      Outcome (machine D V) (stopped D V src (withGuess w x)) T (P w)) :
    Outcome (machine D V) ((machine D V).init x) (T + 4 * x.length + 3)
      (∃ w : List Bool, w.length ≤ x.length ∧ P w) := by
  let G := T + 2 * x.length + 1
  have hg := guess_outcome D V x T P done x [] (by simp)
  have hg' : Outcome (machine D V)
      (prep D V .guess (cursor (letter D V) [] (x.reverse.reverse ++ []))
        (false :: (x.reverse.reverse ++ []))) G (CanFinish x.length P []) := by
    simpa only [G, withGuess, List.flatMap_nil, List.nil_append, List.reverse_reverse,
      List.append_nil] using hg
  have hc : Outcome (machine D V) (prep D V .copy (back (letter D V) (x.reverse ++ []) []) [])
      (G + x.reverse.length + 1) (CanFinish x.length P []) := by
    simpa only [List.append_nil] using copy_outcome D V x.reverse [] hg'
  have hs := scan_outcome D V [] x hc
  rw [init_prep]
  refine (hs.mono ?_).congr (can_start x.length P)
  dsimp only [G]
  rw [List.length_reverse]
  omega

end P1NTime.AstraNTime.Composite
