import P1NTime.TapeGeometry

namespace P1NTime.AstraNTime.Composite

open C1Challenge Turing

variable (D V : Machine)

noncomputable def prep (s : Setup) (src : Tape (Sym D V)) (z : List Bool) : Conf (machine D V) :=
  pack D V (.inl s) src (pending D z) (pending V z)

noncomputable def stopped (src : Tape (Sym D V)) (z : List Bool) : Conf (machine D V) :=
  pack D V (.inr (.inl D.initialState)) src (D.init z).tapes (V.init z).tapes

theorem init_prep (x : List Bool) :
    (machine D V).init x = prep D V .scan (cursor (letter D V) [] x) [] := by
  apply NTimeGuards.cfg_ext
  · rfl
  · funext k
    cases k with
    | none => rfl
    | some k =>
      cases k with
      | inl k =>
        change Tape.mk₁ [] = (pending D [] k).map (intoD D V)
        rw [pending_nil, Tape.map_mk₁, List.map_nil]
      | inr k =>
        change Tape.mk₁ [] = (pending V [] k).map (intoV D V)
        rw [pending_nil, Tape.map_mk₁, List.map_nil]

theorem letter_ne_blank (b : Bool) : letter D V b ≠ default :=
  fun h => D.input_ne_blank b (congrArg Prod.fst h)

variable (src : Tape (Sym D V)) (z : List Bool)

theorem idle_result (s : Setup) (op : Op (Sym D V)) :
    result D V src (pending D z) (pending V z)
      (idle D V (.inl s) op (heads (pending D z)) (heads (pending V z))) =
    prep D V s (act src op) z := by
  simp only [result, idle, update_hold, prep]

theorem push_result (s : Setup) (b : Bool) (op : Op (Sym D V)) :
    result D V src (pending D z) (pending V z)
      (both D V (.inl s) op (heads (pending D z)) (heads (pending V z)) (letter D V b) .left) =
    prep D V s (act src op) (b :: z) := by
  simp only [result, both, letter, update_push, prep]

theorem stop_result :
    result D V src (pending D z) (pending V z)
      (both D V (.inr (.inl D.initialState)) (src.head, .stay)
        (heads (pending D z)) (heads (pending V z))
        (heads (pending D z) D.inputTape, heads (pending V z) V.inputTape) .right) =
    stopped D V src z := by
  simp only [result, both, act_hold, update_install, stopped]

theorem next_idle {s s' : Setup} {op : Op (Sym D V)}
    (h : program D V (.inl s) src.head (heads (pending D z)) (heads (pending V z)) =
      [idle D V (.inl s') op (heads (pending D z)) (heads (pending V z))])
    (y : Conf (machine D V)) :
    (machine D V).Next (prep D V s src z) y ↔ y = prep D V s' (act src op) z := by
  change (machine D V).Next (pack D V (.inl s) src (pending D z) (pending V z)) y ↔ _
  simpa only [idle_result] using next_one D V (.inl s) src (pending D z) (pending V z) h y

theorem next_push {s s' : Setup} {b : Bool} {op : Op (Sym D V)}
    (h : program D V (.inl s) src.head (heads (pending D z)) (heads (pending V z)) =
      [both D V (.inl s') op (heads (pending D z)) (heads (pending V z)) (letter D V b) .left])
    (y : Conf (machine D V)) :
    (machine D V).Next (prep D V s src z) y ↔ y = prep D V s' (act src op) (b :: z) := by
  change (machine D V).Next (pack D V (.inl s) src (pending D z) (pending V z)) y ↔ _
  simpa only [push_result] using next_one D V (.inl s) src (pending D z) (pending V z) h y

theorem scan_bit (hn : src.head ≠ default) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .scan src z) y ↔ y = prep D V .scan (src.move .right) z := by
  simpa only [act_right] using
    next_idle D V src z (s := .scan) (s' := .scan) (op := (src.head, .right))
      (by simp only [program, ite_eq_right hn]) y

theorem scan_end (hb : src.head = default) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .scan src z) y ↔ y = prep D V .copy (src.move .left) z := by
  simpa only [act_left] using
    next_idle D V src z (s := .scan) (s' := .copy) (op := (src.head, .left))
      (by simp only [program, ite_eq_left hb]) y

theorem copy_bit (b : Bool) (h : src.head = letter D V b) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .copy src z) y ↔
      y = prep D V .copy (src.move .left) (b :: z) := by
  have hn : src.head ≠ default := h ▸ letter_ne_blank D V b
  simpa only [act_left] using
    next_push D V src z (s := .copy) (s' := .copy) (b := b) (op := (src.head, .left))
      (by simp only [program, ite_eq_right hn, h]) y

theorem copy_end (hb : src.head = default) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .copy src z) y ↔
      y = prep D V .guess (src.move .right) (false :: z) := by
  simpa only [act_right] using
    next_push D V src z (s := .copy) (s' := .guess) (b := false) (op := (src.head, .right))
      (by simp only [program, ite_eq_left hb]) y

theorem mark_bit (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .mark src z) y ↔ y = prep D V .guess src (true :: z) := by
  simpa only [act_hold] using
    next_push D V src z (s := .mark) (s' := .guess) (b := true) (op := (src.head, .stay)) rfl y

theorem guess_end (hb : src.head = default) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .guess src z) y ↔ y = stopped D V src z := by
  let d := heads (pending D z)
  let v := heads (pending V z)
  have h : program D V (.inl .guess) src.head d v =
      [both D V (.inr (.inl D.initialState)) (src.head, .stay) d v
        (d D.inputTape, v V.inputTape) .right] := by simp only [program, ite_eq_left hb]
  change (machine D V).Next (pack D V (.inl .guess) src (pending D z) (pending V z)) y ↔ _
  simpa only [d, v, stop_result] using next_one D V (.inl .guess) src (pending D z) (pending V z) h y

private theorem three_results {A B : Type} (f : A → B) (x : B) (a b c : A) :
    (∃ u ∈ [a, b, c], x = f u) ↔ x = f a ∨ x = f b ∨ x = f c := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hm : u = a ∨ u = b ∨ u = c := by simpa using hu
    rcases hm with rfl | rfl | rfl
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · rintro (h | h | h)
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩
    · exact ⟨c, by simp, h⟩

theorem guess_options (hn : src.head ≠ default) (y : Conf (machine D V)) :
    (machine D V).Next (prep D V .guess src z) y ↔
      y = stopped D V src z ∨
      y = prep D V .mark (act src (default, .right)) (false :: z) ∨
      y = prep D V .mark (act src (default, .right)) (true :: z) := by
  change (machine D V).Next (pack D V (.inl .guess) src (pending D z) (pending V z)) y ↔ _
  rw [next_pack]
  simp only [program, ite_eq_right hn, three_results, stop_result, push_result]

end P1NTime.AstraNTime.Composite
