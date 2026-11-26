import P1C1U.RowEncoding

namespace P1C1U.AstraC1U.Rows

open C1Challenge P1Hier
noncomputable section

abbrev Represents (M : NMachine) (c : Conf M) (ts : ℕ → Tp) :=
  ∀ k : M.K, absT (base M) (ts (eK (base M) k)) = c.tapes k

abbrev GoodTapes (M : NMachine) (ts : ℕ → Tp) :=
  ∀ k : M.K, Good (base M) (ts (eK (base M) k))

def Valid (M : NMachine) (c : Conf M) (ts : ℕ → Tp) (τ : List Entry) : Prop :=
  (∀ e ∈ τ, e ∈ (ncode M).table) ∧ chainOK (encQ (base M) c.q) τ = true ∧
    ∀ k < Fintype.card M.K, colOK (ts k) (col k τ) = true

def readCell (M : NMachine) (c : Conf M) (o : Out M) (k : ℕ) : Cell :=
  (cellsOf (base M) (M.scanned c) (some o)).getD k (0, 0, none)

def nextTape (M : NMachine) (c : Conf M) (ts : ℕ → Tp) (o : Out M) (k : ℕ) : Tp :=
  (ts k).act (readCell M c o k).2.1 (readCell M c o k).2.2

theorem readCell_at (M : NMachine) (c : Conf M) (o : Out M) (k : M.K) :
    readCell M c o (eK (base M) k) =
      (encG (base M) ((c.tapes k).head), encG (base M) (o.2.1 k), encMv (o.2.2 k)) :=
  cellsOf_getD (base M) (M.scanned c) (some o) k (0, 0, none)

theorem represents_next {M : NMachine} {c : Conf M} {ts : ℕ → Tp} (rep : Represents M c ts)
    (o : Out M) : Represents M (M.apply c o) (nextTape M c ts o) := by
  intro k
  unfold nextTape
  rw [readCell_at M c o k]
  exact (absT_act (base M) (ts (eK (base M) k)) (o.2.1 k) (o.2.2 k)).trans
    (congrArg (fun t : Turing.Tape M.Γ => (o.2.2 k).apply (t.write (o.2.1 k))) (rep k))

theorem good_next {M : NMachine} {ts : ℕ → Tp} (good : GoodTapes M ts)
    (c : Conf M) (o : Out M) : GoodTapes M (nextTape M c ts o) := by
  intro k
  unfold nextTape
  rw [readCell_at M c o k]
  exact good_act (base M) _ (good k) _ _

theorem valid_halt {M : NMachine} {c : Conf M} {ts : ℕ → Tp}
    (rep : Represents M c ts) (good : GoodTapes M ts) (hh : M.Halted c) (rest : List Entry) :
    Valid M c ts (row M c none :: rest) ↔ rest = [] ∧ M.accept c.q = true := by
  constructor
  · intro h
    have hc := h.2.1
    simpa [row, chainOK, Bool.and_eq_true, List.isEmpty_iff] using hc
  · rintro ⟨rfl, ha⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      have he' := List.mem_singleton.mp he
      rw [he']
      exact row_mem_halt (M := M) hh
    · simp [row, chainOK, ha]
    · intro k hk
      simp only [col, List.map_cons, List.map_nil, colOK, Bool.and_true, beq_iff_eq]
      exact reads_ok (base M) c ts rep good none k hk _

theorem valid_step {M : NMachine} {c : Conf M} {ts : ℕ → Tp}
    (rep : Represents M c ts) (good : GoodTapes M ts) {o : Out M}
    (ho : o ∈ M.code c.q (M.scanned c)) (rest : List Entry) :
    Valid M c ts (row M c (some o) :: rest) ↔
      Valid M (M.apply c o) (nextTape M c ts o) rest := by
  constructor
  · rintro ⟨ht, hch, hcol⟩
    refine ⟨fun e he => ht e (List.Mem.tail _ he), ?_, ?_⟩
    · simpa [row, chainOK, NMachine.apply] using hch
    · intro k hk
      have hc := hcol k hk
      simp only [col, List.map_cons, colOK, Bool.and_eq_true] at hc
      exact hc.2
  · rintro ⟨ht, hch, hcol⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact row_mem_some ho
      · exact ht e he
    · simpa [row, chainOK, NMachine.apply] using hch
    · intro k hk
      simp only [col, List.map_cons, colOK, Bool.and_eq_true, beq_iff_eq]
      exact ⟨reads_ok (base M) c ts rep good (some o) k hk _, hcol k hk⟩

theorem path_of_valid (M : NMachine) : ∀ (τ : List Entry) (c : Conf M) (ts : ℕ → Tp),
    Represents M c ts → GoodTapes M ts → Valid M c ts τ →
    ∃ os : List (Out M), τ = rows M c os ∧ M.Run c os ∧
      M.Halted (M.after c os) ∧ M.accept (M.after c os).q = true
  | [], _, _, _, _, h => by
    have hc : false = true := h.2.1
    cases hc
  | e :: rest, c, ts, rep, good, h => by
    obtain ⟨p, he⟩ := checked_head M c ts e rest rep good (h.1 e (List.Mem.head _)) h.2.1 h.2.2
    cases hp : pick (M.code c.q (M.scanned c)) p with
    | none =>
      have hh : M.Halted c := (pick_none_iff _ p).mp hp
      rw [hp] at he
      subst e
      obtain ⟨rfl, ha⟩ := (valid_halt rep good hh rest).mp h
      exact ⟨[], rfl, trivial, hh, ha⟩
    | some o =>
      have ho := pick_mem hp
      rw [hp] at he
      subst e
      have tail := (valid_step rep good ho rest).mp h
      obtain ⟨os, heq, hr, hh, ha⟩ := path_of_valid M rest (M.apply c o) (nextTape M c ts o)
        (represents_next rep o) (good_next good c o) tail
      exact ⟨o :: os, congrArg (List.cons (row M c (some o))) heq, ⟨ho, hr⟩, hh, ha⟩

theorem valid_of_path (M : NMachine) : ∀ (os : List (Out M)) (c : Conf M) (ts : ℕ → Tp),
    Represents M c ts → GoodTapes M ts → M.Run c os → M.Halted (M.after c os) →
    M.accept (M.after c os).q = true → Valid M c ts (rows M c os)
  | [], _, _, rep, good, _, hh, ha => (valid_halt rep good hh []).mpr ⟨rfl, ha⟩
  | o :: os, c, ts, rep, good, hr, hh, ha =>
    (valid_step rep good hr.1 _).mpr (valid_of_path M os (M.apply c o) (nextTape M c ts o)
      (represents_next rep o) (good_next good c o) hr.2 hh ha)

/-- The table checker succeeds exactly on the transcript of an accepting transition sequence
within its clock. -/
theorem check_iff (M : NMachine) (x : List Bool) (T : ℕ) (τ : List Entry) :
    P1Hier.Check (ncode M) x T τ ↔ ∃ a : M.AccComp x,
      τ = rows M (M.init x) a.val ∧ a.val.length ≤ T := by
  let ts : ℕ → Tp := (ncode M).start x
  have rep : Represents M (M.init x) ts := by
    intro k
    change absT (base M) ((P1Hier.code (base M)).start x (eK (base M) k)) = ((base M).init x).tapes k
    rw [start_eq, absT_ofList]
    simp only [Machine.init]
    split_ifs <;> rfl
  have good : GoodTapes M ts := by
    intro k
    change Good (base M) ((P1Hier.code (base M)).start x (eK (base M) k))
    rw [start_eq]
    exact good_ofList (base M) _
  change (τ.length ≤ T + 1 ∧ Valid M (M.init x) ts τ) ↔ _
  constructor
  · rintro ⟨hl, h⟩
    obtain ⟨os, he, hr, hh, ha⟩ := path_of_valid M τ (M.init x) ts rep good h
    refine ⟨⟨os, hr, hh, ha⟩, he, ?_⟩
    change os.length ≤ T
    rw [he, length_rows] at hl
    omega
  · rintro ⟨a, rfl, hl⟩
    refine ⟨?_, valid_of_path M a.val (M.init x) ts rep good a.property.1 a.property.2.1 a.property.2.2⟩
    rw [length_rows]
    omega

end
end P1C1U.AstraC1U.Rows

#print axioms P1C1U.AstraC1U.Rows.check_iff
