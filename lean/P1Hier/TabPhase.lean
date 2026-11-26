import P1Hier.EasyBits
import OAI.Computability.IntegerMultiplication.Code.FoldLeft

/-!
# P1Hier.TabPhase: "every row is a table entry" as a stack task

* `foldKeep`: a left fold whose physical state is `(y, z)`, `y` kept unchanged.
* `findTask`: is the bit string `s` the code of some entry of `table`? cost `(size table+1)(size s+4)`.
* `memTask`: `e ∈ table`, cost `O((size table+1)² + size e)` (guard on code lengths, then `findTask`).
* `allMemTask`: `∀ e ∈ τ, e ∈ table`, cost `O(|τ| (size table+1)² + size τ)`.
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Folds with a fixed physical companion -/

theorem foldKeep {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z] (next : Y → Z → X → Z)
    (a : Y → X → ℕ)
    (h : Task (fun t : X × Y × Z => a t.2.1 t.1) send (fun t => send (t.2.1, next t.2.1 t.2.2 t.1))) :
    Task (fun i : List X × Y × Z => costSum (a i.2.1) i.1 + size i.1) send
      (fun i => send (i.2.1, i.1.foldl (next i.2.1) i.2.2)) := by
  have hs : Task (fun s : {s : X × Z × Y // True} => a s.val.2.2 s.val.1)
      (fun s => Tree.fork (send s.val.1) (send (s.val.2.2, s.val.2.1)))
      (fun s => send (s.val.2.2, next s.val.2.2 s.val.2.1 s.val.1)) :=
    (Task.on (b := fun t : X × Y × Z => a t.2.1 t.1) (p := send)
      (q := fun t => send (t.2.1, next t.2.1 t.2.2 t.1)) h
      (fun s : {s : X × Z × Y // True} => (s.val.1, s.val.2.2, s.val.2.1))).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hf := Task.foldLeft (X := X) (Z := Z) (Y := Y) (fun _ x => send x) (fun y z => send (y, z))
    next a (D := fun _ _ => True) hs
  refine (Task.on hf (fun i : List X × Y × Z => ⟨(i.1, i.2.2, i.2.1), fun _ _ => trivial⟩)).conform
    (fun i => ?_) (fun i => ?_) (fun _ => rfl)
  · show costSum (a i.2.1) i.1 + (Task.forest (fun x => send x) i.1).count = _
    rw [show (fun x : X => send x) = send from rfl, Task.forest_send]
    rfl
  · show Tree.fork (Task.forest (fun x => send x) i.1) (send (i.2.1, i.2.2)) = _
    rw [show (fun x : X => send x) = send from rfl, Task.forest_send]
    rfl

/-! ## Sizes dominate code lengths -/

theorem size_nat (n : ℕ) : size n = 2 * n + 1 := by
  change size (List.replicate n ()) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    have hu : size () = 1 := rfl
    simp only [List.replicate_succ, size_cons, ih, hu]
    omega

theorem size_bits (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [size_cons, size_bit, ih, List.length_cons]; omega

theorem length_serN_le (n : ℕ) : (serN n).length ≤ size n := by
  simp [serN, size_nat]; omega

theorem length_serL_le_size {α : Type*} [Codec α] {f : α → List Bool}
    (hf : ∀ a, (f a).length ≤ size a) (l : List α) : (serL f l).length ≤ size l := by
  induction l with
  | nil => simp [serL_nil]
  | cons a l ih =>
    rw [serL_cons, List.length_cons, List.length_append, size_cons]
    have := hf a
    omega

theorem length_serEntry_le_size (e : Entry) : (serEntry e).length ≤ size e := by
  rcases e with ⟨q, cells, r⟩
  have hcell : ∀ x : Cell, (serCell x).length ≤ size x := by
    rintro ⟨r, w, m⟩
    have h1 := length_serN_le r
    have h2 := length_serN_le w
    have h3 : (serMv m).length ≤ size m := by cases m <;> simp [serMv]
    simp only [serCell, List.length_append, size_prod]
    omega
  have h1 := length_serN_le q
  have h2 := length_serL_le_size hcell cells
  have h3 : (serRes r).length ≤ size r := by
    cases r with
    | inl q' => have := length_serN_le q'; simp [serRes]; omega
    | inr b => simp [serRes]
  simp only [serEntry, List.length_append, size_prod]
  omega

/-! ## Finding a code among the entries of a table -/

def findNext (s : List Bool) (z : Bool) (e : Entry) : Bool := z || decide (serEntry e = s)

theorem foldl_findNext (s : List Bool) (l : List Entry) (z : Bool) :
    l.foldl (findNext s) z = (z || decide (∃ e ∈ l, serEntry e = s)) := by
  induction l generalizing z with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih]
    by_cases h : serEntry e = s
    · simp [findNext, h]
    · have hx : (∃ e' ∈ e :: l, serEntry e' = s) ↔ (∃ e' ∈ l, serEntry e' = s) := by
        constructor
        · rintro ⟨e', he', hs'⟩
          rcases List.mem_cons.1 he' with rfl | h'
          · exact absurd hs' h
          · exact ⟨e', h', hs'⟩
        · rintro ⟨e', he', hs'⟩
          exact ⟨e', List.mem_cons_of_mem _ he', hs'⟩
      simp only [findNext, h, decide_false, Bool.or_false]
      rw [decide_eq_decide.2 hx]

theorem find_step : Task (fun t : Entry × List Bool × Bool => size t + 0) send
    (fun t => send (t.2.1, findNext t.2.1 t.2.2 t.1)) := by
  have h1 : Easy (fun t : Entry × List Bool × Bool => t.2.1) := Easy.fstCompose Easy.snd
  have h2 : Easy (fun t : Entry × List Bool × Bool => decide (serEntry t.1 = t.2.1)) :=
    ((Easy.fst.compose easy_serEntry).pair h1).compose easy_eqBits
  have h3 : Easy (fun t : Entry × List Bool × Bool => t.2.2) := Easy.sndCompose Easy.snd
  have h4 : Easy (fun t : Entry × List Bool × Bool => t.2.2 || decide (serEntry t.1 = t.2.1)) :=
    (h3.pair h2).compose (Easy.finite (fun q : Bool × Bool => q.1 || q.2))
  exact (h1.pair h4).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem findTask : Task (fun i : List Entry × List Bool × Bool =>
      costSum (fun e => size (e, i.2.1, i.2.2) + 0) i.1 + size i.1) send
    (fun i => send (i.2.1, i.2.2 || decide (∃ e ∈ i.1, serEntry e = i.2.1))) := by
  have h := foldKeep (X := Entry) (Y := List Bool) (Z := Bool) findNext
    (fun y e => size (e, y, false) + 0) ?_
  · refine (h.mono (b' := fun i : List Entry × List Bool × Bool =>
        costSum (fun e => size (e, i.2.1, i.2.2) + 0) i.1 + size i.1) (fun i => ?_)).conform
      (fun _ => rfl) (fun _ => rfl) (fun i => by rw [foldl_findNext])
    have : ∀ e : Entry, size (e, i.2.1, false) + 0 ≤ size (e, i.2.1, i.2.2) + 0 := by
      intro e; cases i.2.2 <;> simp
    have := costSum_le (s := i.1) (fun e _ => this e)
    omega
  · refine (find_step.mono (b' := fun t : Entry × List Bool × Bool => size (t.1, t.2.1, false) + 0)
      (fun t => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rcases t with ⟨e, s, z⟩
    cases z <;> simp

/-! ## Membership of one entry -/

/-- `e ∈ table`, decided through the bit codes. -/
def memB (table : List Entry) (e : Entry) : Bool := decide (∃ e' ∈ table, serEntry e' = serEntry e)

theorem memB_iff (table : List Entry) (e : Entry) : memB table e = true ↔ e ∈ table := by
  simp only [memB, decide_eq_true_eq]
  constructor
  · rintro ⟨e', he', h⟩; rw [serEntry_inj.1 h] at he'; exact he'
  · intro h; exact ⟨e, h, rfl⟩

def guardB (t : Entry × List Entry × Bool) : Bool :=
  decide ((serEntry t.1).length ≤ (serL serEntry t.2.1).length)

theorem memB_of_guard_false (t : Entry × List Entry × Bool) (h : guardB t = false) :
    memB t.2.1 t.1 = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro hm
  apply h
  have := length_lt_serL serEntry t.2.1 t.1 ((memB_iff _ _).1 hm)
  simp only [guardB, decide_eq_true_eq]
  omega

theorem costSum_triple (s : List Bool) (l : List Entry) :
    costSum (fun e' => size (e', s, false) + 0) l = costSum size l + l.length * (size s + 3) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [costSum_cons, List.length_cons]
    rw [ih]
    have : size (a, s, false) = size a + size s + 3 := by
      change size a + (size s + size false + 1) + 1 = _
      rw [size_bit]; omega
    rw [this]; ring

/-- Budget of `memTask`. -/
def memBudget (t : Entry × List Entry × Bool) : ℕ :=
  3 * (size t.2.1 + 1) * (size t.2.1 + 4) + 4 * size t + 10

theorem easy_guard : Easy guardB := by
  have hs : Easy (fun t : Entry × List Entry × Bool => serEntry t.1) := Easy.fst.compose easy_serEntry
  have hL : Easy (fun t : Entry × List Entry × Bool => serL serEntry t.2.1) :=
    (Easy.fstCompose Easy.snd).compose (easy_serL easy_serEntry)
  have h : Easy (fun t : Entry × List Entry × Bool =>
      !Code.Iter.small (serL serEntry t.2.1, serEntry t.1)) :=
    ((hL.pair hs).compose Code.Iter.small_easy).compose Code.Iter.negate
  have e : (fun t : Entry × List Entry × Bool =>
      !Code.Iter.small (serL serEntry t.2.1, serEntry t.1)) = guardB := by
    funext t
    simp only [Code.Iter.small, guardB]
    by_cases hc : (serEntry t.1).length ≤ (serL serEntry t.2.1).length
    · simp [hc, Nat.not_lt.mpr hc]
    · simp [hc, Nat.lt_of_not_le hc]
  rwa [e] at h

theorem memTask : Task (fun t => size t + memBudget t) send
    (fun t => send (t.2.1, t.2.2 && memB t.2.1 t.1)) := by
  -- step 1: guard bit and the two work copies
  have hs : Easy (fun t : Entry × List Entry × Bool => serEntry t.1) := Easy.fst.compose easy_serEntry
  have htab : Easy (fun t : Entry × List Entry × Bool => t.2.1) := Easy.fstCompose Easy.snd
  have hin : Easy (fun t : Entry × List Entry × Bool => (t.2.1, serEntry t.1, false)) :=
    htab.pair (hs.pair (Easy.const false))
  have E1 : Easy (fun t : Entry × List Entry × Bool =>
      (guardB t, ((t.2.1, serEntry t.1, false), t.2))) :=
    easy_guard.pair (hin.pair Easy.snd)
  -- step 2: branch on the guard
  let F : Entry × List Entry × Bool → Tree := fun t => send ((t.2.1, serEntry t.1, false), t.2)
  have hc : Task (fun t : Entry × List Entry × Bool => memBudget t) (fun t => Tree.fork (Tree.atom (guardB t)) (F t))
      (fun t => send (t.2.1, t.2.2 && memB t.2.1 t.1)) := by
    apply Task.control guardB
    · -- guard false: the entry is too long to be in the table
      have hf : Easy (fun r : (List Entry × List Bool × Bool) × (List Entry × Bool) => (r.2.1, false)) :=
        (Easy.fstCompose Easy.snd).pair (Easy.const false)
      refine ((hf.on (fun x : {t // guardB t = false} =>
          ((x.val.2.1, serEntry x.val.1, false), x.val.2))).mono
          (b' := fun x : {t // guardB t = false} => memBudget x.val) (fun x => ?_)).conform
        (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      · have h1 := length_serEntry_le_size x.val.1
        rcases x with ⟨⟨e, tab, ok⟩, hx⟩
        simp only [size_prod, size_bits, size_bit, memBudget] at h1 ⊢
        nlinarith
      · simp [memB_of_guard_false x.val x.property]
    · -- guard true: scan the table
      have hl := Task.left (findTask.on (fun x : {t // guardB t = true} => (x.val.2.1, serEntry x.val.1, false)))
        (fun x : {t // guardB t = true} => send x.val.2)
      have hk : Easy (fun r : (List Bool × Bool) × (List Entry × Bool) => (r.2.1, r.2.2 && r.1.2)) :=
        (Easy.fstCompose Easy.snd).pair ((((Easy.sndCompose Easy.snd).pair (Easy.sndCompose Easy.fst)).compose
          (Easy.finite (fun q : Bool × Bool => q.1 && q.2))))
      have hk' := hk.on (fun x : {t // guardB t = true} =>
        ((serEntry x.val.1, false || decide (∃ e ∈ x.val.2.1, serEntry e = serEntry x.val.1)), x.val.2))
      have hlk := (hl.conform (q' := fun x : {t // guardB t = true} => send ((serEntry x.val.1,
          false || decide (∃ e ∈ x.val.2.1, serEntry e = serEntry x.val.1)), x.val.2))
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).compose hk'
      refine (hlk.mono (b' := fun x : {t // guardB t = true} => memBudget x.val) (fun x => ?_)).conform
        (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
      · rcases x with ⟨⟨e, tab, ok⟩, hx⟩
        simp only [guardB, decide_eq_true_eq] at hx
        have hL := length_serL_le_size length_serEntry_le_size tab
        have hcs : costSum (fun e' => size (e', serEntry e, false) + 0) tab ≤
            size tab + tab.length * (size (serEntry e) + 3) := by
          rw [costSum_triple]
          have := costSum_le_length_size tab
          omega
        have hlen : tab.length ≤ size tab := by have := costSum_le_length_size tab; omega
        have hse : size (serEntry e) ≤ 2 * size tab + 1 := by rw [size_bits]; omega
        have hse' : size (serEntry e) ≤ 2 * size e + 1 := by
          rw [size_bits]; have := length_serEntry_le_size e; omega
        have hprod : tab.length * (size (serEntry e) + 3) ≤ size tab * (2 * size tab + 4) :=
          Nat.mul_le_mul hlen (by omega)
        simp only [memBudget, size_prod, size_bit] at hcs ⊢
        nlinarith
      · simp [memB]
  exact Task.compose E1 (hc.conform (p' := fun t => send (guardB t, ((t.2.1, serEntry t.1, false), t.2)))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

/-! ## All rows in the table -/

def rowNext (table : List Entry) (z : Bool) (e : Entry) : Bool := z && memB table e

open Classical in
theorem foldl_rowNext (table : List Entry) (l : List Entry) (z : Bool) :
    l.foldl (rowNext table) z = (z && decide (∀ e ∈ l, e ∈ table)) := by
  induction l generalizing z with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih]
    by_cases h : e ∈ table
    · have : memB table e = true := (memB_iff _ _).2 h
      simp [rowNext, this, h]
    · have : memB table e = false := by
        rw [Bool.eq_false_iff]; intro hm; exact h ((memB_iff _ _).1 hm)
      simp [rowNext, this, h]

/-- Per-row cost of the table check. -/
def rowCost (table : List Entry) (e : Entry) : ℕ :=
  size (e, table, true) + memBudget (e, table, true)

open Classical in
theorem allMemTask : Code.Task (fun i : List Entry × List Entry × Bool =>
      costSum (rowCost i.2.1) i.1 + size i.1) send
    (fun i => send (i.2.1, i.2.2 && decide (∀ e ∈ i.1, e ∈ i.2.1))) := by
  have h := foldKeep (X := Entry) (Y := List Entry) (Z := Bool) rowNext rowCost
    ((memTask.mono (b' := fun t : Entry × List Entry × Bool => rowCost t.2.1 t.1) (fun t => by
        rcases t with ⟨e, tab, z⟩
        cases z <;> simp [rowCost, memBudget])).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  exact h.conform (fun _ => rfl) (fun _ => rfl) (fun i => by rw [foldl_rowNext])

end P1Hier
