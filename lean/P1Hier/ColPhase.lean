import P1Hier.TapeLoop
import OAI.Computability.IntegerMultiplication.Code.FoldLeft

/-!
# P1Hier.ColPhase: the column passes of the transcript check (phase 4 of `Check`)

`colsB i = decide (∀ k < nK, colOK (start c y k) (col k τ))` is computed by ONE sweep over the
tapes `k = 0, …, nK-1` (`Task.sweep`, ghost = the whole input). The state holds the cell lists of
all rows with the first `k` cells removed, the encoded input word `y.map c.sym`, a counter
`inp + 1 - k` (the input tape is the tape where it equals `1`), and the answer so far. A step peels
the first cell of every row (the column `k`), builds the start tape of tape `k`, and runs
`tape_task` on it. Each step costs `O(size τ + (size c + 1)(|y| + T + 3))`, so the sweep fits
`checkBudget`.

Main result: `cols_core`.
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Two reassociation tasks -/

theorem assocR_task {X : Type*} (f g h : X → Tree) :
    Task (fun x => (f x).count) (fun x => Tree.fork (Tree.fork (f x) (g x)) (h x))
      (fun x => Tree.fork (f x) (Tree.fork (g x) (h x))) := by
  refine ⟨splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((pack 0).join ((move 1 0 2).join (pack 0))))), 200, fun x env r => ?_⟩
  have m1 := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) (f x) env
    (pile 0 (g x) (pile 0 (h x) r))
  have p1 := fits_pack (g x) (h x) (pile 1 (f x) r) 0 env
  have m2 := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) (f x) env
    (pile 0 (Tree.fork (g x) (h x)) r)
  have p2 := fits_pack (f x) (Tree.fork (g x) (h x)) r 0 env
  have all := m1.join ((p1.cast' (by deck_eq) rfl).join ((m2.cast' (by deck_eq) rfl).join p2))
  refine (fits_pair (c := fun _ => Prog.pass) (fits_pair (c := fun _ => Prog.pass) all)).mono ?_
  have := (f x).count_pos
  dsimp only
  omega

theorem assocL_task {X : Type*} (f g h : X → Tree) :
    Task (fun x => (f x).count) (fun x => Tree.fork (f x) (Tree.fork (g x) (h x)))
      (fun x => Tree.fork (Tree.fork (f x) (g x)) (h x)) := by
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (splitRoot 0 (fun _ => .pass)
    ((move 1 0 2).join ((pack 0).join (pack 0))))), 200, fun x env r => ?_⟩
  have m1 := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) (f x) env
    (pile 0 (Tree.fork (g x) (h x)) r)
  have m2 := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) (f x) env
    (pile 0 (g x) (pile 0 (h x) r))
  have p1 := fits_pack (f x) (g x) (pile 0 (h x) r) 0 env
  have p2 := fits_pack (Tree.fork (f x) (g x)) (h x) r 0 env
  have inner : Fits env (splitRoot 0 (fun _ => .pass) ((move 1 0 2).join ((pack 0).join (pack 0))))
      (pile 0 (Tree.fork (g x) (h x)) (pile 1 (f x) r)) (pile 0 (Tree.fork (Tree.fork (f x) (g x)) (h x)) r)
      _ := fits_pair (c := fun _ => Prog.pass) ((m2.cast' (by deck_eq) rfl).join (p1.join p2))
  refine (fits_pair (c := fun _ => Prog.pass) (m1.join (inner.cast' (by deck_eq) rfl))).mono ?_
  have := (f x).count_pos
  dsimp only
  omega

/-! ## Encoding the input word: `y.map c.sym` -/

/-- The symbol of an input bit. -/
def symOf (s : ℕ × ℕ) (b : Bool) : ℕ := if b then s.2 else s.1

def symNext (s : ℕ × ℕ) (acc : List ℕ) (b : Bool) : List ℕ := symOf s b :: acc

theorem foldl_symNext (s : ℕ × ℕ) (y : List Bool) (acc : List ℕ) :
    y.foldl (symNext s) acc = (y.map (symOf s)).reverse ++ acc := by
  induction y generalizing acc with
  | nil => simp
  | cons b y ih => simp [symNext, ih]

theorem easy_symPick : Easy (fun q : Bool × (ℕ × ℕ) => ((q.2), symOf q.2 q.1)) := by
  have h : Easy (fun q : Bool × (ℕ × ℕ) => bif q.1 then q.2.2 else q.2.1) :=
    Easy.ifst (f := fun s : ℕ × ℕ => s.1) (g := fun s : ℕ × ℕ => s.2) Easy.fst Easy.snd
  have e := (Easy.snd (X := Bool) (Y := ℕ × ℕ)).pair h
  refine e.conform (fun _ => rfl) (fun _ => rfl) (fun q => ?_)
  obtain ⟨b, s⟩ := q
  cases b <;> rfl

/-- One step of the symbol map: `(b, (s, acc)) ↦ (s, sym b :: acc)`. -/
theorem symStep : Task (fun i : {i : Bool × List ℕ × (ℕ × ℕ) // True} => 2 * size i.val.2.2 + 2)
    (fun i => Tree.fork (send i.val.1) (send (i.val.2.2, i.val.2.1)))
    (fun i => send (i.val.2.2, symNext i.val.2.2 i.val.2.1 i.val.1)) := by
  have a1 := assocL_task (fun i : {i : Bool × List ℕ × (ℕ × ℕ) // True} => send i.val.1)
    (fun i => send i.val.2.2) (fun i => send i.val.2.1)
  have a2 := Task.left (Task.on easy_symPick (fun i : {i : Bool × List ℕ × (ℕ × ℕ) // True} =>
    (i.val.1, i.val.2.2))) (fun i => send i.val.2.1)
  have a3 := assocR_task (fun i : {i : Bool × List ℕ × (ℕ × ℕ) // True} => send i.val.2.2)
    (fun i => send (symOf i.val.2.2 i.val.1)) (fun i => send i.val.2.1)
  refine ((a1.compose a2).compose a3).bound 4 (fun i => ?_)
  have hb : (send i.val.1).count = 1 := rfl
  have hs : size (i.val.1, i.val.2.2) = 1 + size i.val.2.2 + 1 := by simp [size_prod]
  change (send i.val.1).count + size (i.val.1, i.val.2.2) + (send i.val.2.2).count + 1 ≤ _
  rw [hb, hs]
  change 1 + (1 + size i.val.2.2 + 1) + size i.val.2.2 + 1 ≤ _
  omega

theorem size_reverse {X : Type*} [Codec X] (l : List X) : size l.reverse = size l := by
  rw [← costSum_le_length_size, ← costSum_le_length_size l]
  simp [costSum, List.map_reverse, List.sum_reverse]

theorem size_map_le {X Y : Type*} [Codec X] [Codec Y] (l : List X) (f : X → Y) (B : ℕ)
    (h : ∀ x ∈ l, size (f x) ≤ B) : size (l.map f) ≤ l.length * (B + 1) + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem costSum_const {X : Type*} (l : List X) (c : ℕ) : costSum (fun _ => c) l = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [costSum_cons, ih, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-- `((s0, s1), y) ↦ y.map sym`, linear in `|y|` times the symbol sizes. -/
theorem symMap_task : Task (fun q : (ℕ × ℕ) × List Bool => (q.2.length + 1) * (size q.1 + 1))
    send (fun q => send (q.2.map (symOf q.1))) := by
  have hf := Task.foldLeft (X := Bool) (Y := ℕ × ℕ) (Z := List ℕ) (D := fun _ _ => True)
    (fun _ x => send x) (fun s acc => send (s, acc)) symNext (fun s _ => 2 * size s + 2)
    ((symStep.on (fun i : {s : Bool × List ℕ × (ℕ × ℕ) // True} =>
      (⟨(i.val.1, i.val.2.1, i.val.2.2), trivial⟩ : {i : Bool × List ℕ × (ℕ × ℕ) // True}))).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  have h1 := hf.on (fun q : (ℕ × ℕ) × List Bool => (⟨(q.2, [], q.1), fun _ _ => trivial⟩ :
    {s : List Bool × List ℕ × (ℕ × ℕ) // ∀ v ∈ s.1, True}))
  have h1' : Task (fun q : (ℕ × ℕ) × List Bool => costSum (fun _ => 2 * size q.1 + 2) q.2 +
      (Task.forest (fun x => send x) q.2).count)
      (fun q => send (q.2, (q.1, ([] : List ℕ)))) (fun q => send (q.1, q.2.foldl (symNext q.1) [])) :=
    h1.conform (fun _ => rfl) (fun q => by simp [Task.forest_send]) (fun _ => rfl)
  have hin : Easy (fun q : (ℕ × ℕ) × List Bool => (q.2, (q.1, ([] : List ℕ)))) :=
    Easy.snd.pair (Easy.fst.pair (Easy.const []))
  have hout : Easy (fun p : (ℕ × ℕ) × List ℕ => p.2.reverse) := Easy.snd.compose Easy.reverse
  have h3 := (Task.compose hin h1').compose
    (Task.on hout (fun q : (ℕ × ℕ) × List Bool => (q.1, q.2.foldl (symNext q.1) [])))
  have h4 : Task (fun q : (ℕ × ℕ) × List Bool => (q.2.length + 1) * (size q.1 + 1)) send
      (fun q => send ((q.2.foldl (symNext q.1) []).reverse)) := by
    refine h3.bound 10 (fun q => ?_)
    obtain ⟨s, y⟩ := q
    dsimp only
    have hc := costSum_const y (2 * size s + 2)
    have hfo : (Task.forest (fun x : Bool => send x) y).count = 2 * y.length + 1 := by
      rw [Task.forest_count]
      have : costSum (fun x : Bool => (send x).count) y = y.length := by
        have := costSum_const y 1
        exact this.trans (Nat.mul_one _)
      omega
    have hfold : size (y.foldl (symNext s) []) ≤ y.length * (size s + 1) + 1 := by
      rw [foldl_symNext, List.append_nil, size_reverse]
      refine size_map_le y (symOf s) (size s) (fun b _ => ?_)
      cases b <;> simp [symOf, size_prod] <;> omega
    have hy := size_bits y
    have e1 : (y.length + 1) * (size s + 1) = y.length * size s + y.length + size s + 1 := by ring
    have e2 : y.length * (size s + 1) = y.length * size s + y.length := by ring
    have e3 : y.length * (2 * size s + 2) = 2 * (y.length * size s) + 2 * y.length := by ring
    have p1 : size (s, y) = size s + size y + 1 := rfl
    have p2 : size (s, y.foldl (symNext s) []) = size s + size (y.foldl (symNext s) []) + 1 := rfl
    rw [p1, p2, e1]
    rw [e2] at hfold
    rw [e3] at hc
    omega
  exact h4.conform (fun _ => rfl) (fun _ => rfl) (fun q => by rw [foldl_symNext]; simp)

/-! ## The column step -/

/-- State of the sweep: the cell lists of all rows (first `k` cells removed), `y.map c.sym`,
the counter `inp + 1 - k`, the answer so far. -/
abbrev CState := List (List Cell) × List ℕ × ℕ × Bool

def defCell : Cell := (0, 0, none)

/-- The start tape of the current tape: the input tape iff the counter is `1`. -/
def startOf (ymap : List ℕ) (cnt : ℕ) : Tp := if cnt = 1 then Tp.ofList ymap else Tp.ofList []

/-- The current column: the first cell of every row. -/
def colOf (rest : List (List Cell)) : List Cell := rest.map (fun l => l.headD defCell)

def nextS (z : CState) : CState :=
  (z.1.map List.tail, z.2.1, z.2.2.1 - 1, z.2.2.2 && colOK (startOf z.2.1 z.2.2.1) (colOf z.1))

/-- All symbols in the state are `≤ B`. -/
def StepOK (zb : CState × ℕ) : Prop :=
  (∀ s ∈ zb.1.2.1, s ≤ zb.2) ∧ ∀ l ∈ zb.1.1, ∀ x ∈ l, x.2.1 ≤ zb.2

def stepBud (zb : CState × ℕ) : ℕ :=
  size zb.1 + (zb.1.1.length + zb.1.2.1.length + 2) * (zb.2 + 1)

theorem easy_listTail {X : Type*} [Codec X] : Easy (fun l : List X => l.tail) := by
  have h := Easy.listCase (X := X) (f := fun p : X × List X => p.2) [] Easy.snd
  refine h.conform (fun _ => rfl) (fun _ => rfl) (fun l => ?_)
  cases l <;> rfl

theorem easy_listHeadD {X : Type*} [Codec X] (d : X) : Easy (fun l : List X => l.headD d) := by
  have h := Easy.listCase (X := X) (f := fun p : X × List X => p.1) d Easy.fst
  refine h.conform (fun _ => rfl) (fun _ => rfl) (fun l => ?_)
  cases l <;> rfl

theorem easy_natPred : Easy (fun n : ℕ => n - 1) := by
  have h := Task.on (easy_listTail (X := Unit)) (fun n : ℕ => List.replicate n ())
  refine h.conform (fun _ => rfl) (fun _ => rfl) (fun n => ?_)
  change send (List.replicate n ()).tail = send (List.replicate (n - 1) ())
  rw [List.tail_replicate]

theorem easy_peel : Easy (fun rest : List (List Cell) => (rest.map List.tail, colOf rest)) :=
  (easy_map easy_id easy_listTail).pair (easy_map easy_id (easy_listHeadD defCell))

/-- Prepare the tape pass: `(col, ymap, cnt, ok) ↦ (tape input, (ymap, cnt - 1, ok))`. -/
def prepF (w : List Cell × List ℕ × ℕ × Bool) :
    ((ℕ × Bool) × List ℕ × List ℕ × List Cell) × (List ℕ × ℕ × Bool) :=
  ((((startOf w.2.1 w.2.2.1).h, true), (startOf w.2.1 w.2.2.1).L, (startOf w.2.1 w.2.2.1).R, w.1),
    (w.2.1, w.2.2.1 - 1, w.2.2.2))

theorem startOf_h (ymap : List ℕ) (cnt : ℕ) :
    (startOf ymap cnt).h = bif decide (cnt = 1) then ymap.headD 0 else 0 := by
  unfold startOf; by_cases h : cnt = 1 <;> simp [h, Tp.ofList]

theorem startOf_L (ymap : List ℕ) (cnt : ℕ) : (startOf ymap cnt).L = [] := by
  unfold startOf; by_cases h : cnt = 1 <;> simp [h, Tp.ofList]

theorem startOf_R (ymap : List ℕ) (cnt : ℕ) :
    (startOf ymap cnt).R = bif decide (cnt = 1) then ymap.tail else [] := by
  unfold startOf; by_cases h : cnt = 1 <;> simp [h, Tp.ofList]

theorem easy_prepF : Easy prepF := by
  have hcol : Easy (fun w : List Cell × List ℕ × ℕ × Bool => w.1) := Easy.fst
  have hy : Easy (fun w : List Cell × List ℕ × ℕ × Bool => w.2.1) := Easy.fstCompose Easy.snd
  have hc : Easy (fun w : List Cell × List ℕ × ℕ × Bool => w.2.2.1) :=
    Easy.fstCompose (Easy.sndCompose Easy.snd)
  have hok : Easy (fun w : List Cell × List ℕ × ℕ × Bool => w.2.2.2) :=
    Easy.sndCompose (Easy.sndCompose Easy.snd)
  have h1 : Easy (fun w : List Cell × List ℕ × ℕ × Bool => decide (w.2.2.1 = 1)) :=
    (hc.pair (Easy.const 1)).compose easy_natEq
  have hh : Easy (fun w : List Cell × List ℕ × ℕ × Bool =>
      bif decide (w.2.2.1 = 1) then w.2.1.headD 0 else 0) :=
    (h1.pair hy).compose (Easy.ifst (f := fun _ : List ℕ => (0 : ℕ)) (g := fun l => l.headD 0)
      (Easy.const 0) (easy_listHeadD 0))
  have hR : Easy (fun w : List Cell × List ℕ × ℕ × Bool =>
      bif decide (w.2.2.1 = 1) then w.2.1.tail else []) :=
    (h1.pair hy).compose (Easy.ifst (f := fun _ : List ℕ => ([] : List ℕ)) (g := fun l => l.tail)
      (Easy.const []) easy_listTail)
  have hall := ((hh.pair (Easy.const true)).pair ((Easy.const ([] : List ℕ)).pair (hR.pair hcol))).pair
    (hy.pair ((hc.compose easy_natPred).pair hok))
  refine hall.conform (fun _ => rfl) (fun _ => rfl) (fun w => ?_)
  simp only [prepF, startOf_h, startOf_L, startOf_R]

theorem easy_fin : Easy (fun v : Bool × List ℕ × ℕ × Bool => (v.2.1, v.2.2.1, v.2.2.2 && v.1)) :=
  (Easy.fstCompose Easy.snd).pair ((Easy.fstCompose (Easy.sndCompose Easy.snd)).pair
    (((Easy.sndCompose (Easy.sndCompose Easy.snd)).pair Easy.fst).compose
      (Easy.finite (fun p : Bool × Bool => p.1 && p.2))))

theorem tapeOK_of {zb : CState × ℕ} (h : StepOK zb) :
    TapeOK (startOf zb.1.2.1 zb.1.2.2.1, colOf zb.1.1, zb.2) := by
  obtain ⟨hy, hr⟩ := h
  refine ⟨?_, ?_⟩
  · unfold startOf
    split_ifs
    · exact ⟨by simp [Tp.ofList], headD_le hy, mem_tail_le hy⟩
    · exact ⟨by simp [Tp.ofList], Nat.zero_le _, by simp [Tp.ofList]⟩
  · intro x hx
    simp only [colOf, List.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    cases l with
    | nil => exact Nat.zero_le _
    | cons a l => exact hr _ hl a List.mem_cons_self

theorem size_headD_le (l : List Cell) : size (l.headD defCell) ≤ size l + 4 := by
  cases l with
  | nil => rfl
  | cons a l => simp only [List.headD_cons, size_cons]; omega

theorem size_colOf_le (rest : List (List Cell)) : size (colOf rest) ≤ 5 * size rest := by
  induction rest with
  | nil => simp [colOf]
  | cons l rest ih =>
    have := size_headD_le l
    simp only [colOf, List.map_cons, size_cons] at ih ⊢
    omega

theorem size_tails_le (rest : List (List Cell)) : size (rest.map List.tail) ≤ size rest := by
  induction rest with
  | nil => simp
  | cons l rest ih =>
    have : size l.tail ≤ size l := by
      cases l with
      | nil => exact le_rfl
      | cons a l => simp only [List.tail_cons, size_cons]; omega
    simp only [List.map_cons, size_cons]
    omega

theorem tlen_startOf_le (ymap : List ℕ) (cnt : ℕ) : tlen (startOf ymap cnt) ≤ ymap.length := by
  unfold startOf tlen
  split_ifs <;> simp [Tp.ofList]

abbrev CZ := {zb : CState × ℕ // StepOK zb}

theorem colStep : Task (fun x : CZ => stepBud x.val)
    (fun x => Tree.fork (Tree.atom false) (send x.val.1)) (fun x => send (nextS x.val.1)) := by
  have T1 : Task (fun _ : CZ => (Tree.atom false).count)
      (fun x => Tree.fork (Tree.atom false) (send x.val.1)) (fun x => send x.val.1) :=
    Task.dropLeft (fun _ => Tree.atom false) (fun x : CZ => send x.val.1)
  have T2 : Task (fun x : CZ => size x.val.1.1) (fun x => send x.val.1)
      (fun x => Tree.fork (send (x.val.1.1.map List.tail, colOf x.val.1.1)) (send x.val.1.2)) :=
    Task.left (Task.on easy_peel (fun x : CZ => x.val.1.1)) (fun x : CZ => send x.val.1.2)
  have T3 : Task (fun x : CZ => (send (x.val.1.1.map List.tail)).count)
      (fun x => Tree.fork (send (x.val.1.1.map List.tail, colOf x.val.1.1)) (send x.val.1.2))
      (fun x => Tree.fork (send (x.val.1.1.map List.tail))
        (Tree.fork (send (colOf x.val.1.1)) (send x.val.1.2))) :=
    assocR_task (fun x : CZ => send (x.val.1.1.map List.tail)) (fun x => send (colOf x.val.1.1))
      (fun x => send x.val.1.2)
  have I1 : Task (fun x : CZ => size (colOf x.val.1.1, x.val.1.2))
      (fun x => send (colOf x.val.1.1, x.val.1.2)) (fun x => send (prepF (colOf x.val.1.1, x.val.1.2))) :=
    Task.on easy_prepF (fun x : CZ => (colOf x.val.1.1, x.val.1.2))
  have I1' : Task (fun x : CZ => size (colOf x.val.1.1, x.val.1.2))
      (fun x => send (colOf x.val.1.1, x.val.1.2))
      (fun x => Tree.fork (tapeIn (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1))
        (send (x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))) :=
    I1.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have I2 : Task (fun x : CZ => tapeBudget (startOf x.val.1.2.1 x.val.1.2.2.1, colOf x.val.1.1, x.val.2))
      (fun x => Tree.fork (tapeIn (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1))
        (send (x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2)))
      (fun x => Tree.fork (send (colOK (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1)))
        (send (x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))) :=
    Task.left (Task.on tape_task (fun x : CZ =>
      (⟨(startOf x.val.1.2.1 x.val.1.2.2.1, colOf x.val.1.1, x.val.2), tapeOK_of x.property⟩ :
        {p : Tp × List Cell × ℕ // TapeOK p})))
      (fun x : CZ => send (x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))
  have I3 : Task (fun x : CZ => size (colOK (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1),
        x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))
      (fun x => send (colOK (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1),
        x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))
      (fun x => send (x.val.1.2.1, x.val.1.2.2.1 - 1,
        x.val.1.2.2.2 && colOK (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1))) :=
    Task.on easy_fin (fun x : CZ => (colOK (startOf x.val.1.2.1 x.val.1.2.2.1) (colOf x.val.1.1),
        x.val.1.2.1, x.val.1.2.2.1 - 1, x.val.1.2.2.2))
  have inner := (I1'.compose I2).compose I3
  have T4 := Task.right inner (fun x : CZ => send (x.val.1.1.map List.tail))
  have all := T1.compose (T2.compose (T3.compose T4))
  refine (all.bound 20 (fun x => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨⟨⟨rest, ymap, cnt, ok⟩, B⟩, hx⟩ := x
  dsimp only
  have a := size_tails_le rest
  have b := size_colOf_le rest
  have c := tlen_startOf_le ymap cnt
  have hlen : (colOf rest).length = rest.length := by simp [colOf]
  have d : ((colOf rest).length + tlen (startOf ymap cnt) + 2) * (B + 1) ≤
      (rest.length + ymap.length + 2) * (B + 1) := Nat.mul_le_mul_right _ (by omega)
  have e : size (cnt - 1) ≤ size cnt := by rw [size_nat, size_nat]; omega
  simp only [tapeBudget, stepBud, size_prod, size_bit] at d ⊢
  change 1 + _ + 1 ≤ _
  generalize ((colOf rest).length + tlen (startOf ymap cnt) + 2) * (B + 1) = P at d ⊢
  generalize (rest.length + ymap.length + 2) * (B + 1) = Q at d ⊢
  have a' : (send (rest.map List.tail)).count ≤ size rest := a
  omega

/-! ## The states of the sweep -/

abbrev CIn' := MCode × List Bool × ℕ × List Entry

def rows0 (i : CIn') : List (List Cell) := i.2.2.2.map (fun e => e.2.1)

def ymapOf (i : CIn') : List ℕ := i.2.1.map (symOf (i.1.sym0, i.1.sym1))

def okUpTo (i : CIn') (k : ℕ) : Bool :=
  decide (∀ k' < k, colOK (i.1.start i.2.1 k') (col k' i.2.2.2) = true)

def stateAt (i : CIn') (k : ℕ) : CState :=
  ((rows0 i).map (List.drop k), ymapOf i, i.1.inp + 1 - k, okUpTo i k)

theorem headD_drop (l : List Cell) (k : ℕ) : (l.drop k).headD defCell = l.getD k (0, 0, none) := by
  induction l generalizing k with
  | nil => cases k <;> simp [defCell]
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.drop_succ_cons, List.getD_cons_succ]; exact ih k

theorem tail_drop' (l : List Cell) (k : ℕ) : (l.drop k).tail = l.drop (k + 1) := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [List.drop_succ_cons]; exact ih k

theorem symOf_sym (c : MCode) : symOf (c.sym0, c.sym1) = c.sym := by
  funext b; cases b <;> rfl

theorem startOf_stateAt (i : CIn') (k : ℕ) :
    startOf (ymapOf i) (i.1.inp + 1 - k) = i.1.start i.2.1 k := by
  unfold startOf MCode.start ymapOf
  rw [symOf_sym]
  by_cases h : k = i.1.inp
  · subst h; simp
  · have h' : ¬ (i.1.inp + 1 - k = 1) := by omega
    simp [h, h']

theorem colOf_stateAt (i : CIn') (k : ℕ) :
    colOf ((rows0 i).map (List.drop k)) = col k i.2.2.2 := by
  simp only [colOf, rows0, col, List.map_map]
  apply List.map_congr_left
  intro e _
  simp [headD_drop, defCell]

theorem okUpTo_succ (i : CIn') (k : ℕ) :
    okUpTo i (k + 1) = (okUpTo i k && colOK (i.1.start i.2.1 k) (col k i.2.2.2)) := by
  unfold okUpTo
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨fun m hm => h m (by omega), h k (by omega)⟩
  · rintro ⟨h1, h2⟩ m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
    · exact h1 m hm
    · exact h2

theorem nextS_stateAt (i : CIn') (k : ℕ) : nextS (stateAt i k) = stateAt i (k + 1) := by
  simp only [nextS, stateAt]
  rw [startOf_stateAt, colOf_stateAt, ← okUpTo_succ]
  simp only [List.map_map, Function.comp_def, tail_drop', Nat.sub_sub]

theorem stateAt_zero (i : CIn') : stateAt i 0 = (rows0 i, ymapOf i, i.1.inp + 1, true) := by
  have h : (List.drop 0 : List Cell → List Cell) = id := funext fun _ => rfl
  simp only [stateAt, h, List.map_id]
  simp [okUpTo]

/-! ## Sizes -/

theorem mem_size_lt {X : Type*} [Codec X] {l : List X} {x : X} (h : x ∈ l) : size x < size l := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [size_cons]; omega
    · have := ih h; simp only [size_cons]; omega

theorem size_code (c : MCode) :
    size c = size c.nK + size c.inp + size c.sym0 + size c.sym1 + size c.init + size c.table + 5 := by
  change size (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table) = _
  simp only [size_prod]; omega

theorem write_le {c : MCode} {e : Entry} (he : e ∈ c.table) {x : Cell} (hx : x ∈ e.2.1) :
    x.2.1 ≤ size c := by
  have h1 := mem_size_lt he
  have h2 := mem_size_lt hx
  have h3 := size_code c
  have h4 : size e = size e.1 + size e.2 + 1 := size_prod e
  have h5 : size e.2 = size e.2.1 + size e.2.2 + 1 := size_prod e.2
  have h6 : size x = size x.1 + size x.2 + 1 := size_prod x
  have h7 : size x.2 = size x.2.1 + size x.2.2 + 1 := size_prod x.2
  have h8 := size_nat x.2.1
  omega

theorem size_map_le_size {X Y : Type*} [Codec X] [Codec Y] (l : List X) (f : X → Y)
    (h : ∀ x, size (f x) ≤ size x) : size (l.map f) ≤ size l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, size_cons]; have := h a; omega

theorem size_drop_le {X : Type*} [Codec X] (l : List X) (k : ℕ) : size (l.drop k) ≤ size l := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.drop_succ_cons, size_cons]; have := ih k; omega

/-- The domain of the column phase (the earlier phases accepted). -/
def GoodIn (i : CIn') : Prop := i.2.2.2.length ≤ i.2.2.1 + 1 ∧ ∀ e ∈ i.2.2.2, e ∈ i.1.table

theorem ymap_le (i : CIn') : ∀ s ∈ ymapOf i, s ≤ size i.1 := by
  intro s hs
  simp only [ymapOf, List.mem_map] at hs
  obtain ⟨b, _, rfl⟩ := hs
  have h3 := size_code i.1
  have h4 := size_nat i.1.sym0
  have h5 := size_nat i.1.sym1
  cases b
  · show i.1.sym0 ≤ size i.1
    omega
  · show i.1.sym1 ≤ size i.1
    omega

theorem stepOK_stateAt (i : CIn') (hi : GoodIn i) (k : ℕ) : StepOK (stateAt i k, size i.1) := by
  refine ⟨ymap_le i, ?_⟩
  intro l hl x hx
  simp only [stateAt, rows0, List.map_map, List.mem_map, Function.comp_def] at hl
  obtain ⟨e, he, rfl⟩ := hl
  exact write_le (hi.2 e he) (List.mem_of_mem_drop hx)

theorem size_ymap_le (i : CIn') : size (ymapOf i) ≤ i.2.1.length * (2 * size i.1 + 2) + 1 := by
  have h := size_map_le i.2.1 (symOf (i.1.sym0, i.1.sym1)) (2 * size i.1 + 1) (fun b _ => by
    have := ymap_le i (symOf (i.1.sym0, i.1.sym1) b) (by simp only [ymapOf]; exact List.mem_map_of_mem ‹_›)
    rw [size_nat]; omega)
  have e : 2 * size i.1 + 1 + 1 = 2 * size i.1 + 2 := by omega
  rw [e] at h
  exact h

theorem size_rows_le (i : CIn') (k : ℕ) : size ((rows0 i).map (List.drop k)) ≤ size i.2.2.2 := by
  have h1 := size_map_le_size (rows0 i) (List.drop k) (fun l => size_drop_le l k)
  have h2 := size_map_le_size i.2.2.2 (fun e : Entry => e.2.1) (fun e => by
    have h4 : size e = size e.1 + size e.2 + 1 := size_prod e
    have h5 : size e.2 = size e.2.1 + size e.2.2 + 1 := size_prod e.2
    omega)
  exact h1.trans h2

theorem size_stateAt_le (i : CIn') (k : ℕ) :
    size (stateAt i k) ≤ size i.2.2.2 + i.2.1.length * (2 * size i.1 + 2) + 2 * size i.1 + 10 := by
  have h1 := size_rows_le i k
  have h2 := size_ymap_le i
  have h3 := size_code i.1
  have h4 := size_nat i.1.inp
  have h5 := size_nat (i.1.inp + 1 - k)
  change size ((rows0 i).map (List.drop k), ymapOf i, i.1.inp + 1 - k, okUpTo i k) ≤ _
  simp only [size_prod, size_bit]
  omega

/-- Cost bound of one step of the sweep. -/
def bigBud (i : CIn') : ℕ := size i.2.2.2 + 4 * ((size i.1 + 1) * (i.2.1.length + i.2.2.1 + 3))

theorem stepBud_le (i : CIn') (hi : GoodIn i) (k : ℕ) : stepBud (stateAt i k, size i.1) ≤ bigBud i := by
  have h1 := size_stateAt_le i k
  have hl1 : ((rows0 i).map (List.drop k)).length ≤ i.2.2.1 + 1 := by
    simp only [rows0, List.length_map]; exact hi.1
  have hl2 : (ymapOf i).length = i.2.1.length := by simp [ymapOf]
  change size (stateAt i k) + (((rows0 i).map (List.drop k)).length + (ymapOf i).length + 2) *
    (size i.1 + 1) ≤ bigBud i
  unfold bigBud
  rw [hl2]
  have hp := size_pos i.1
  nlinarith [Nat.mul_le_mul_right (size i.1 + 1) hl1, h1]

/-! ## The sweep -/

abbrev Gh := {i : CIn' // GoodIn i}

def wS (l : List Unit) (y : Gh) : Tree := send (stateAt y.val (y.val.1.nK - l.length))

theorem sweep_step : Task (fun s : {s : Unit × List Unit × Gh // (s.1 :: s.2.1).length ≤ s.2.2.val.1.nK} =>
      bigBud s.val.2.2.val)
    (fun s => Tree.fork (send s.val.1) (wS (s.val.1 :: s.val.2.1) s.val.2.2))
    (fun s => wS s.val.2.1 s.val.2.2) := by
  have h := colStep.on (fun s : {s : Unit × List Unit × Gh // (s.1 :: s.2.1).length ≤ s.2.2.val.1.nK} =>
    (⟨(stateAt s.val.2.2.val (s.val.2.2.val.1.nK - (s.val.2.1.length + 1)), size s.val.2.2.val.1),
      stepOK_stateAt _ s.val.2.2.property _⟩ : CZ))
  refine (h.mono (fun s => stepBud_le _ s.val.2.2.property _)).conform (fun _ => rfl) (fun _ => rfl)
    (fun s => ?_)
  rcases s with ⟨⟨u, l, y⟩, hs⟩
  dsimp only [wS]
  rw [nextS_stateAt]
  simp only [List.length_cons] at hs
  congr 2
  omega

theorem foldCost_const {X : Type*} (A : ℕ) (l : List X) :
    Task.foldCost (fun _ _ => A) l = l.length * (A + 1) + 1 := by
  induction l with
  | nil => simp [Task.foldCost]
  | cons a l ih => simp only [Task.foldCost, ih, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

theorem sweep_task : Task (fun y : Gh => y.val.1.nK * (bigBud y.val + 2) + 1 +
      size (stateAt y.val y.val.1.nK))
    (fun y => Tree.fork (send (List.replicate y.val.1.nK ()))
      (send (rows0 y.val, ymapOf y.val, y.val.1.inp + 1, true)))
    (fun y => send (okUpTo y.val y.val.1.nK)) := by
  have hs := Task.sweep (X := Unit) (Y := Gh) (p := fun _ x => send x) (w := wS)
    (a := fun _ _ y => bigBud y.val) (D := fun l y => l.length ≤ y.val.1.nK)
    (fun x l y h => by simp only [List.length_cons] at h; omega) sweep_step
  have h2 := hs.on (fun y : Gh => (⟨(List.replicate y.val.1.nK (), y), by simp⟩ :
    {s : List Unit × Gh // s.1.length ≤ s.2.val.1.nK}))
  have hE : Easy (fun z : CState => z.2.2.2) := Easy.sndCompose (Easy.sndCompose Easy.snd)
  have h3 := h2.compose (Task.on hE (fun y : Gh => stateAt y.val y.val.1.nK))
  have hf : ∀ (A : ℕ) (l : List Unit), Task.foldCost (fun (x : Unit) (_ : List Unit) => A + (send x).count) l
      = l.length * (A + 1 + 1) + 1 := fun A l => foldCost_const (A + 1) l
  refine h3.conform (fun y => ?_) (fun y => ?_) (fun y => rfl)
  · dsimp only
    rw [hf, List.length_replicate]
  · simp [wS, Task.forest_send, stateAt_zero]

/-! ## The whole column phase -/

theorem size_rows0_le (i : CIn') : size (rows0 i) ≤ size i.2.2.2 :=
  size_map_le_size i.2.2.2 (fun e : Entry => e.2.1) (fun e => by
    have h4 : size e = size e.1 + size e.2 + 1 := size_prod e
    have h5 : size e.2 = size e.2.1 + size e.2.2 + 1 := size_prod e.2
    omega)

theorem size_rows_bound (i : CIn') (hi : GoodIn i) :
    size i.2.2.2 ≤ (i.2.2.1 + 1) * (size i.1 + 1) + 1 := by
  have h := size_map_le i.2.2.2 id (size i.1) (fun e he => by
    have h1 := mem_size_lt (hi.2 e he)
    have h2 := size_code i.1
    simp only [id]; omega)
  rw [List.map_id] at h
  have : i.2.2.2.length * (size i.1 + 1) ≤ (i.2.2.1 + 1) * (size i.1 + 1) :=
    Nat.mul_le_mul_right _ hi.1
  omega

theorem cols_bound (i : CIn') (hi : GoodIn i) :
    size i + ((i.2.1.length + 1) * (size (i.1.sym0, i.1.sym1) + 1) +
      (size (ymapOf i, List.replicate i.1.nK (), rows0 i, i.1.inp + 1) +
        (i.1.nK * (bigBud i + 2) + 1 + size (stateAt i i.1.nK)))) + 1 ≤
      100 * (checkBudget i + 1) := by
  have hτ := size_rows_bound i hi
  have hst := size_stateAt_le i i.1.nK
  have hym := size_ymap_le i
  have hrows := size_rows0_le i
  obtain ⟨c, y, T, τ⟩ := i
  dsimp only at hτ hst hym hrows ⊢
  have hsc := size_code c
  have h1 := size_nat c.nK
  have h2 := size_nat c.inp
  have h3 := size_nat (c.inp + 1)
  have h4 := size_nat c.sym0
  have h5 := size_nat c.sym1
  have hnK : c.nK ≤ size c := by omega
  have hss : size (c.sym0, c.sym1) ≤ size c := by simp only [size_prod]; omega
  have hsize : size (c, y, T, τ) = size c + (2 * y.length + 1) + (2 * T + 1) + size τ + 3 := by
    simp only [size_prod, size_bits, size_nat]; omega
  have htal : size (List.replicate c.nK ()) = 2 * c.nK + 1 := size_nat c.nK
  have hmid : size (ymapOf (c, y, T, τ), List.replicate c.nK (), rows0 (c, y, T, τ), c.inp + 1) =
      size (ymapOf (c, y, T, τ)) + (size (List.replicate c.nK ()) +
        (size (rows0 (c, y, T, τ)) + size (c.inp + 1) + 1) + 1) + 1 := by
    simp only [size_prod]
  set sc := size c with hsc_def
  set M := (sc + 1) ^ 2 * (y.length + T + 1) with hM
  have F0 : (y.length + T + 1) * (sc + 1) ≤ M := by
    calc (y.length + T + 1) * (sc + 1) ≤ (sc + 1) * ((y.length + T + 1) * (sc + 1)) :=
          Nat.le_mul_of_pos_left _ (by omega)
      _ = M := by rw [hM]; ring
  have F1 : (y.length + 1) * (size (c.sym0, c.sym1) + 1) ≤ M :=
    (Nat.mul_le_mul (by omega) (by omega)).trans F0
  have F2 : y.length * (2 * sc + 2) ≤ 2 * M := by
    have : y.length * (sc + 1) ≤ (y.length + T + 1) * (sc + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : y.length * (2 * sc + 2) = 2 * (y.length * (sc + 1)) := by ring
    omega
  have F3 : c.nK * size τ ≤ M + sc := by
    have a : c.nK * size τ ≤ sc * ((T + 1) * (sc + 1) + 1) := Nat.mul_le_mul hnK hτ
    have b : sc * ((T + 1) * (sc + 1)) ≤ (sc + 1) * ((y.length + T + 1) * (sc + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
    have e1 : sc * ((T + 1) * (sc + 1) + 1) = sc * ((T + 1) * (sc + 1)) + sc := by ring
    have e2 : (sc + 1) * ((y.length + T + 1) * (sc + 1)) = M := by rw [hM]; ring
    omega
  have F4 : c.nK * (4 * ((sc + 1) * (y.length + T + 3))) ≤ 12 * M := by
    have a : c.nK * (4 * ((sc + 1) * (y.length + T + 3))) ≤
        (sc + 1) * (4 * ((sc + 1) * (3 * (y.length + T + 1)))) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
    have e : (sc + 1) * (4 * ((sc + 1) * (3 * (y.length + T + 1)))) = 12 * M := by rw [hM]; ring
    omega
  have G : sc + y.length + T + 1 ≤ M := by
    have : sc + y.length + T + 1 ≤ (y.length + T + 1) * (sc + 1) := by nlinarith
    omega
  have E : c.nK * (bigBud (c, y, T, τ) + 2) =
      c.nK * size τ + c.nK * (4 * ((sc + 1) * (y.length + T + 3))) + 2 * c.nK := by
    unfold bigBud; dsimp only; ring
  have hcb : checkBudget (c, y, T, τ) = M + size τ := by
    unfold checkBudget; dsimp only
  rw [E, hcb, hsize, hmid, htal]
  have hy2 : y.length ≤ M := by omega
  generalize c.nK * size τ = P3 at F3 ⊢
  generalize c.nK * (4 * ((sc + 1) * (y.length + T + 3))) = P4 at F4 ⊢
  generalize (y.length + 1) * (size (c.sym0, c.sym1) + 1) = P1 at F1 ⊢
  generalize y.length * (2 * sc + 2) = P2 at F2 hym hst ⊢
  omega

/-- The column phase on its domain. -/
theorem cols_core : Task (fun i : Gh => checkBudget i.val) (fun i => send i.val)
    (fun i => send (okUpTo i.val i.val.1.nK)) := by
  have hcode : Easy (fun c : MCode => (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)) :=
    (Task.self (b := size) (p := send)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hc : Easy (fun i : CIn' => (i.1.nK, i.1.inp, i.1.sym0, i.1.sym1, i.1.init, i.1.table)) :=
    Easy.fst.compose hcode
  have hnK : Easy (fun i : CIn' => i.1.nK) := hc.compose Easy.fst
  have hinp : Easy (fun i : CIn' => i.1.inp) := hc.compose (Easy.fstCompose Easy.snd)
  have hs0 : Easy (fun i : CIn' => i.1.sym0) :=
    hc.compose (Easy.fstCompose (Easy.sndCompose Easy.snd))
  have hs1 : Easy (fun i : CIn' => i.1.sym1) :=
    hc.compose (Easy.fstCompose (Easy.sndCompose (Easy.sndCompose Easy.snd)))
  have hy : Easy (fun i : CIn' => i.2.1) := Easy.fstCompose Easy.snd
  have hτ : Easy (fun i : CIn' => i.2.2.2) := Easy.sndCompose (Easy.sndCompose Easy.snd)
  have hrows : Easy rows0 := easy_map hτ (Easy.fstCompose Easy.snd)
  have hinc : Easy (fun n : ℕ => n + 1) :=
    ((Task.tag false (send (X := ℕ))).mono (fun _ => Nat.zero_le _)).conform (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
  have E0 : Easy (fun i : CIn' => (((i.1.sym0, i.1.sym1), i.2.1),
      (List.replicate i.1.nK (), (rows0 i, i.1.inp + 1)))) :=
    ((hs0.pair hs1).pair hy).pair ((hnK.compose easy_tally).pair (hrows.pair (hinp.compose hinc)))
  have S0 := Task.on E0 (fun i : Gh => i.val)
  have S1 := Task.left (Task.on symMap_task (fun i : Gh => ((i.val.1.sym0, i.val.1.sym1), i.val.2.1)))
    (fun i : Gh => send (List.replicate i.val.1.nK (), (rows0 i.val, i.val.1.inp + 1)))
  have E2 : Easy (fun v : List ℕ × List Unit × List (List Cell) × ℕ => (v.2.1, (v.2.2.1, v.1, v.2.2.2, true))) :=
    (Easy.fstCompose Easy.snd).pair ((Easy.fstCompose (Easy.sndCompose Easy.snd)).pair
      (Easy.fst.pair ((Easy.sndCompose (Easy.sndCompose Easy.snd)).pair (Easy.const true))))
  have S2 := Task.on E2 (fun i : Gh => (ymapOf i.val, List.replicate i.val.1.nK (), rows0 i.val,
    i.val.1.inp + 1))
  have all := S0.compose (S1.compose (S2.compose sweep_task))
  exact all.bound 100 (fun i => cols_bound i.val i.property)

end P1Hier
