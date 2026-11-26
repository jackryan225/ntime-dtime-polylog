import P1NTime.Paths

namespace P1NTime.AstraNTime.Composite

open C1Challenge

inductive Setup where
  | scan | copy | guess | mark
  deriving DecidableEq

instance : Fintype Setup where
  elems := {.scan, .copy, .guess, .mark}
  complete := by intro q; cases q <;> simp

abbrev Key (D V : Machine) := Option (D.K ⊕ V.K)
abbrev Sym (D V : Machine) := D.Γ × V.Γ
abbrev Control (D V : Machine) := Setup ⊕ (D.Q ⊕ V.Q)
abbrev Tapes (M : Machine) := M.K → Turing.Tape M.Γ
abbrev Op (A : Type) := A × HeadMove

def heads {K A : Type} [Inhabited A] (ts : K → Turing.Tape A) (k : K) : A := (ts k).head

def hold {K A : Type} (r : K → A) (k : K) : Op A := (r k, .stay)

def atInput (M : Machine) (r : M.K → M.Γ) (a : Op M.Γ) (k : M.K) : Op M.Γ :=
  if k = M.inputTape then a else (r k, .stay)

def act {A : Type} [Inhabited A] (t : Turing.Tape A) (a : Op A) : Turing.Tape A :=
  a.2.apply (t.write a.1)

def updateBank {K A : Type} [Inhabited A] (ts : K → Turing.Tape A) (ops : K → Op A) :
    K → Turing.Tape A := fun k => act (ts k) (ops k)

theorem act_hold {A : Type} [Inhabited A] (t : Turing.Tape A) : act t (t.head, .stay) = t :=
  Turing.Tape.write_self t

theorem update_hold {K A : Type} [Inhabited A] (ts : K → Turing.Tape A) :
    updateBank ts (hold (heads ts)) = ts := funext fun k => act_hold (ts k)

variable (D V : Machine)

def letter (b : Bool) : Sym D V := (D.inputSymbol b, V.inputSymbol b)

/-- An instruction in the native alphabet of each group of tapes. -/
structure Instruction (D V : Machine) where
  q : Control D V
  src : Op (Sym D V)
  ds : D.K → Op D.Γ
  vs : V.K → Op V.Γ

def idle (q : Control D V) (src : Op (Sym D V)) (d : D.K → D.Γ) (v : V.K → V.Γ) :
    Instruction D V := ⟨q, src, hold d, hold v⟩

def both (q : Control D V) (src : Op (Sym D V)) (d : D.K → D.Γ) (v : V.K → V.Γ)
    (a : Sym D V) (m : HeadMove) : Instruction D V :=
  ⟨q, src, atInput D d (a.1, m), atInput V v (a.2, m)⟩

abbrev NativeOut (M : Machine) := M.Q × (M.K → M.Γ) × (M.K → HeadMove)

def checkInstr (s : Sym D V) (v : V.K → V.Γ) (o : NativeOut D) : Instruction D V :=
  ⟨.inr (.inl o.1), (s, .stay), fun k => (o.2.1 k, o.2.2 k), hold v⟩

def verifyInstr (s : Sym D V) (d : D.K → D.Γ) (o : NativeOut V) : Instruction D V :=
  ⟨.inr (.inr o.1), (s, .stay), hold d, fun k => (o.2.1 k, o.2.2 k)⟩

open Classical in
noncomputable def program (q : Control D V) (s : Sym D V) (d : D.K → D.Γ) (v : V.K → V.Γ) :
    List (Instruction D V) :=
  match q with
  | .inl .scan =>
    if s = default then [idle D V (.inl .copy) (s, .left) d v]
    else [idle D V (.inl .scan) (s, .right) d v]
  | .inl .copy =>
    if s = default then [both D V (.inl .guess) (s, .right) d v (letter D V false) .left]
    else [both D V (.inl .copy) (s, .left) d v s .left]
  | .inl .guess =>
    let stop := both D V (.inr (.inl D.initialState)) (s, .stay) d v
      (d D.inputTape, v V.inputTape) .right
    let bit := fun b => both D V (.inl .mark) (default, .right) d v (letter D V b) .left
    if s = default then [stop] else [stop, bit false, bit true]
  | .inl .mark =>
    [both D V (.inl .guess) (s, .stay) d v (letter D V true) .left]
  | .inr (.inl q) =>
    match D.code q d with
    | some o => [checkInstr D V s v o]
    | none => if D.accept q then [idle D V (.inr (.inr V.initialState)) (s, .stay) d v] else []
  | .inr (.inr q) =>
    match V.code q v with
    | some o => [verifyInstr D V s d o]
    | none => []

def encode (a : Instruction D V) :
    Control D V × (Key D V → Sym D V) × (Key D V → HeadMove) :=
  (a.q, (fun
    | none => a.src.1
    | some (.inl k) => ((a.ds k).1, default)
    | some (.inr k) => (default, (a.vs k).1)), (fun
    | none => a.src.2
    | some (.inl k) => (a.ds k).2
    | some (.inr k) => (a.vs k).2))

noncomputable def machine : NMachine where
  K := Key D V
  inputTape := none
  Γ := Sym D V
  Q := Control D V
  initialState := .inl .scan
  inputSymbol := letter D V
  input_injective := fun _ _ h => D.input_injective (congrArg Prod.fst h)
  input_ne_blank := fun b h => D.input_ne_blank b (congrArg Prod.fst h)
  code := fun q r => (program D V q (r none)
    (fun k => (r (some (.inl k))).1) (fun k => (r (some (.inr k))).2)).map (encode D V)
  accept := fun
    | .inr (.inr q) => V.accept q
    | _ => false

def intoD : Turing.PointedMap D.Γ (Sym D V) := ⟨fun a => (a, default), rfl⟩
def intoV : Turing.PointedMap V.Γ (Sym D V) := ⟨fun a => (default, a), rfl⟩

noncomputable def pack (q : Control D V) (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V) :
    Conf (machine D V) :=
  ⟨q, fun
    | none => src
    | some (.inl k) => (d k).map (intoD D V)
    | some (.inr k) => (v k).map (intoV D V)⟩

noncomputable def result (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V) (a : Instruction D V) :
    Conf (machine D V) :=
  pack D V a.q (act src a.src) (updateBank d a.ds) (updateBank v a.vs)

theorem act_map {A B : Type} [Inhabited A] [Inhabited B] (f : Turing.PointedMap A B)
    (t : Turing.Tape A) (a : Op A) :
    act (t.map f) (f a.1, a.2) = (act t a).map f := by
  change a.2.apply ((t.map f).write (f a.1)) = (a.2.apply (t.write a.1)).map f
  rw [← Turing.Tape.map_write, NTimeGuards.headMove_apply_map]

theorem apply_pack (q : Control D V) (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V)
    (a : Instruction D V) :
    (machine D V).apply (pack D V q src d v) (encode D V a) = result D V src d v a := by
  apply NTimeGuards.cfg_ext
  · rfl
  · funext k
    cases k with
    | none => rfl
    | some k =>
      cases k with
      | inl k => exact act_map (intoD D V) (d k) (a.ds k)
      | inr k => exact act_map (intoV D V) (v k) (a.vs k)

theorem next_pack (q : Control D V) (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V)
    (y : Conf (machine D V)) :
    (machine D V).Next (pack D V q src d v) y ↔
      ∃ a ∈ program D V q src.head (heads d) (heads v), y = result D V src d v a := by
  change (∃ o ∈ (program D V q src.head (heads d) (heads v)).map (encode D V),
    (machine D V).apply (pack D V q src d v) o = y) ↔ _
  constructor
  · rintro ⟨o, ho, rfl⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    exact ⟨a, ha, apply_pack D V q src d v a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨encode D V a, List.mem_map.mpr ⟨a, ha, rfl⟩, apply_pack D V q src d v a⟩

theorem next_one (q : Control D V) (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V)
    {a : Instruction D V} (h : program D V q src.head (heads d) (heads v) = [a])
    (y : Conf (machine D V)) :
    (machine D V).Next (pack D V q src d v) y ↔ y = result D V src d v a := by
  rw [next_pack, h]
  simp

theorem halted_empty (q : Control D V) (src : Turing.Tape (Sym D V)) (d : Tapes D) (v : Tapes V)
    (h : program D V q src.head (heads d) (heads v) = []) :
    (machine D V).Halted (pack D V q src d v) := by
  change (program D V q src.head (heads d) (heads v)).map (encode D V) = []
  simp only [h, List.map_nil]

end P1NTime.AstraNTime.Composite
