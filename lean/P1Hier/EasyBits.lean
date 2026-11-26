import P1Hier.Universal
import P1Hier.Hierarchy
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Code.Automata
import OAI.Computability.IntegerMultiplication.Code.Slice

/-!
# P1Hier.EasyBits: linear-time tools on bit strings (OpenAI `Easy` framework)

* `easy_all`: conjunction of a bit list; `easy_eqBits`: equality of two bit lists.
* `easy_sumElim`: case split on a sum type.
* `easy_serN`, `easy_serL`, `easy_serRes`, `easy_serCell`, `easy_serEntry`: the prefix-free bit codes
  of `Hierarchy.lean` are linear-time; with `pf_*` they turn equality tests on structured data into
  `easy_eqBits`.
-/

namespace P1Hier

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Unary numbers are tally lists already. -/
theorem easy_tally : Easy (fun n : ℕ => List.replicate n ()) :=
  (Task.self (b := size) (p := send)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-! ## Conjunction and equality of bit lists -/

def andStep (x : Bool) (s : Bool) : Bool × List Unit := (s && x, [])

theorem foldl_trans_and (l : List Bool) (s : Bool) (acc : List Unit) :
    l.foldl (Code.trans andStep) (s, acc) = (s && l.all id, acc) := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    have : Code.trans andStep (s, acc) x = (s && x, acc) := by
      simp [Code.trans, andStep]
    rw [this, ih]
    simp [Bool.and_assoc]

theorem easy_all : Easy (fun l : List Bool => l.all id) := by
  have h : Easy (fun l : List Bool => (Code.machine andStep (l, true)).2) :=
    Easy.sndCompose (Easy.machine (easy_id.pair (Easy.const true)))
  have e : (fun l : List Bool => (Code.machine andStep (l, true)).2) = fun l => l.all id := by
    funext l
    simp [Code.machine, foldl_trans_and]
  rwa [e] at h

def eqPairs (p : List Bool × List Bool) : Bool :=
  decide (p.1.length = p.2.length) && ((zipSafe false false p).map (fun q => q.1 == q.2)).all id

theorem easy_eqPairs : Easy eqPairs := by
  have h1 : Easy (fun p : List Bool × List Bool => decide (p.1.length = p.2.length)) :=
    Code.Iter.linked
  have h2 : Easy (fun p : List Bool × List Bool =>
      ((zipSafe false false p).map (fun q => q.1 == q.2)).all id) :=
    (easy_map (Easy.zipSafe false false) (Easy.finite _)).compose easy_all
  exact (h1.pair h2).compose (Easy.finite (fun q : Bool × Bool => q.1 && q.2))

theorem all_zip_eq (l1 l2 : List Bool) (h : l1.length = l2.length) :
    ((l1.zip l2).map (fun q => q.1 == q.2)).all id = decide (l1 = l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.length_cons, add_left_inj] at h
      simp only [List.zip_cons_cons, List.map_cons, List.all_cons, ih l2 h, List.cons.injEq, id]
      by_cases hab : a = b <;> simp [hab]

theorem eqPairs_eq (l1 l2 : List Bool) : eqPairs (l1, l2) = decide (l1 = l2) := by
  unfold eqPairs zipSafe
  by_cases h : l1.length = l2.length
  · simp only [h, decide_true, Bool.true_and]
    rw [List.zip_append (by simp [h]), List.map_append, List.all_append, all_zip_eq l1 l2 h]
    have : ((List.replicate l2.length false).zip (List.replicate l2.length false)).map
        (fun q : Bool × Bool => q.1 == q.2) = List.replicate l2.length true := by
      simp [List.zip_replicate']
    rw [this]
    simp
  · have hne : l1 ≠ l2 := fun e => h (by rw [e])
    simp [h, hne]

theorem easy_eqBits : Easy (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
  have e : eqPairs = fun p : List Bool × List Bool => decide (p.1 = p.2) := by
    funext p
    rcases p with ⟨a, b⟩
    exact eqPairs_eq a b
  rw [← e]
  exact easy_eqPairs

/-! ## Case split on a sum -/

section Sum
variable {X Y Z : Type*} [Codec X] [Codec Y] [Codec Z]

def payload : X ⊕ Y → Tree
  | Sum.inl a => send a
  | Sum.inr b => send b

def leftOf : {s : X ⊕ Y // s.isRight = false} → X
  | ⟨Sum.inl a, _⟩ => a
  | ⟨Sum.inr _, h⟩ => absurd h (by simp)

def rightOf : {s : X ⊕ Y // s.isRight = true} → Y
  | ⟨Sum.inr b, _⟩ => b
  | ⟨Sum.inl _, h⟩ => absurd h (by simp)

theorem easy_sumElim {f : X → Z} {g : Y → Z} (hf : Easy f) (hg : Easy g) :
    Easy (fun s : X ⊕ Y => Sum.elim f g s) := by
  have hc : Task size (fun s : X ⊕ Y => Tree.fork (Tree.atom s.isRight) (payload s))
      (fun s => send (Sum.elim f g s)) := by
    apply Task.control (fun s : X ⊕ Y => s.isRight)
    · refine ((hf.on leftOf).mono (b' := fun x => size x.val) ?_).conform (fun _ => rfl)
        (fun x => ?_) (fun x => ?_)
      · rintro ⟨s, hs⟩
        cases s with
        | inl a => simp [leftOf]
        | inr b => simp at hs
      · rcases x with ⟨s, hs⟩
        cases s with
        | inl a => rfl
        | inr b => simp at hs
      · rcases x with ⟨s, hs⟩
        cases s with
        | inl a => rfl
        | inr b => simp at hs
    · refine ((hg.on rightOf).mono (b' := fun x => size x.val) ?_).conform (fun _ => rfl)
        (fun x => ?_) (fun x => ?_)
      · rintro ⟨s, hs⟩
        cases s with
        | inl a => simp at hs
        | inr b => simp [rightOf]
      · rcases x with ⟨s, hs⟩
        cases s with
        | inl a => simp at hs
        | inr b => rfl
      · rcases x with ⟨s, hs⟩
        cases s with
        | inl a => simp at hs
        | inr b => rfl
  refine hc.conform (fun _ => rfl) (fun s => ?_) (fun _ => rfl)
  cases s <;> rfl

end Sum

/-! ## The bit codes are linear-time -/

theorem easy_serN : Easy serN := by
  have h : Easy (fun n : ℕ => (List.replicate n ()).map (fun _ => true) ++ [false]) :=
    easy_append (easy_map easy_tally (Easy.const true)) (Easy.const [false])
  have e : (fun n : ℕ => (List.replicate n ()).map (fun _ => true) ++ [false]) = serN := by
    funext n
    simp [serN, List.map_replicate]
  rwa [e] at h

theorem easy_serL {α : Type*} [Codec α] {f : α → List Bool} (hf : Easy f) : Easy (serL f) := by
  have h : Easy (fun l : List α => (l.map (fun a => true :: f a)).flatten ++ [false]) :=
    easy_append (easy_flatten (easy_map easy_id ((Easy.const true).pair hf |>.compose Easy.cons)))
      (Easy.const [false])
  have e : (fun l : List α => (l.map (fun a => true :: f a)).flatten ++ [false]) = serL f := by
    funext l
    simp [serL, List.flatMap]
  rwa [e] at h

theorem easy_serMv : Easy serMv := Easy.finite _

theorem easy_serRes : Easy serRes := by
  have h : Easy (fun s : ℕ ⊕ Bool =>
      Sum.elim (fun q => false :: serN q) (fun b => [true, b]) s) :=
    easy_sumElim ((Easy.const false).pair easy_serN |>.compose Easy.cons) (Easy.finite _)
  have e : (fun s : ℕ ⊕ Bool => Sum.elim (fun q => false :: serN q) (fun b => [true, b]) s) =
      serRes := by
    funext s
    cases s <;> rfl
  rwa [e] at h

theorem easy_serCell : Easy serCell := by
  have h1 : Easy (fun x : Cell => serN x.1) := Easy.fst.compose easy_serN
  have h2 : Easy (fun x : Cell => serN x.2.1) := (Easy.fstCompose Easy.snd).compose easy_serN
  have h3 : Easy (fun x : Cell => serMv x.2.2) := (Easy.sndCompose Easy.snd).compose easy_serMv
  exact easy_append h1 (easy_append h2 h3)

theorem easy_serEntry : Easy serEntry := by
  have h1 : Easy (fun e : Entry => serN e.1) := Easy.fst.compose easy_serN
  have h2 : Easy (fun e : Entry => serL serCell e.2.1) :=
    (Easy.fstCompose Easy.snd).compose (easy_serL easy_serCell)
  have h3 : Easy (fun e : Entry => serRes e.2.2) := (Easy.sndCompose Easy.snd).compose easy_serRes
  exact easy_append h1 (easy_append h2 h3)

/-! ## Equality of structured data through the bit codes -/

/-- `chainOK` is an equality of two lists of `ℕ ⊕ Bool`. -/
theorem chainOK_eq (q : ℕ) (τ : List Entry) : chainOK q τ =
    decide ((Sum.inl q :: τ.map (fun e => e.2.2)) =
      (τ.map (fun e => (Sum.inl e.1 : ℕ ⊕ Bool)) ++ [Sum.inr true])) := by
  induction τ generalizing q with
  | nil => simp [chainOK]
  | cons e rest ih =>
    rcases e with ⟨q0, cells, r⟩
    cases r with
    | inl q' =>
      simp only [chainOK, ih, List.map_cons, List.cons_append, List.cons.injEq, Sum.inl.injEq]
      by_cases h : q0 = q
      · subst h; simp
      · have h' : ¬ q = q0 := fun e => h e.symm
        simp [h, h']
    | inr b =>
      cases rest with
      | nil =>
        by_cases h : q0 = q
        · subst h; cases b <;> simp [chainOK]
        · have h' : ¬ q = q0 := fun e => h e.symm
          simp [chainOK, h, h']
      | cons e' r' => simp [chainOK]

theorem serL_injective {α : Type*} {f : α → List Bool} (hf : PF f) :
    Function.Injective (serL f) := by
  intro a b h
  have := pf_serL hf a b [] [] (by simpa using h)
  exact this.1

theorem easy_eq_of_pf {α : Type*} [Codec α] [DecidableEq α] {f : α → List Bool} (hf : Easy f)
    (hinj : Function.Injective f) : Easy (fun p : α × α => decide (p.1 = p.2)) := by
  have h : Easy (fun p : α × α => decide (f p.1 = f p.2)) :=
    ((Easy.fst.compose hf).pair (Easy.snd.compose hf)).compose easy_eqBits
  have e : (fun p : α × α => decide (f p.1 = f p.2)) = fun p => decide (p.1 = p.2) := by
    funext p
    simp [hinj.eq_iff]
  rwa [e] at h

theorem serEntry_inj {a b : Entry} : serEntry a = serEntry b ↔ a = b :=
  ⟨fun h => (pf_serEntry a b [] [] (by simpa using h)).1, fun h => h ▸ rfl⟩

/-- Entry equality through the bit code. -/
theorem easy_eqEntry : Easy (fun p : Entry × Entry => decide (serEntry p.1 = serEntry p.2)) :=
  ((Easy.fst.compose easy_serEntry).pair (Easy.snd.compose easy_serEntry)).compose easy_eqBits

end P1Hier
