import P1Hier.UMachine

/-! A linear prefix reader for the wire constructors used by the universal machine.
The input and output occupy different registers. Reading a product left to right
leaves its flipped tree on the output stack, in the order required by `pack`. -/

namespace P1Hier.AstraParse

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

abbrev Bits := List Bool

def unitWord (_ : Unit) : Bits := []
def bitWord (b : Bool) : Bits := [b]

def prodWord {α β : Type} (s : α → Bits) (t : β → Bits) (p : α × β) : Bits :=
  s p.1 ++ t p.2

def sumWord {α β : Type} (s : α → Bits) (t : β → Bits) : α ⊕ β → Bits
  | .inl a => false :: s a
  | .inr b => true :: t b

def optionWord {α : Type} (s : α → Bits) : Option α → Bits
  | none => [false]
  | some a => true :: s a

private def input (w : Bits) (r : Deck) := pile 0 (send w) r
private def output (v : Tree) (r : Deck) := pile 1 v r

private theorem output_input (v : Tree) (w : Bits) (r : Deck) :
    output v (input w r) = input w (output v r) :=
  pile_comm 1 v r 0 (send w) (by decide)

private theorem emitAtom (b : Bool) (w : Bits) (G : Env) (r : Deck) :
    Fits G (give 1 b) (input w r) (input w (output (.atom b) r)) 1 := by
  rw [← output_input]
  exact fits_give b (input w r) 1 G

private theorem emitFork (x y : Tree) (w : Bits) (G : Env) (r : Deck) :
    Fits G (pack 1) (input w (output x (output y r)))
      (input w (output (.fork x y) r)) 1 := by
  have h := fits_pack x y (input w r) 1 G
  change Fits G (pack 1) (output x (output y (input w r)))
    (output (.fork x y) (input w r)) 1 at h
  simpa only [output_input] using h

private def nextBit (k : Bool → Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) (splitRoot 0 k .pass)

private theorem consume (k : Bool → Cmd) (b : Bool) {w : Bits} {r q : Deck} {G : Env} {n : ℕ}
    (h : Fits G (k b) (input w r) q n) :
    Fits G (nextBit k) (input (b :: w) r) q (n + 4 + 4) :=
  fits_pair (c := fun _ => .pass) (fits_bit (c := k) (d := .pass) h)

/-- The residual word and every parked stack entry are available to the next call.
The cost is independent of both the residual word and the parked entries. -/
def Reads {α : Type} [Codec α] (s : α → Bits) : Prop :=
  ∃ p : Cmd, ∃ K : ℕ, ∀ (a : α) (w : Bits) (G : Env) (r : Deck),
    Fits G p (input (s a ++ w) r) (input w (output (send a).flip r))
      (K * ((s a).length + 1))

namespace Reads

variable {α β : Type} [Codec α] [Codec β] {s : α → Bits} {t : β → Bits}

theorem via (h : Reads s) (f : β → α) (hw : ∀ b, s (f b) = t b)
    (hv : ∀ b, send (f b) = send b) : Reads t := by
  obtain ⟨p, K, hp⟩ := h
  exact ⟨p, K, fun b w G r => by simpa only [hw, hv] using hp (f b) w G r⟩

theorem unit : Reads unitWord := by
  exact ⟨give 1 false, 1, fun _ w G r => emitAtom false w G r⟩

theorem bit : Reads bitWord := by
  refine ⟨nextBit (give 1), 9, fun b w G r => ?_⟩
  exact (consume (give 1) b (emitAtom b w G r)).mono (by change 9 ≤ 18; decide)

theorem prod (hs : Reads s) (ht : Reads t) : Reads (prodWord s t) := by
  obtain ⟨p, A, hp⟩ := hs
  obtain ⟨q, B, hq⟩ := ht
  refine ⟨p.join (q.join (pack 1)), A + B + 8, ?_⟩
  rintro ⟨a, b⟩ w G r
  have h₁ := hp a (t b ++ w) G r
  have h₂ := hq b w G (output (send a).flip r)
  have h₃ := emitFork (send b).flip (send a).flip w G r
  change Fits G _ (input ((s a ++ t b) ++ w) r)
    (input w (output (.fork (send b).flip (send a).flip) r))
    ((A + B + 8) * ((s a ++ t b).length + 1))
  rw [List.append_assoc]
  apply (h₁.join (h₂.join h₃)).mono
  simp only [List.length_append, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

private def tagCmd (b : Bool) (p : Cmd) : Cmd :=
  (give 1 b).join (p.join (pack 1))

private theorem tagRun (b : Bool) (p : Cmd) (v : Tree) (w z : Bits) (G : Env) (r : Deck)
    (n : ℕ) (h : ∀ d, Fits G p (input w d) (input z (output v d)) n) :
    Fits G (tagCmd b p) (input w r) (input z (output (.fork v (.atom b)) r))
      (1 + (n + 1 + 2) + 2) :=
  (emitAtom b w G r).join ((h (output (.atom b) r)).join (emitFork v (.atom b) z G r))

theorem sum (hs : Reads s) (ht : Reads t) : Reads (sumWord s t) := by
  obtain ⟨p, A, hp⟩ := hs
  obtain ⟨q, B, hq⟩ := ht
  let k (b : Bool) := bif b then tagCmd true q else tagCmd false p
  refine ⟨nextBit k, A + B + 20, ?_⟩
  intro v w G r
  cases v with
  | inl a =>
    have h := tagRun false p (send a).flip (s a ++ w) w G r _ (hp a w G)
    apply (consume k false h).mono
    simp only [sumWord, List.length_cons, Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  | inr b =>
    have h := tagRun true q (send b).flip (t b ++ w) w G r _ (hq b w G)
    apply (consume k true h).mono
    simp only [sumWord, List.length_cons, Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

theorem option (hs : Reads s) : Reads (optionWord s) := by
  obtain ⟨p, A, hp⟩ := hs
  let k (b : Bool) := bif b then tagCmd true p else give 1 false
  refine ⟨nextBit k, A + 20, ?_⟩
  intro v w G r
  cases v with
  | none =>
    apply (consume k false (emitAtom false w G r)).mono
    simp only [optionWord, List.length_cons, List.length_nil, Nat.add_mul]
    omega
  | some a =>
    have h := tagRun true p (send a).flip (s a ++ w) w G r _ (hp a w G)
    apply (consume k true h).mono
    simp only [optionWord, List.length_cons, Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

private def listArm (p : Cmd) (b : Bool) : Cmd :=
  bif b then p.join ((Prog.again 0).join (pack 1)) else give 1 false

theorem list (hs : Reads s) : Reads (serL s) := by
  obtain ⟨p, A, hp⟩ := hs
  let body := nextBit (listArm p)
  refine ⟨.tie body, A + 20, ?_⟩
  intro as w G r
  have run : ∀ (l : List α) (z : Bits) (d : Deck),
      Fits (body :: G) body (input (serL s l ++ z) d)
        (input z (output (send l).flip d)) ((A + 20) * (serL s l).length) := by
    intro l
    induction l with
    | nil =>
      intro z d
      apply (consume (listArm p) false (emitAtom false z (body :: G) d)).mono
      simp only [serL_nil, List.length_cons, List.length_nil, Nat.mul_one]
      omega
    | cons a l ih =>
      intro z d
      have ha := hp a (serL s l ++ z) (body :: G) d
      have hl := Fits.again0 (ih z (output (send a).flip d))
      have he := emitFork (send l).flip (send a).flip z (body :: G) d
      rw [serL_cons, List.cons_append, List.append_assoc]
      apply (consume (listArm p) true (ha.join (hl.join he))).mono
      simp only [List.length_cons, List.length_append, Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega
  apply (Fits.tie (run as w r)).mono
  simp only [Nat.mul_add, Nat.mul_one]
  omega

open private runBound from OAI.Computability.IntegerMultiplication.Code.Product in
/-- One forward pass restores the orientation and puts the value above its residual
word. Each output letter required a push during parsing, which pays for this pass. -/
theorem task (hs : Reads s) :
    Task (fun i : α × Bits => size (s i.1 ++ i.2))
      (fun i => send (s i.1 ++ i.2)) (fun i => send i) := by
  obtain ⟨p, K, hp⟩ := hs
  refine ⟨p.join ((forward 1 [0]).join (pack 0)), 21 * K + 8, ?_⟩
  rintro ⟨a, w⟩ G r
  have h₁ := hp a w G r
  obtain ⟨j, hj, run⟩ := h₁
  have hsize := runBound run 1
  simp only [input, output, pile_far 0 1 (by decide), letters_here, List.length_append,
    Tree.spell_length, Tree.count_flip] at hsize
  have hv : (send a).count ≤ K * ((s a).length + 1) := by omega
  have h₂ := fits_forward 1 [0] (by decide) (by decide) G (send a).flip (input w r)
  change Fits G (forward 1 [0]) (output (send a).flip (input w r))
    (pile 0 (send a).flip.flip (input w r)) (20 * (send a).flip.count) at h₂
  rw [output_input, Tree.flip_flip, Tree.count_flip] at h₂
  have h₃ := fits_pack (send a) (send w) r 0 G
  apply ((hp a w G r).join (h₂.join h₃)).mono
  have hw : (s a).length + 1 ≤ size (s a ++ w) + 1 := by
    rw [UM.size_bits', List.length_append]
    omega
  have hm := Nat.mul_le_mul_left K hw
  change K * ((s a).length + 1) + (20 * (send a).count + 1 + 2) + 2 ≤
    (21 * K + 8) * (size (s a ++ w) + 1)
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

end Reads

end P1Hier.AstraParse
