import P1SolGreedy.C6Reads
import P1SolGreedy.GreedyDecisions

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

private theorem xorHalves {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (i j : ℕ) :
    (a + 2 ^ n * i) ^^^ (b + 2 ^ n * j) = (a ^^^ b) + 2 ^ n * (i ^^^ j) := by
  rw [← Nat.mod_add_div ((a + 2 ^ n * i) ^^^ (b + 2 ^ n * j)) (2 ^ n)]
  simp only [Nat.xor_mod_two_pow, Nat.xor_div_two_pow, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, zero_add]

private theorem val_two_add (a b : ZMod 2) : (a + b).val = a.val ^^^ b.val := by
  decide +revert

/-- Binary numbering sends addition in the packed bit words to XOR. -/
theorem bitWord_code_add {n : ℕ} (x y : BitWord n) :
    (bitWordFinEquiv n (x + y)).val = (bitWordFinEquiv n x).val ^^^ (bitWordFinEquiv n y).val := by
  induction n with
  | zero =>
    change 0 = (0 : ℕ) ^^^ 0
    simp
  | succ n ih =>
    rw [bitWordFinEquiv_val, bitWordFinEquiv_val n x, bitWordFinEquiv_val n y,
      xorHalves (bitWordFinEquiv n (Fin.tail x)).isLt (bitWordFinEquiv n (Fin.tail y)).isLt]
    change (bitWordFinEquiv n (Fin.tail x + Fin.tail y)).val + 2 ^ n * (x 0 + y 0).val = _
    rw [ih, val_two_add]

theorem bitWord_code_sub {n : ℕ} (x y : BitWord n) :
    (bitWordFinEquiv n (x - y)).val = (bitWordFinEquiv n x).val ^^^ (bitWordFinEquiv n y).val := by
  have h : -y = y := funext fun i => (by decide : ∀ z : ZMod 2, -z = z) (y i)
  rw [sub_eq_add_neg, h, bitWord_code_add]

theorem bitWord_code_zero (n : ℕ) : (bitWordFinEquiv n 0).val = 0 := by
  have h := bitWord_code_add (0 : BitWord n) 0
  simpa only [add_zero, Nat.xor_self] using h

abbrev OptSlotWord := Bool × NumberWord
abbrev TestChoiceWord := Bool × OptSlotWord × OptSlotWord
abbrev TagTestWord := PortWord × TestChoiceWord

def codeOptSlot {d : ℕ} : Option (Fin d) → OptSlotWord
  | none => (false, [])
  | some i => (true, Carry.born i.val)

def codePort {d : ℕ} (p : Bool × Fin d) : PortWord := (p.1, Carry.born p.2.val)

def codeTestChoice {d : ℕ} : Option (Fin d) ⊕ (Option (Fin d) × Option (Fin d)) → TestChoiceWord
  | .inl o => (false, codeOptSlot o, (false, []))
  | .inr (o₁, o₂) => (true, codeOptSlot o₁, codeOptSlot o₂)

def codeTagTest {d : ℕ} (t : SlotGraph.TagTests d) : TagTestWord :=
  (codePort t.1, codeTestChoice t.2)

def optSlotWords (t : TagRow) : List OptSlotWord :=
  (false, []) :: (wordRange t.2.1).map (fun k => (true, k))

@[fun_prop] theorem optSlotWords_poly : Poly optSlotWords := by
  unfold optSlotWords
  fun_prop

def choiceWords (t : TagRow) : List TestChoiceWord :=
  let opts := optSlotWords t
  (opts.map (fun o => (false, o, false, []))) ++ ((opts.product opts).map (fun p => (true, p)))

@[fun_prop] theorem choiceWords_poly : Poly choiceWords := by
  have h := product_poly (false, ([] : NumberWord)) (false, ([] : NumberWord))
  unfold choiceWords
  dsimp only
  fun_prop

def tagTestWords (t : TagRow) : List TagTestWord := (tagPorts t).product (choiceWords t)

@[fun_prop] theorem tagTestWords_poly : Poly tagTestWords := by
  have h := product_poly ((false, []) : PortWord) ((false, (false, []), (false, [])) : TestChoiceWord)
  unfold tagTestWords
  fun_prop

def tagIncrementWord (p : (TagContext × FieldCache) × NumberWord × OptSlotWord) : NumberWord :=
  let r := p.1.1.1.2.2.2
  let Z := p.2.1
  let o := p.2.2
  bif o.1 then
    extractedTag (p.1.1.2, cacheRead (p.1.2, slotAt .outDisp (r, Z, o.2)))
  else []

@[fun_prop] theorem tagIncrementWord_poly : Poly tagIncrementWord := by
  unfold tagIncrementWord
  dsimp only
  fun_prop

def rootShift (p : TagFields × PortWord) : NumberWord :=
  let Y := p.1.1.1.2.2.1
  let r := p.1.1.1.2.2.2
  let k := p.2.2
  let req := bif p.2.1 then slotAt .outDisp (r, Y, k) else slotAt .inDisp (r, Y, k)
  extractedTag (p.1.1.2, cacheRead (p.1.2.1, req))

@[fun_prop] theorem rootShift_poly : Poly rootShift := by unfold rootShift; dsimp only; fun_prop

def maskedTag (p : TagFields × NumberWord) : NumberWord :=
  let q := p.1.1
  let Y := q.1.2.2.1
  let Z := p.2
  let r := q.1.2.2.2
  bif Carry.lt_ (Z, Y) then boundWord (q.2.1.2.2, cacheRead (p.1.2.2, offsetAt (r, Z))) else []

@[fun_prop] theorem maskedTag_poly : Poly maskedTag := by unfold maskedTag; dsimp only; fun_prop

def testTagWord (p : TagFields × TagTestWord) : NumberWord :=
  let q := p.1.1
  let Y := q.1.2.2.1
  let dir := p.2.1
  let t := p.2.2
  let w := rootShift (p.1, dir)
  let Z := neighborAt ((q, p.1.2.1), dir)
  let home₁ := tagIncrementWord ((q, p.1.2.1), Y, t.2.1)
  let home₂ := tagIncrementWord ((q, p.1.2.1), Y, t.2.2)
  let near₁ := tagIncrementWord ((q, p.1.2.2), Z, t.2.1)
  let near₂ := tagIncrementWord ((q, p.1.2.2), Z, t.2.2)
  bif t.1 then
    xorWords ((bif dir.1 then xorWords (xorWords (w, home₁), near₂)
      else xorWords (xorWords (w, near₁), home₂)), maskedTag (p.1, Z))
  else xorWords (w, home₁)

@[fun_prop] theorem testTagWord_poly : Poly testTagWord := by
  unfold testTagWord
  dsimp only
  fun_prop

def forbiddenTagWords (s : TagFields) : List NumberWord :=
  Code.polyPush testTagWord (s, tagTestWords s.1.2)

@[fun_prop] theorem forbiddenTagWords_poly : Poly forbiddenTagWords := by
  have h := Poly.push ((emptyTagContext, [], []) : TagFields)
    (((false, []), false, (false, []), (false, [])) : TagTestWord) testTagWord_poly
  unfold forbiddenTagWords
  fun_prop

def decideTag (s : TagFields) : Bool :=
  let q := s.1
  let Y := q.1.2.2.1
  let r := q.1.2.2.2
  let v := cacheRead (s.2.1, offsetAt (r, Y))
  bif q.1.2.1 then
    leastMissingWords (v, q.2.1.2.2, forbiddenTagWords s, wordRange q.2.2.2)
  else true

theorem decideTag_poly : Poly decideTag := by
  have h := leastMissingWords_poly
  unfold decideTag
  dsimp only
  fun_prop

end P1SolGreedy.SolDemand
