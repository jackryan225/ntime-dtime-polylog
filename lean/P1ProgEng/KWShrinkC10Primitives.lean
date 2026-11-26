import OAI.Computability.IntegerMultiplication.Carry.Figure
import OAI.Computability.MultitapeWeakETH.SyntaxSort
import Mathlib.Data.Nat.Log

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.IntegerMultiplication
open Code Bits Carry

/-- The numeric spelling in the C10 codec. -/
def spell (n : ℕ) : Word := short (Nat.clog 2 (n + 1)) n

scoped instance numCodec : Codec ℕ := ⟨fun n => send (spell n)⟩

theorem send_spell (n : ℕ) : send n = send (spell n) := rfl

theorem send_spell_pair (p : ℕ × ℕ) : send p = send (spell p.1, spell p.2) := rfl

theorem value_spell (n : ℕ) : value (spell n) = n := by
  have h := Nat.le_pow_clog (b := 2) (by decide) (n + 1)
  exact (value_short _ _).trans (Nat.mod_eq_of_lt (by omega))

theorem cut_spell (w : Word) : cut w = spell (value w) := by
  have h := cut_v w
  apply word_inject
  · rw [spell, short_length]
    exact (measure _ _ (by rw [h.1]; omega) h.2.2).symm
  · rw [h.1, value_spell]

theorem binary₂ {f : ℕ → ℕ → ℕ} {g : Word × Word → Word}
    (hg : Poly g) (hv : ∀ x y, value (g (x, y)) = f (value x) (value y)) :
    Poly (fun p : ℕ × ℕ => f p.1 p.2) := by
  obtain ⟨t, ht, h⟩ := hg.compose polyCut
  refine ⟨fun p => t (spell p.1, spell p.2), ?_, ?_⟩
  · exact ht.map _
  · change Task _ (fun p : ℕ × ℕ => send (spell p.1, spell p.2))
      (fun p : ℕ × ℕ => send (spell (f p.1 p.2)))
    simpa only [cut_spell, hv, value_spell] using h.on (fun p : ℕ × ℕ => (spell p.1, spell p.2))

theorem binary₁ {f : ℕ → ℕ} {g : Word → Word}
    (hg : Poly g) (hv : ∀ x, value (g x) = f (value x)) : Poly f := by
  obtain ⟨t, ht, h⟩ := hg.compose polyCut
  refine ⟨fun n => t (spell n), ht.map _, ?_⟩
  change Task _ (fun p : ℕ => send (spell p)) (fun p : ℕ => send (spell (f p)))
  simpa only [cut_spell, hv, value_spell] using h.on spell

theorem binaryCmp {f : ℕ → ℕ → Bool} {g : Word × Word → Bool}
    (hg : Poly g) (hv : ∀ x y, g (x, y) = f (value x) (value y)) :
    Poly (fun p : ℕ × ℕ => f p.1 p.2) := by
  obtain ⟨t, ht, h⟩ := hg
  refine ⟨fun p => t (spell p.1, spell p.2), ht.map _, ?_⟩
  change Task _ (fun p : ℕ × ℕ => send (spell p.1, spell p.2)) (fun p : ℕ × ℕ => send (f p.1 p.2))
  simpa only [hv, value_spell] using h.on (fun p : ℕ × ℕ => (spell p.1, spell p.2))

@[fun_prop] theorem add_poly : Poly (fun p : ℕ × ℕ => p.1 + p.2) :=
  binary₂ swift add_val

@[fun_prop] theorem sub_poly : Poly (fun p : ℕ × ℕ => p.1 - p.2) :=
  binary₂ sub0_r sub0_v

@[fun_prop] theorem mul_poly : Poly (fun p : ℕ × ℕ => p.1 * p.2) :=
  binary₂ polyTime tm_value

@[fun_prop] theorem div_poly : Poly (fun p : ℕ × ℕ => p.1 / p.2) :=
  binary₂ polyND.fstCompose (fun x y => (division_rules x y).1)

@[fun_prop] theorem mod_poly : Poly (fun p : ℕ × ℕ => p.1 % p.2) :=
  binary₂ polyND.sndCompose (fun x y => (division_rules x y).2)

@[fun_prop] theorem sqrt_poly : Poly Nat.sqrt := binary₁ rescuePoly rescued

@[fun_prop] theorem lt_poly : Poly (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
  binaryCmp (f := fun x y => decide (x < y)) ltPoly lt_r

@[fun_prop] theorem eq_poly : Poly (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  have h : Poly (fun p : ℕ × ℕ => !(decide (p.1 < p.2) || decide (p.2 < p.1))) :=
    ((lt_poly.pair (Easy.exchange.poly.compose lt_poly)).compose Iter.conn_easy.poly).compose
      Iter.negate.poly
  convert h using 1
  funext p
  obtain hlt | heq | hgt := lt_trichotomy p.1 p.2
  · simp [hlt, ne_of_lt hlt]
  · simp [heq]
  · simp [hgt, ne_of_gt hgt, not_lt_of_gt hgt]

theorem eqOn_poly {X : Type} [Codec X] {f g : X → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x = g x)) :=
  (hf.pair hg).compose eq_poly

theorem ltOn_poly {X : Type} [Codec X] {f g : X → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x < g x)) :=
  (hf.pair hg).compose lt_poly

private def xorWords (p : Word × Word) : Word :=
  (zipSafe false false p).map (fun b => b.1 ^^ b.2)

private theorem xorWords_poly : Poly xorWords :=
  (easy_zipSafe false false Easy.identity).poly.compose
    (Poly.maps _ (Easy.finite (fun p : Bool × Bool => p.1 ^^ p.2)).poly)

private theorem xorValue (x y : Word) : value (xorWords (x, y)) = value x ^^^ value y := by
  have eq (a b : Word) (len : a.length = b.length) :
      value ((a.zip b).map fun p => p.1 ^^ p.2) = value a ^^^ value b := by
    induction a generalizing b with
    | nil => cases b <;> simp_all
    | cons c a ih =>
      cases b with
      | nil => simp at len
      | cons e b =>
        have tail := ih b (by simpa using len)
        change digit (c ^^ e) + 2 * value ((a.zip b).map fun t => t.1 ^^ t.2) =
          (digit c + 2 * value a) ^^^ (digit e + 2 * value b)
        rw [tail]
        have step (b : Bool) (n : ℕ) : digit b + 2 * n = Nat.bit b n := by
          cases b <;> simp [Nat.bit_val, Nat.add_comm]
        simp only [step]
        apply Nat.eq_of_testBit_eq
        intro j
        cases j <;> simp only [Nat.testBit_xor, Nat.testBit_bit_zero, Nat.testBit_bit_succ]
  have := eq (x ++ List.replicate y.length false) (y ++ List.replicate x.length false)
    (by simp [Nat.add_comm])
  simpa only [xorWords, zipSafe, value_append, zeroes, mul_zero, add_zero] using this

@[fun_prop] theorem xor_poly : Poly (fun p : ℕ × ℕ => p.1 ^^^ p.2) :=
  binary₂ xorWords_poly xorValue

@[fun_prop] theorem length_poly {T : Type} [Codec T] : Poly (List.length : List T → ℕ) := by
  have hp := (Easy.ruler (X := T) Easy.identity).poly.compose easy_chart.poly
  obtain ⟨t, ht, h⟩ := hp.compose polyCut
  exact ⟨t, ht, by simpa only [cut_spell, birthValue, ruler_length, send_spell, id_eq] using h⟩

/-- The tally length is bounded by the supplied list even on malformed indexes. -/
theorem cappedTally_poly {T : Type} [Codec T] :
    Poly (fun p : List T × ℕ => tally (min p.1.length p.2)) := by
  let cap : List T × ℕ → ℕ := fun p => min p.1.length p.2
  have hc : Poly cap := by
    have ht : Poly (fun p : List T × ℕ => decide (p.1.length < p.2)) :=
      ((Easy.fst.poly.compose length_poly).pair Easy.snd.poly).compose lt_poly
    have h := Poly.choose ht (Easy.fst.poly.compose length_poly) Easy.snd.poly
    convert h using 1
    funext p
    by_cases hp : p.1.length < p.2
    · simp [cap, hp, min_eq_left hp.le]
    · simp [cap, hp, min_eq_right (Nat.le_of_not_gt hp)]
  have hs : Dom size (fun p => size (spell (cap p)) + value (spell (cap p))) :=
    (hc.length.add (Dom.base _)).mono fun p => by
      rw [value_spell]
      change size (cap p) + cap p ≤ size (cap p) + size p
      exact Nat.add_le_add_left ((min_le_left ..).trans <|
        (duration p.1).le.trans (by rw [size_prod]; omega)) _
  obtain ⟨t, h₀⟩ := hc
  obtain ⟨hd, h₀⟩ := h₀
  have hu : Task (fun p => size (spell (cap p)) + value (spell (cap p)))
      (fun p => send (cap p)) (fun p => send (tally (cap p))) := by
    simpa only [value_spell, send_spell] using rice.on (fun p => spell (cap p))
  exact ⟨_, hd.add hs, h₀.compose hu⟩

def read {T : Type} (d : T) (xs : List T) (i : ℕ) : T := xs[i]?.getD d

@[fun_prop] theorem read_poly {T : Type} [Codec T] (d : T) :
    Poly (fun p : List T × ℕ => read d p.1 p.2) := by
  have h := (Easy.fst.poly.pair (cappedTally_poly (T := T))).compose (Iter.facile d).poly
  convert h using 1
  funext p
  obtain ⟨xs, i⟩ := p
  by_cases hi : i < xs.length
  · simp only [Nat.min_eq_right hi.le, read, getElem?_pos xs i hi, Option.getD_some]
    exact (Iter.search _ _ _ hi).symm
  · have hle := Nat.le_of_not_gt hi
    simp only [Nat.min_eq_left hle, read, getElem?_neg xs i hi, Option.getD_none,
      Iter.pick, tally_length, List.drop_length, List.headD_nil]

@[fun_prop] theorem fixedList_poly {I T : Type} [Codec I] [Codec T]
    {n : ℕ} (f : I → Fin n → T) (hf : ∀ j, Poly (fun i => f i j)) :
    Poly (fun i => List.ofFn (f i)) := by
  induction n with
  | zero => simpa only [List.ofFn_zero] using (Code.Poly.const ([] : List T) (X := I))
  | succ n ih =>
    simpa only [List.ofFn_succ] using
      ((hf 0).pair (ih (fun i j => f i j.succ) (fun j => hf j.succ))).compose Code.Poly.cons

@[fun_prop] theorem tallyToNat_poly : Poly (List.length : Tally → ℕ) := length_poly

@[fun_prop] theorem poly_some {T : Type} [Codec T] : Poly (@some T) := Easy.some.poly

@[fun_prop] theorem poly_fst {S T : Type} [Codec S] [Codec T] :
    Poly (Prod.fst : S × T → S) := Easy.fst.poly

@[fun_prop] theorem poly_snd {S T : Type} [Codec S] [Codec T] :
    Poly (Prod.snd : S × T → T) := Easy.snd.poly

@[fun_prop] theorem bool_and_poly : Poly (fun p : Bool × Bool => p.1 && p.2) :=
  (Easy.finite _).poly

@[fun_prop] theorem bool_or_poly : Poly (fun p : Bool × Bool => p.1 || p.2) :=
  Iter.conn_easy.poly

@[fun_prop] theorem bool_not_poly : Poly Bool.not := Iter.negate.poly

@[fun_prop] theorem flatten_poly {T : Type} [Codec T] :
    Poly (List.flatten : List (List T) → List T) := Easy.flatten.poly

@[fun_prop] theorem head_poly {T : Type} [Codec T] (d : T) :
    Poly (fun xs : List T => xs.headD d) := (Iter.leader d).poly

@[fun_prop] theorem empty_poly {T : Type} [Codec T] :
    Poly (List.isEmpty : List T → Bool) := (vacant T).poly

open Code.Task in
/-- Option elimination, using the atom/fork representation of the option codec.
This is the same tape construction as `NearSquareRoot.PhaseTable.easyOption`. -/
theorem easyOption {X Y : Type} [Codec X] [Codec Y] (d : Y) (f : X → Y)
    (F : Easy f) : Easy (fun o : Option X => o.elim d f) := by
  have q : Easy (fun p : Bool × X => f p.2) := Easy.snd.compose F
  obtain ⟨c, C, hc⟩ := q
  refine ⟨splitRoot 0 (fun _ => Task.prepare 0 (send d)) (.join (pack 0) c),
    C + 5 * (send d).count + 7, fun x env r => ?_⟩
  cases x with
  | none =>
    refine (fits_bit (b := false) (c := fun _ => Task.prepare 0 (send d))
      (fits_prepare _ _ _ _)).mono ?_
    simp only [size_none, Nat.add_mul]
    omega
  | some y =>
    have hh := hc (true, y) env r
    refine (fits_pair ((fits_pack _ _ _ _ _).join hh)).mono ?_
    simp only [size_some, size_prod, size_bit, Nat.add_mul]
    rw [show 1 + Code.size y + 1 + 1 = Code.size y + 2 + 1 by omega]
    omega

@[fun_prop] theorem getD_poly {T : Type} [Codec T] (d : T) :
    Poly (fun o : Option T => o.getD d) := by
  have h : (fun o : Option T => o.getD d) = (fun o => o.elim d id) := by
    funext o
    cases o <;> rfl
  rw [h]
  exact (easyOption d id Easy.identity).poly

@[fun_prop] theorem isSome_poly {T : Type} [Codec T] :
    Poly (Option.isSome : Option T → Bool) := by
  have h : (Option.isSome : Option T → Bool) = (fun o => o.elim false (fun _ => true)) := by
    funext o
    cases o <;> rfl
  rw [h]
  exact (easyOption false (fun _ : T => true) (Easy.const _)).poly

/-- Map with polynomial-time access to a common input for each element. -/
@[fun_prop] theorem mapWith_poly {A S T : Type} [Codec A] [Codec S] [Codec T]
    [Inhabited A] [Inhabited S] (f : A × S → T) (h : Poly f) :
    Poly (fun p : A × List S => p.2.map (fun s => f (p.1, s))) :=
  Code.Poly.push default default h

/-- Filter with polynomial-time access to a common input for each element. -/
@[fun_prop] theorem filterWith_poly {A S : Type} [Codec A] [Codec S]
    [Inhabited A] [Inhabited S] (f : A × S → Bool) (h : Poly f) :
    Poly (fun p : A × List S => p.2.filter (fun s => f (p.1, s))) := by
  have hs : Poly (fun p : A × S => bif f p then [p.2] else []) :=
    Code.Poly.choose h
      ((poly_snd.pair (Code.Poly.const ([] : List S))).compose Code.Poly.cons)
      (Code.Poly.const [])
  have hm := (mapWith_poly _ hs).compose flatten_poly
  convert hm using 1
  funext p
  obtain ⟨a, xs⟩ := p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (x :: xs).filter _ =
      (bif f (a, x) then [x] else []) ++ (xs.map _).flatten
    cases hfx : f (a, x) <;> simp only [List.filter_cons, hfx, Bool.cond_true,
      Bool.cond_false, Bool.false_eq_true, ite_false, ite_true, List.nil_append, List.singleton_append, ih]

def lookup {T : Type} (d : T) (xs : List (ℕ × T)) (i : ℕ) : T :=
  ((xs.filter (fun a => decide (i = a.1))).headD (i, d)).2

@[fun_prop] theorem lookup_poly {T : Type} [Codec T] [Inhabited T] (d : T) :
    Poly (fun p : List (ℕ × T) × ℕ => lookup d p.1 p.2) := by
  have h := filterWith_poly (fun p : ℕ × (ℕ × T) => decide (p.1 = p.2.1))
    ((poly_fst.pair poly_snd.fstCompose).compose eq_poly)
  have h' := Easy.exchange.poly.compose h
  unfold lookup
  have hd : Poly (fun p : List (ℕ × T) × ℕ => ((p.1.filter (fun a => decide (p.2 = a.1))).headD (0, d)).2) :=
    (h'.compose (head_poly (0, d))).sndCompose
  convert hd using 1
  funext p
  cases e : p.1.filter (fun a => decide (p.2 = a.1)) <;> rfl

theorem lookup_eq_of_mem {T : Type} {xs : List (ℕ × T)} {i : ℕ} {v d : T}
    (hmem : (i, v) ∈ xs) (hval : ∀ w, (i, w) ∈ xs → w = v) : lookup d xs i = v := by
  unfold lookup
  have he : (i, v) ∈ xs.filter (fun a => decide (i = a.1)) :=
    List.mem_filter.mpr ⟨hmem, by simp⟩
  cases h : xs.filter (fun a => decide (i = a.1)) with
  | nil => simp only [h, List.not_mem_nil] at he
  | cons a as =>
    have ha := List.mem_filter.mp (h.symm ▸ List.mem_cons_self (a := a) (l := as))
    have hi : i = a.1 := of_decide_eq_true ha.2
    exact hval a.2 (by rw [hi]; exact ha.1)

theorem lookup_default_of_absent {T : Type} (d : T) (xs : List (ℕ × T)) (i : ℕ)
    (h : i ∉ xs.map Prod.fst) : lookup d xs i = d := by
  unfold lookup
  have hf : xs.filter (fun a => decide (i = a.1)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨hx, he⟩ := List.mem_filter.mp ha
    exact h ((of_decide_eq_true he).symm ▸ List.mem_map_of_mem hx)
  rw [hf]
  rfl

private def addUnique (p : List ℕ × ℕ) : List ℕ :=
  bif (p.1.filter (fun i => decide (p.2 = i))).isEmpty then p.2 :: p.1 else p.1

private theorem addUnique_poly : Poly addUnique := by
  unfold addUnique
  have hf := Easy.exchange.poly.compose (filterWith_poly
    (fun p : ℕ × ℕ => decide (p.1 = p.2)) eq_poly)
  exact Code.Poly.choose (hf.compose empty_poly)
    (Easy.exchange.poly.compose Code.Poly.cons) poly_fst

private theorem addUnique_spec (xs : List ℕ) (i : ℕ) :
    addUnique (xs, i) = if i ∈ xs then xs else i :: xs := by
  unfold addUnique
  by_cases hm : i ∈ xs
  · have hr : i ∈ xs.filter (fun n => decide (i = n)) := List.mem_filter.mpr ⟨hm, by simp⟩
    cases h : xs.filter (fun n => decide (i = n)) with
    | nil => simp only [h, List.not_mem_nil] at hr
    | cons j js => simp only [List.isEmpty_cons, Bool.cond_false, hm, ite_true]
  · have hr : xs.filter (fun n => decide (i = n)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      obtain ⟨hj, h⟩ := List.mem_filter.mp hj
      exact hm ((of_decide_eq_true h).symm ▸ hj)
    simp only [hr, List.isEmpty_nil, Bool.cond_true, hm, ite_false]

def unique (xs : List ℕ) : List ℕ := xs.foldl (fun a b => addUnique (a, b)) []

private theorem unique_bound (acc xs : List ℕ) :
    size (xs.foldl (fun a b => addUnique (a, b)) acc) ≤ size acc + size xs := by
  induction xs generalizing acc with
  | nil => exact Nat.le_add_right _ _
  | cons j js ih =>
    rw [List.foldl_cons]
    refine (ih _).trans ?_
    by_cases hj : j ∈ acc <;> simp only [addUnique_spec, hj, ite_true, ite_false, size_cons] <;> omega

@[fun_prop] theorem unique_poly : Poly unique := by
  have h := Code.Poly.fold_left addUnique_poly 2 1 (fun s l hl => by
    have hs := unique_bound s.2 l
    have hp : size l ≤ size s.1 := by
      obtain ⟨t, ht⟩ := hl
      rw [← ht]
      have hsz := size_append_right l t
      have hp := size_pos t
      omega
    rw [pow_one, size_prod]
    omega)
  exact (Code.Poly.identity.pair (Code.Poly.const ([] : List ℕ))).compose h

theorem unique_spec (xs : List ℕ) : (unique xs).Nodup ∧ ∀ i, i ∈ unique xs ↔ i ∈ xs := by
  have h (xs acc : List ℕ) (hn : acc.Nodup) :
      let out := xs.foldl (fun a b => addUnique (a, b)) acc
      out.Nodup ∧ ∀ i, i ∈ out ↔ i ∈ xs ∨ i ∈ acc := by
    induction xs generalizing acc with
    | nil => exact ⟨hn, fun i => by simp only [List.foldl_nil, List.not_mem_nil, false_or]⟩
    | cons j js ih =>
      dsimp only
      rw [List.foldl_cons, addUnique_spec acc j]
      by_cases hj : j ∈ acc
      · rw [ite_eq_left hj]
        obtain ⟨hn', hmem⟩ := ih acc hn
        refine ⟨hn', fun i => ?_⟩
        rw [hmem, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rintro ((rfl | h) | h)
          · exact Or.inr hj
          · exact Or.inl h
          · exact Or.inr h
      · rw [ite_eq_right hj]
        obtain ⟨hn', hmem⟩ := ih (j :: acc) (List.nodup_cons.mpr ⟨hj, hn⟩)
        refine ⟨hn', fun i => ?_⟩
        simp only [hmem, List.mem_cons]
        tauto
  simpa only [unique, List.not_mem_nil, or_false] using h xs [] List.nodup_nil

/-- All zero-based positions of a stored list, in increasing order. -/
def positions {T : Type} (xs : List T) : List ℕ := List.ofFn fun i : Fin xs.length => i.val

@[fun_prop] theorem positions_poly {T : Type} [Codec T] : Poly (positions (T := T)) := by
  have hr := (Easy.ruler (X := T) Easy.identity).poly.compose Iter.poly_line
  have hm := hr.compose (Code.Poly.maps _ tallyToNat_poly)
  convert hm using 1
  funext xs
  simp only [positions, Iter.lineup, id_eq, ruler_length, List.map_ofFn, Function.comp_def, tally_length, Fin.val_cast]

/-- List indices below a numeric cap, with a cost governed by the stored list. -/
def limitedPositions {T : Type} (xs : List T) (cap : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (min xs.length cap) => i.val

@[fun_prop] theorem limitedPositions_poly {T : Type} [Codec T] :
    Poly (fun p : List T × ℕ => limitedPositions p.1 p.2) := by
  have h := (cappedTally_poly (T := T)).compose (positions_poly (T := Unit))
  have he (n : ℕ) : positions (tally n) = List.ofFn (fun i : Fin n => i.val) :=
    congrArg (fun m => List.ofFn fun i : Fin m => i.val) (tally_length n)
  simpa only [limitedPositions, he] using h

end P1ProgEng.SolKWS.C10
