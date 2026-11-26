import P1SolCone.Tables
import P1P5.KWRefresh
import P1ChkFinal.Progs
import P1ChkDir.NatPoly
import P1Batch.Statement

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10 P1ProgEng.SolKWR

private abbrev WordState := Tally × List (List Bool)

private def extendWords (p : WordState × Unit) : WordState :=
  let (fuel, ws) := p.1
  (fuel, ((ws.map (false :: ·)) ++ (ws.map (true :: ·))).take fuel.length)

private theorem extendWords_poly : Poly extendWords := by
  have fuel : Poly (fun p : WordState × Unit => p.1.1) := (Easy.fst.compose Easy.fst).poly
  have words : Poly (fun p : WordState × Unit => p.1.2) := (Easy.fst.compose Easy.snd).poly
  have zeros : Easy (fun w : List Bool => false :: w) := by fun_prop
  have ones : Easy (fun w : List Bool => true :: w) := by fun_prop
  have full := (words.compose (Easy.mapping zeros).poly).app (words.compose (Easy.mapping ones).poly)
  exact fuel.pair (poly_take (poly_lengthNat fuel) full)

private theorem size_wordList_le (ws : List (List Bool)) (n : ℕ) (h : ∀ w ∈ ws, w.length ≤ n) :
    size ws ≤ ws.length * (2 * n + 2) + 1 := by
  induction ws with
  | nil => simp [size_nil]
  | cons w ws ih =>
    have hw := h w List.mem_cons_self
    have ht := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    rw [size_cons, P1ChkFinal.size_listBool, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem wordFold_poly :
    Poly (fun q : Tally × WordState => q.1.foldl (fun p a => extendWords (p, a)) q.2) := by
  -- The fold starts from an arbitrary state, so retain its initial words in the size bound.
  apply Poly.fold_left extendWords_poly 8 2
  intro q clock hc
  let output := clock.foldl (fun p a => extendWords (p, a)) q.2
  change size output ≤ 8 * (size q + 1) ^ 2
  have bound (t : Tally) (st : WordState) :
      let s := t.foldl (fun p a => extendWords (p, a)) st
      s.1 = st.1 ∧ s.2.length ≤ max st.2.length st.1.length ∧
        ∀ v ∈ s.2, v.length ≤ size st.2 + t.length := by
    induction t using List.reverseRecOn with
    | nil =>
      exact ⟨rfl, le_max_left _ _, fun v hv => by
        have he := (size_bel hv).le
        rw [P1ChkFinal.size_listBool] at he
        simp only [List.foldl_nil, List.length_nil, Nat.add_zero] at he ⊢
        omega⟩
    | append_singleton t a ih =>
      rw [List.foldl_append]
      let s := t.foldl (fun p a => extendWords (p, a)) st
      let ws := (s.2.map (false :: ·)) ++ (s.2.map (true :: ·))
      change s.1 = st.1 ∧ (ws.take s.1.length).length ≤ max st.2.length st.1.length ∧
        ∀ v ∈ ws.take s.1.length, v.length ≤ size st.2 + (t ++ [a]).length
      have hf : s.1 = st.1 := ih.1
      simp only [hf, List.length_take, List.length_append, List.length_singleton]
      refine ⟨True.intro, (min_le_left _ _).trans (le_max_right _ _), fun v hv => ?_⟩
      change v ∈ ((s.2.map (false :: ·) ++ s.2.map (true :: ·)).take st.1.length) at hv
      have hh := (List.take_sublist _ _).subset hv
      rcases List.mem_append.mp hh with h | h
      all_goals
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
        exact Nat.add_le_add_right (ih.2.2 z hz) 1
  have h := bound clock q.2
  have hclock : clock.length ≤ size q.1 := hc.length_le.trans (by rw [size_tally]; omega)
  have hcount : output.2.length ≤ size q := h.2.1.trans (by
    apply max_le
    · have hh := duration q.2.2
      simp only [size_prod] at *
      omega
    · simp only [size_prod, size_tally]
      omega)
  have hwidth : ∀ v ∈ output.2, v.length ≤ size q := fun v hv =>
    (h.2.2 _ hv).trans (by simp only [size_prod]; omega)
  have hf : size output.1 ≤ size q := by
    rw [h.1]
    simp only [size_prod]
    omega
  have hwords := (size_wordList_le output.2 (size q) hwidth).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcount) 1)
  calc
    size output ≤ size q + (size q * (2 * size q + 2) + 1) + 1 := by
      rw [size_prod]
      exact Nat.add_le_add_right (Nat.add_le_add hf hwords) _
    _ ≤ _ := by nlinarith

/-- Enumerate words in binary order using a tally to cap every intermediate list. -/
def boundedWords (p : ℕ × Tally) : List (List Bool) :=
  ((tally (min p.1 p.2.length)).foldl (fun s a => extendWords (s, a)) (p.2, [[]])).2

theorem boundedWords_poly : Poly boundedWords := by
  have fuel : Poly (fun p : ℕ × Tally => p.2) := Easy.snd.poly
  have clock := poly_tallyCap 1 (Easy.fst.poly : Poly (fun p : ℕ × Tally => p.1)) fuel
  have start := fuel.pair (Code.Poly.const ([[]] : List (List Bool)))
  show Poly (fun p : ℕ × Tally =>
    ((tally (min p.1 p.2.length)).foldl (fun s a => extendWords (s, a)) (p.2, [[]])).2)
  simpa only [Nat.one_mul] using ((clock.pair start).compose wordFold_poly).sndCompose

theorem boundedWords_eq (w : ℕ) (fuel : Tally) (h : 2 ^ w ≤ fuel.length) :
    boundedWords (w, fuel) = bitWords w := by
  have fold (n : ℕ) (hn : 2 ^ n ≤ fuel.length) :
      (tally n).foldl (fun s a => extendWords (s, a)) (fuel, [[]]) = (fuel, bitWords n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn' : 2 ^ n ≤ fuel.length := (Nat.pow_le_pow_right (by decide) (Nat.le_succ n)).trans hn
      have hclock : tally (n + 1) = tally n ++ [()] := by
        simp [tally, List.replicate_add]
      rw [hclock, List.foldl_append, ih hn']
      change (fuel, (bitWords (n + 1)).take fuel.length) = _
      rw [List.take_of_length_le (by rw [length_bitWords]; exact hn)]
  unfold boundedWords
  rw [min_eq_left (Nat.lt_two_pow_self.le.trans h), fold w h]

/-- The least-significant-bit-first encoding of a power of two, from a unary exponent. -/
def powTwoWord (s : Tally) : List Bool := (s.map (fun _ => false)) ++ [true]

theorem powTwoWord_easy : Easy powTwoWord := by
  unfold powTwoWord
  fun_prop

theorem bval_powTwoWord (s : Tally) : P1Batch.bval (powTwoWord s) = 2 ^ s.length := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    change P1Batch.bval (false :: powTwoWord s) = 2 ^ (s.length + 1)
    simp only [P1Batch.bval, Bool.toNat_false, Nat.zero_add, ih, pow_succ']

/-- Allocate a power-of-two tally in time linear in its length. -/
theorem powTwoTally_computes :
    Computes (fun s : Tally => 2 ^ s.length) (fun s => tally (2 ^ s.length)) := by
  have h := Task.compose (show Computes size powTwoWord from powTwoWord_easy)
    (P1Batch.countdown.on powTwoWord)
  refine (h.conform (fun _ => rfl) (fun _ => rfl) (fun s => by rw [bval_powTwoWord])).bound 6
    (fun s => ?_)
  have hb := Nat.lt_two_pow_self (n := s.length)
  rw [bval_powTwoWord]
  simp only [size_tally, powTwoWord, List.length_append,
    List.length_map, List.length_singleton]
  omega

/-- A bounded Cartesian product is polynomial in the explicit input lists. -/
theorem boundedAssignments_poly {A : Type} [Codec A] (a : A) (axes : ℕ) :
    Poly (fun xs : List (List A) => assignments (xs.take axes)) := by
  have step : Poly (fun q : List A × List (List A) =>
      q.1.flatMap fun v => q.2.map (v :: ·)) := by
    have row : Poly (fun p : List (List A) × A => p.1.map (p.2 :: ·)) :=
      Easy.exchange.poly.compose (Poly.push a ([] : List A) Poly.cons)
    exact (Easy.exchange.poly.compose (Poly.push ([] : List (List A)) a row)).compose Easy.flatten.poly
  have head : Poly (fun xs : List (List A) => readAt [] xs 0) :=
    poly_readAt [] Poly.identity (Code.Poly.const 0)
  have tail : Poly (fun xs : List (List A) => xs.drop 1) :=
    poly_drop (Code.Poly.const 1) Poly.identity
  have empty : Poly (fun xs : List (List A) => xs.isEmpty) := P1ChkDir.NP.poly_isEmpty
  induction axes with
  | zero => exact Code.Poly.const [[]]
  | succ n ih =>
    have h := Poly.choose empty (Code.Poly.const ([[]] : List (List A)))
      ((head.pair (tail.compose ih)).compose step)
    convert h using 1
    funext xs
    cases xs <;> rfl

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.boundedWords_poly
#print axioms P1SolCone.SolCone.boundedWords_eq

#print axioms P1SolCone.SolCone.powTwoTally_computes

#print axioms P1SolCone.SolCone.boundedAssignments_poly
