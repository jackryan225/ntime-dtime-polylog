import P1SolFactor.PolyLabels

namespace P1SolFactor.SolMachine

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1SolFactor.SolPolyWords
open scoped Classical

noncomputable section

abbrev Tape (V : FiniteMultiTapeMachine) := Tally × List (Label V.Γ)
abbrev Config (V : FiniteMultiTapeMachine) := Label V.Q × List (Tape V)
abbrev Reply (V : FiniteMultiTapeMachine) := Option (V.Q × (V.K → V.Γ × Fin 3))

def moveCode : HeadMove → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

def headMove (d : Fin 3) (x : Tally) : Tally :=
  if d = 0 then decT x else if d = 1 then x else () :: x

@[fun_prop] theorem headMove_poly (d : Fin 3) : Poly (headMove d) := by
  unfold headMove
  split
  · exact decT_poly
  · split
    · exact Code.Poly.identity
    · fun_prop

def tapeAt (V : FiniteMultiTapeMachine) (k : V.K) (c : Config V) : Tape V :=
  Iter.pick ([], []) (c.2, tally (kIdx V.K k).val)

def readHead (V : FiniteMultiTapeMachine) (t : Tape V) : Label V.Γ :=
  Iter.pick ⟨default⟩ (t.2, t.1)

@[fun_prop] theorem tapeAt_poly (V : FiniteMultiTapeMachine) (k : V.K) : Poly (tapeAt V k) := by
  unfold tapeAt
  fun_prop

@[fun_prop] theorem readHead_poly (V : FiniteMultiTapeMachine) : Poly (readHead V) := by
  unfold readHead
  fun_prop

def reads (V : FiniteMultiTapeMachine) (c : Config V) : Label (V.K → V.Γ) :=
  ⟨fun k => (readHead V (tapeAt V k c)).val⟩

@[fun_prop] theorem reads_poly (V : FiniteMultiTapeMachine) : Poly (reads V) := by
  let f (i : Fin (Fintype.card V.K)) (c : Config V) :=
    readHead V (tapeAt V ((kIdx V.K).symm i) c)
  let reindex (v : Label (Fin (Fintype.card V.K) → V.Γ)) : Label (V.K → V.Γ) :=
    ⟨v.val ∘ kIdx V.K⟩
  have h := (labelPi_poly _ f (by intro i; unfold f; fun_prop)).compose (Easy.finite reindex).poly
  convert h using 1
  funext c
  apply Label.ext
  funext k
  simp only [reads, reindex, Function.comp_apply, f, Equiv.symm_apply_apply]

def instruction (V : FiniteMultiTapeMachine)
    (x : Label V.Q × Label (V.K → V.Γ)) : Label (Reply V) :=
  ⟨(V.code x.1.val x.2.val).map (fun out => (out.1, fun k => (out.2.1 k, moveCode (out.2.2 k))))⟩

def command (V : FiniteMultiTapeMachine) (c : Config V) : Label (Reply V) :=
  instruction V (c.1, reads V c)

@[fun_prop] theorem command_poly (V : FiniteMultiTapeMachine) : Poly (command V) :=
  (Easy.fst.poly.pair (reads_poly V)).compose (Easy.finite (instruction V)).poly

def patch (V : FiniteMultiTapeMachine) (symbol : V.Γ) (p : Tape V × Tally) : Label V.Γ :=
  bif eqT (p.2, p.1.1) then ⟨symbol⟩ else Iter.pick ⟨default⟩ (p.1.2, p.2)

@[fun_prop] theorem patch_poly (V : FiniteMultiTapeMachine) (symbol : V.Γ) : Poly (patch V symbol) := by
  unfold patch
  fun_prop

def updateTape (V : FiniteMultiTapeMachine) (w : V.Γ × Fin 3) (t : Tape V) : Tape V :=
  (headMove w.2 t.1, polyPush (patch V w.1) (t, Iter.lineup (ruler t.2)))

@[fun_prop] theorem updateTape_poly (V : FiniteMultiTapeMachine) (w : V.Γ × Fin 3) :
    Poly (updateTape V w) := by
  unfold updateTape
  have hp : Poly (fun t : Tape V => (t, Iter.lineup (ruler t.2))) := by fun_prop
  exact (Easy.fst.poly.compose (headMove_poly w.2)).pair
    (hp.compose (Code.Poly.push ([], []) [] (patch_poly V w.1)))

def applyCommand (V : FiniteMultiTapeMachine) (r : Reply V) (c : Config V) : Config V :=
  match r with
  | none => c
  | some (q, w) =>
    (⟨q⟩, List.ofFn fun i =>
      let k := (kIdx V.K).symm i
      updateTape V (w k) (tapeAt V k c))

private theorem applyCommand_poly (V : FiniteMultiTapeMachine) (r : Reply V) :
    Poly (applyCommand V r) := by
  cases r with
  | none => exact Code.Poly.identity
  | some r =>
    rcases r with ⟨q, w⟩
    apply (Code.Poly.const (⟨q⟩ : Label V.Q)).pair
    apply ofFn_poly
    intro i
    exact (tapeAt_poly V _).compose (updateTape_poly V _)

def step (V : FiniteMultiTapeMachine) (c : Config V) : Config V :=
  applyCommand V (command V c).val c

@[fun_prop] theorem step_poly (V : FiniteMultiTapeMachine) : Poly (step V) :=
  select_poly (command V) (command_poly V) (applyCommand V) (applyCommand_poly V) id Code.Poly.identity

def encode (V : FiniteMultiTapeMachine) (width : ℕ) (c : AbsCfg V) : Config V :=
  (⟨c.q⟩, List.ofFn fun i =>
    let k := (kIdx V.K).symm i
    (tally (c.pos k).toNat, List.ofFn fun j : Fin width => ⟨c.cells k j.val⟩))

@[simp] theorem tapeAt_encode (V : FiniteMultiTapeMachine) (width : ℕ) (c : AbsCfg V) (k : V.K) :
    tapeAt V k (encode V width c) =
      (tally (c.pos k).toNat, List.ofFn fun j : Fin width => ⟨c.cells k j.val⟩) := by
  simp only [tapeAt, encode, Iter.entry, Equiv.symm_apply_apply]

theorem reads_encode (V : FiniteMultiTapeMachine) (width : ℕ) (c : AbsCfg V)
    (hpos : ∀ k, 0 ≤ c.pos k ∧ c.pos k < width) :
    reads V (encode V width c) = ⟨c.heads⟩ := by
  apply Label.ext
  funext k
  unfold reads
  simp only [tapeAt_encode, readHead]
  obtain ⟨h0, h1⟩ := hpos k
  have h : (c.pos k).toNat < width := by omega
  rw [show (c.pos k).toNat = (⟨(c.pos k).toNat, h⟩ : Fin width).val from rfl, Iter.entry]
  simp only [AbsCfg.heads, Int.toNat_of_nonneg h0]

private theorem headMove_encode (m : HeadMove) (x : ℤ) (hx : 0 ≤ x) :
    headMove (moveCode m) (tally x.toNat) = tally (x + moveDelta m).toNat := by
  cases m
  · change decT (tally x.toNat) = tally (x + -1).toNat
    rw [decT_tally]
    congr 1
    omega
  · change tally x.toNat = tally (x + 0).toNat
    rw [Int.add_zero]
  · change () :: tally x.toNat = tally (x + 1).toNat
    rw [← tally_succ]
    congr 1
    omega

theorem step_encode (V : FiniteMultiTapeMachine) (width : ℕ) (c : AbsCfg V)
    (hpos : ∀ k, 0 ≤ c.pos k ∧ c.pos k < width) :
    step V (encode V width c) = encode V width (absStep V c) := by
  unfold step command
  rw [reads_encode V width c hpos]
  change applyCommand V ((V.code c.q c.heads).map
    (fun out => (out.1, fun k => (out.2.1 k, moveCode (out.2.2 k))))) _ = _
  cases he : V.code c.q c.heads with
  | none =>
    rw [absStep_of_none he]
    rfl
  | some out =>
    rw [absStep_of_some he]
    simp only [Option.map_some, applyCommand, encode, AbsCfg.update]
    congr 1
    apply congrArg List.ofFn
    funext i
    let k := (kIdx V.K).symm i
    change updateTape V (out.2.1 k, moveCode (out.2.2 k)) (tapeAt V k (encode V width c)) = _
    have hR : ruler (List.ofFn (fun j : Fin width => (⟨c.cells k j.val⟩ : Label V.Γ))) =
        tally width := by
      rw [← recover_tally (ruler _), ruler_length, List.length_ofFn]
    rw [tapeAt_encode]
    simp only [updateTape, headMove_encode _ _ (hpos k).1, polyPush, hR, Iter.lined,
      List.map_ofFn, Function.comp_def, patch, Iter.entry, eqT_tally]
    congr 1
    apply congrArg List.ofFn
    funext j
    have hn := (hpos k).1
    have h : j.val = (c.pos k).toNat ↔ (j.val : ℤ) = c.pos k := by omega
    rw [Bool.cond_decide]
    apply Label.ext
    change (if j.val = (c.pos k).toNat then (⟨out.2.1 k⟩ : Label V.Γ)
      else ⟨c.cells k j.val⟩).val = (if (j.val : ℤ) = c.pos k then out.2.1 k else c.cells k j.val)
    by_cases he : j.val = (c.pos k).toNat
    · simp only [ite_eq_left he, ite_eq_left (h.mp he)]
    · simp only [ite_eq_right he, ite_eq_right (fun he' => he (h.mpr he'))]

def run (V : FiniteMultiTapeMachine) := ride (step V)

theorem run_encode (V : FiniteMultiTapeMachine) (width fuel : ℕ) (c : AbsCfg V)
    (h : ∀ t < fuel, ∀ k, 0 ≤ ((absStep V)^[t] c).pos k ∧ ((absStep V)^[t] c).pos k < width) :
    run V (tally fuel, encode V width c) = encode V width ((absStep V)^[fuel] c) := by
  rw [run, ride_t, tally_length]
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      step_encode V width c (h 0 (Nat.zero_lt_succ _))]
    apply ih
    intro t ht k
    rw [← Function.iterate_succ_apply]
    exact h (t + 1) (Nat.succ_lt_succ ht) k

private theorem size_list_le {A : Type} [Codec A] (xs : List A) (M : ℕ)
    (h : ∀ x ∈ xs, size x ≤ M) :
    size xs ≤ 1 + xs.length * (M + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hu := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private def tapeWithin {V : FiniteMultiTapeMachine} (M : ℕ) (p : Tape V) : Prop :=
  p.1.length ≤ M ∧ p.2.length ≤ M

private def cfgWithin {V : FiniteMultiTapeMachine} (M : ℕ) (p : Config V) : Prop :=
  p.2.length ≤ M ∧ ∀ t ∈ p.2, tapeWithin M t

private theorem cfgWithin_mono {V : FiniteMultiTapeMachine} {M N : ℕ} {p : Config V}
    (h : cfgWithin M p) (hMN : M ≤ N) : cfgWithin N p :=
  ⟨h.1.trans hMN, fun t ht => ⟨(h.2 t ht).1.trans hMN, (h.2 t ht).2.trans hMN⟩⟩

private theorem tapeAt_within (V : FiniteMultiTapeMachine) (M : ℕ) (p : Config V)
    (h : cfgWithin M p) (k : V.K) : tapeWithin M (tapeAt V k p) := by
  unfold tapeAt
  rw [pick_getD, List.getD_eq_getElem?_getD]
  cases he : p.2[(kIdx V.K k).val]? with
  | none => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | some t => exact h.2 t (List.mem_of_getElem? he)

private theorem headMove_length (d : Fin 3) (x : Tally) :
    (headMove d x).length ≤ x.length + 1 := by
  unfold headMove
  split
  · simp [decT, cutLists]
    omega
  · split <;> simp

private theorem updateTape_within (V : FiniteMultiTapeMachine) (M : ℕ) (t : Tape V)
    (h : tapeWithin M t) (w : V.Γ × Fin 3) : tapeWithin (M + 1) (updateTape V w t) := by
  constructor
  · exact (headMove_length _ _).trans (Nat.add_le_add_right h.1 _)
  · simpa only [updateTape, polyPush, List.length_map, Iter.sizeup, ruler_length] using
      h.2.trans (Nat.le_succ M)

private theorem step_within (V : FiniteMultiTapeMachine) (M : ℕ) (p : Config V)
    (h : cfgWithin M p) (hK : Fintype.card V.K ≤ M) : cfgWithin (M + 1) (step V p) := by
  unfold step
  cases (command V p).val with
  | none => exact cfgWithin_mono h (Nat.le_succ M)
  | some r =>
    rcases r with ⟨q, w⟩
    refine ⟨by simpa only [applyCommand, List.length_ofFn] using hK.trans (Nat.le_succ M), ?_⟩
    intro t ht
    simp only [applyCommand, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    exact updateTape_within V M _ (tapeAt_within V M p h _) _

private theorem cfgWithin_start (V : FiniteMultiTapeMachine) (p : Config V) :
    cfgWithin (size p + Fintype.card V.K) p := by
  have hs : size p.2 ≤ size p := by
    change size p.2 ≤ size p.1 + size p.2 + 1
    omega
  refine ⟨(duration p.2).le.trans (hs.trans (Nat.le_add_right _ _)), ?_⟩
  intro t ht
  have ht' := (size_bel ht).le.trans hs
  have hp := duration t.1
  have hc := duration t.2
  rw [size_prod] at ht'
  exact ⟨by omega, by omega⟩

private theorem run_within (V : FiniteMultiTapeMachine) (p : Config V) (l : Tally)
    (M : ℕ) (h : cfgWithin M p) (hK : Fintype.card V.K ≤ M) :
    cfgWithin (M + l.length) (run V (l, p)) := by
  induction l generalizing p M with
  | nil => simpa only [run, ride, List.foldl_nil, List.length_nil, Nat.add_zero] using h
  | cons _ l ih =>
    change cfgWithin (M + (l.length + 1)) (run V (l, step V p))
    rw [show M + (l.length + 1) = M + 1 + l.length by omega]
    exact ih (step V p) (M + 1) (step_within V M p h hK) (hK.trans (Nat.le_succ M))

private def boundCoeff (V : FiniteMultiTapeMachine) : ℕ :=
  2 * Fintype.card V.Q + 2 * Fintype.card V.Γ + 11

private theorem cfgWithin_size (V : FiniteMultiTapeMachine) (p : Config V) (M : ℕ)
    (h : cfgWithin M p) : size p ≤ boundCoeff V * (M + 1)^2 := by
  let A := 2 * Fintype.card V.Γ + 2
  let Q := 2 * Fintype.card V.Q + 1
  let w := (M + 1)^2
  have hs (t : Tape V) (ht : tapeWithin M t) : size t ≤ (A + 2) * M + 3 := by
    obtain ⟨hp, hl⟩ := ht
    have hm := size_list_le t.2 (A - 1)
      (fun c hc => (label_size c.val).trans (by unfold A; omega))
    have hu : size t.2 ≤ 1 + M * A := by
      have he : A - 1 + 1 = A := by unfold A; omega
      rw [he] at hm
      exact hm.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _)
    rw [size_prod, size_tally, Nat.add_mul]
    nlinarith
  have hb := size_list_le p.2 ((A + 2) * M + 3) (fun t ht => hs t (h.2 t ht))
  have hbig : p.2.length * ((A + 2) * M + 3 + 1) ≤ (A + 6) * w := by
    have hM : p.2.length ≤ M + 1 := h.1.trans (Nat.le_succ M)
    have hA : (A + 2) * M + 3 + 1 ≤ (A + 6) * (M + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      nlinarith
    unfold w
    rw [pow_two, ← Nat.mul_assoc, Nat.mul_comm (A + 6) (M + 1), Nat.mul_assoc]
    exact Nat.mul_le_mul hM hA
  have hq : size p.1 ≤ Q := label_size p.1.val
  have hw : 0 < w := by unfold w; positivity
  have hqw := Nat.le_mul_of_pos_right (Q + 2) hw
  have he : boundCoeff V = Q + 2 + (A + 6) := by unfold boundCoeff Q A; omega
  rw [he]
  change size p ≤ (Q + 2 + (A + 6)) * w
  rw [size_prod, Nat.add_mul]
  omega

theorem run_poly (V : FiniteMultiTapeMachine) : Poly (run V) := by
  let K := Fintype.card V.K
  apply Code.Poly.fold_left (f := fun p : Config V × Unit => step V p.1)
    (Easy.fst.poly.compose (step_poly V)) (boundCoeff V * (K + 1)^2) 2
  rintro ⟨fuel, p⟩ l hl
  have hK : K ≤ size p + K := Nat.le_add_left _ _
  have h := run_within V p l (size p + K) (cfgWithin_start V p) hK
  change size (run V (l, p)) ≤ _
  apply (cfgWithin_size V _ _ h).trans
  have hn : l.length ≤ fuel.length := hl.length_le
  have hd := duration fuel
  let S := size (fuel, p) + 1
  have hS : S = size fuel + size p + 2 := by dsimp only [S, size_prod]
  have hs : 0 < S := Nat.zero_lt_succ _
  have hb : size p + K + l.length + 1 ≤ (K + 1) * S := by
    rw [Nat.add_mul, Nat.one_mul]
    have hk := Nat.le_mul_of_pos_right K hs
    omega
  change boundCoeff V * (size p + K + l.length + 1)^2 ≤ (boundCoeff V * (K + 1)^2) * S^2
  rw [Nat.mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)

end

end P1SolFactor.SolMachine
