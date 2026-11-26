import P1SolFactor.FactorTableData

namespace P1SolFactor.SolFactor

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Net P1SolFactor.SolHalf P1SolFactor.SolPolyWords P1SolFactor.SolMachine
open scoped Classical

noncomputable section

def subTally (p : Tally × Tally) : Tally := dropT (p.2, p.1)

@[fun_prop] theorem subTally_poly : Poly subTally := by unfold subTally; fun_prop

@[simp] theorem subTally_tally (m n : ℕ) : subTally (tally m, tally n) = tally (m - n) := by
  unfold subTally
  rw [dropT_tally, ← recover_tally ((tally m).drop n)]
  simp only [List.length_drop, tally_length]

def splitPos (p : Tally × Tally) : Tally × Tally :=
  let twice := doubleT p.1
  bif lessT (p.2, p.1) then (tally 0, p.2)
  else bif lessT (p.2, twice) then (tally 1, subTally (p.2, p.1))
  else (tally 2, subTally (p.2, twice))

@[fun_prop] theorem splitPos_poly : Poly splitPos := by unfold splitPos; fun_prop

theorem splitPos_encode (B : ℕ) [NeZero B] (pos : ℤ) (h0 : 0 ≤ pos) (h1 : pos < 3 * (B : ℤ)) :
    splitPos (tally B, tally pos.toNat) =
      (tally (finOfInt 3 (pos / B)).val, tally (finOfInt B (pos % B)).val) := by
  let n := pos.toNat
  let m : Fin 3 := if n < B then 0 else if n < 2 * B then 1 else 2
  have hn : (n : ℤ) = pos := Int.toNat_of_nonneg h0
  have hb : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hm : m.val * B ≤ n ∧ n < m.val * B + B := by
    by_cases lh : n < B
    · simp [m, lh]
    by_cases hh : n < 2 * B
    · simp [m, lh, hh, Nat.le_of_not_gt lh]
      omega
    · simp [m, lh, hh]
      omega
  have hl : (m.val : ℤ) * B ≤ pos := by
    rw [← hn]
    exact_mod_cast hm.1
  have hu : pos < (m.val : ℤ) * B + B := by
    rw [← hn]
    exact_mod_cast hm.2
  have hq : pos / B = (m.val : ℤ) := ediv_eq_of_bounds hb hl hu
  have hr : pos % B = ((n - m.val * B : ℕ) : ℤ) := by
    have he := Int.emod_add_ediv_mul pos B
    rw [hq] at he
    rw [Nat.cast_sub hm.1, Nat.cast_mul, hn]
    linarith only [he]
  have hnat : n - m.val * B < B := by omega
  rw [hq, hr, finOfInt_coe 3 m]
  have hv : (finOfInt B ((n - m.val * B : ℕ) : ℤ)).val = n - m.val * B := by
    have e := finOfInt_coe B (⟨n - m.val * B, hnat⟩ : Fin B)
    exact congrArg Fin.val e
  rw [hv]
  change splitPos (tally B, tally n) = (tally m.val, tally (n - m.val * B))
  by_cases lh : n < B
  · simp [splitPos, m, lh, -tally_succ]
  by_cases hh : n < 2 * B
  · simp [splitPos, m, lh, hh, -tally_succ]
  · simp [splitPos, m, lh, hh, -tally_succ]

def tapeBlock (V : FiniteMultiTapeMachine) (d : Fin 3) (p : Tally × Tape V) : List (Label V.Γ) :=
  takeT (p.1, dropT (mulT (tally d.val, p.1), p.2.2))

@[fun_prop] theorem tapeBlock_poly (V : FiniteMultiTapeMachine) (d : Fin 3) :
    Poly (tapeBlock V d) := by unfold tapeBlock; fun_prop

theorem tapeBlock_encode (V : FiniteMultiTapeMachine) (B : ℕ) (c : AbsCfg V) (k : V.K) (d : Fin 3) :
    tapeBlock V d (tally B, tapeAt V k (SolMachine.encode V (3 * B) c)) =
      List.ofFn (fun j : Fin B => (⟨c.cells k ((d.val : ℤ) * B + j.val)⟩ : Label V.Γ)) := by
  simp only [tapeBlock, tapeAt_encode, mulT_tally, dropT_tally, takeT_tally]
  rw [ofFn_slice_row _ d]
  apply congrArg List.ofFn
  funext j
  apply Label.ext
  congr 1
  simp only [finProdFinEquiv_apply_val, Nat.cast_add, Nat.cast_mul]
  ring

def tapePosition (V : FiniteMultiTapeMachine) (k : V.K) (p : Tally × Config V) : Tally × Tally :=
  splitPos (p.1, (tapeAt V k p.2).1)

@[fun_prop] theorem tapePosition_poly (V : FiniteMultiTapeMachine) (k : V.K) :
    Poly (tapePosition V k) := by unfold tapePosition; fun_prop

theorem tapePosition_encode (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (c : AbsCfg V)
    (k : V.K) (h : 0 ≤ c.pos k ∧ c.pos k < 3 * (B : ℤ)) :
    tapePosition V k (tally B, SolMachine.encode V (3 * B) c) =
      (tally (finOfInt 3 (c.pos k / B)).val, tally (finOfInt B (c.pos k % B)).val) := by
  simp only [tapePosition, tapeAt_encode, splitPos_encode B _ h.1 h.2]

def configStateWord (V : FiniteMultiTapeMachine) (p : Tally × Config V) : List Bool :=
  stateWord V (p.1, (p.2.1, List.ofFn (fun i => (tapePosition V ((kIdx V.K).symm i) p).2)))

@[fun_prop] theorem configStateWord_poly (V : FiniteMultiTapeMachine) : Poly (configStateWord V) := by
  unfold configStateWord
  have hoff : Poly (fun p : Tally × Config V =>
      List.ofFn (fun i => (tapePosition V ((kIdx V.K).symm i) p).2)) :=
    ofFn_poly _ _ (fun _ => (tapePosition_poly V _).sndCompose)
  have hq : Poly (fun p : Tally × Config V => p.2.1) := by fun_prop
  exact (Easy.fst.poly.pair (hq.pair hoff)).compose (stateWord_poly V)

@[simp] theorem configStateWord_encode (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]
    (c : AbsCfg V) (h : ∀ k, 0 ≤ c.pos k ∧ c.pos k < 3 * (B : ℤ)) :
    configStateWord V (tally B, SolMachine.encode V (3 * B) c) =
      List.ofFn (encS V B c.q (fun k => finOfInt B (c.pos k % B))) := by
  have hoff (k : V.K) :
      (tapePosition V k (tally B, SolMachine.encode V (3 * B) c)).2 =
        tally (finOfInt B (c.pos k % B)).val :=
    congrArg Prod.snd (tapePosition_encode V B c k (h k))
  simp only [configStateWord, hoff]
  exact stateWord_encS V B c.q (fun k => finOfInt B (c.pos k % B))

def configBlockWord (V : FiniteMultiTapeMachine) (k : V.K) (d : Fin 3)
    (p : Tally × Config V) : List Bool :=
  blockWord V (strT V p.1, tapeBlock V d (p.1, tapeAt V k p.2))

@[fun_prop] theorem configBlockWord_poly (V : FiniteMultiTapeMachine) (k : V.K) (d : Fin 3) :
    Poly (configBlockWord V k d) := by unfold configBlockWord; fun_prop

@[simp] theorem configBlockWord_encode (V : FiniteMultiTapeMachine) (B : ℕ) (c : AbsCfg V)
    (k : V.K) (d : Fin 3) :
    configBlockWord V k d (tally B, SolMachine.encode V (3 * B) c) =
      List.ofFn (encC V B (fun j => c.cells k ((d.val : ℤ) * B + j.val))) := by
  simp only [configBlockWord, strT_tally, tapeBlock_encode, blockWord_encC]

abbrev ConfigPair (V : FiniteMultiTapeMachine) := Tally × (Config V × Config V)

def configPart (V : FiniteMultiTapeMachine) : Ext V.K → ConfigPair V → List Bool
  | .stIn => fun p => configStateWord V (p.1, p.2.1)
  | .stOut => fun p => configStateWord V (p.1, p.2.2)
  | .cIn k d => fun p => configBlockWord V k d (p.1, p.2.1)
  | .cOut k d => fun p => configBlockWord V k d (p.1, p.2.2)

theorem configPart_poly (V : FiniteMultiTapeMachine) (c : Ext V.K) : Poly (configPart V c) := by
  cases c <;> (unfold configPart; fun_prop)

def configTuple (V : FiniteMultiTapeMachine) (p : ConfigPair V) : List Bool :=
  (List.ofFn fun i => configPart V ((extIdx V.K).symm i) p).flatten

@[fun_prop] theorem configTuple_poly (V : FiniteMultiTapeMachine) : Poly (configTuple V) :=
  (ofFn_poly _ _ (fun _ => configPart_poly V _)).compose flatten_poly

private theorem configTuple_ofFn (V : FiniteMultiTapeMachine) (B : ℕ)
    (p : ConfigPair V) (f : Ext V.K → Fin (strWidth V B) → Bool)
    (h : ∀ c, configPart V c p = List.ofFn (f c)) :
    configTuple V p = List.ofFn (tupleWord V B f) := by
  unfold configTuple tupleWord tupWidth
  rw [ofFn_prod]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [h]
  apply congrArg List.ofFn
  funext j
  simp only [Equiv.symm_apply_apply]

section LocalRun

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B]

theorem run_window (d : LocalIn V B) {t : ℕ} (ht : t ≤ B) (k : V.K) :
    0 ≤ ((absStep V)^[t] d.toAbs).pos k ∧ ((absStep V)^[t] d.toAbs).pos k < 3 * (B : ℤ) := by
  have h := iterate_pos_bound t d.toAbs k
  have hp : d.toAbs.pos k = B + (d.off k).val := rfl
  have hlt := (d.off k).isLt
  rw [hp] at h
  omega

theorem input_pos_off (d : LocalIn V B) (k : V.K) :
    finOfInt B (d.toAbs.pos k % B) = d.off k := by
  have hb : (0 : ℤ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hp : d.toAbs.pos k = B + (d.off k).val := rfl
  have hlt : ((d.off k).val : ℤ) < B := by exact_mod_cast (d.off k).isLt
  have hq : d.toAbs.pos k / B = 1 := ediv_eq_of_bounds hb (by rw [hp]; omega)
    (by rw [hp]; omega)
  have hr : d.toAbs.pos k % B = (d.off k).val := by
    have he := Int.emod_add_ediv_mul (d.toAbs.pos k) B
    rw [hq] at he
    rw [hp] at he ⊢
    omega
  rw [hr, finOfInt_coe]

theorem configTuple_run (d : LocalIn V B) :
    configTuple V (tally B, (SolMachine.encode V (3 * B) d.toAbs,
      SolMachine.encode V (3 * B) ((absStep V)^[B] d.toAbs))) =
      List.ofFn (tupleWord V B (extData V B d (evolve d))) := by
  apply configTuple_ofFn
  intro c
  cases c with
  | stIn =>
    have h (k : V.K) : 0 ≤ d.toAbs.pos k ∧ d.toAbs.pos k < 3 * (B : ℤ) :=
      run_window V B d (Nat.zero_le B) k
    simp only [configPart, extData, configStateWord_encode V B d.toAbs h, input_pos_off]
    rfl
  | stOut =>
    simp only [configPart, configStateWord_encode V B _ (run_window V B d le_rfl), extData, evolve]
  | cIn k δ =>
    simp only [configPart, configBlockWord_encode, extData, abs_cell V B d]
  | cOut k δ =>
    simp only [configPart, configBlockWord_encode, extData, evolve]

end LocalRun

end

end P1SolFactor.SolFactor
