import P1ChkDir.Basic
import P1Wit.Layout

/-!
# P1ChkDir.P6: the checks C1-C3 on the witness format of lane P6 (`P1Wit.Layout`)

Lane P1-lean-W2-chkdir. `P1Wit.Layout` (job wit-3, 10:49Z) stores every field as a natural number, LEAST significant
bit first (`P1Wit.readNat`): trits as `0, 1, 2` (`3` invalid), start blocks as `zigzag β`, owners as
`optCode` (`0` = none, `ι + 1` = `ι`). This file
* proves that the bits `field u o w` of `P1ChkDir.Basic` spell the number `P1Wit.readNat u o w` (`bitsVal_field`);
* builds the three codes of P6 as `P1ChkDir.Code`s (`numCode`: a number of `w` bits read through a partial inverse):
  `tritNum`, `zigCode`, `ownCode`;
* builds the directory layout `dirP6 D ρ` of a `P1Wit.Dims` (tape numbering `ρ : K ≃ Fin D.r`), with offsets
  `D.off s + index * D.width s` exactly as `P1Wit.readField`;
* reads it back through P6's readers: `dirP6_sigmaS`, `dirP6_C1_iff`, `dirP6_betaS`, `dirP6_prevS`, `dirP6_nextS`;
* states the check families in the indexed form of decision D5 (board 1548 and its amendment 1556): `C1F`, `C2F`,
  `C3F` with `Ck_out` (an index beyond the count passes) and `dirF_iff` (all indices pass iff the directory is true).
-/

namespace P1ChkDir

open P1Wit

/-! ## The bits of a field spell P6's number -/

theorem field_succ (u : List Bool) (o w : ℕ) : field u o (w + 1) = bit u o :: field u (o + 1) w := by
  unfold field
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ List.cons (by simp) ?_
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  congr 1
  omega

theorem field_cons (a : Bool) (u : List Bool) (o w : ℕ) : field (a :: u) (o + 1) w = field u o w := by
  unfold field
  apply List.map_congr_left
  intro j _
  simp [bit, show o + 1 + j = (o + j) + 1 by omega]

theorem field_zero_cons (a : Bool) (u : List Bool) (w : ℕ) : field (a :: u) 0 (w + 1) = a :: field u 0 w := by
  rw [field_succ, field_cons]
  rfl

theorem bitsVal_field_nil (o w : ℕ) : bitsVal (field [] o w) = 0 := by
  induction w generalizing o with
  | zero => simp [field, bitsVal]
  | succ w ih =>
    simp [field_succ, bitsVal, ih, bit]

/-- The bits `field u o w` spell the number that P6 reads at offset `o`, width `w`. -/
theorem bitsVal_field (u : List Bool) (o w : ℕ) : bitsVal (field u o w) = readNat u o w := by
  induction u generalizing o w with
  | nil => simp [bitsVal_field_nil, readNat, bitsVal]
  | cons a u ih =>
    cases o with
    | succ o =>
      rw [field_cons, ih]
      simp [readNat]
    | zero =>
      cases w with
      | zero => simp [field, readNat, bitsVal]
      | succ w =>
        rw [field_zero_cons]
        have h := ih 0 w
        simp only [readNat, List.drop_zero] at h ⊢
        simp only [List.take_succ_cons, bitsVal, h]

theorem field_eq_natBits (u : List Bool) (o w : ℕ) : field u o w = natBits w (readNat u o w) := by
  have h := natBits_bitsVal (field u o w)
  rw [field_length, bitsVal_field] at h
  exact h.symm

/-! ## Codes of numbers -/

/-- A value stored as a number of `w` bits (LSB first), decoded by a partial inverse `ofN` of `toN`. A word is
invalid if its length is not `w` or `ofN` rejects its number; the range is `toN a < 2 ^ w`. -/
def numCode {α : Type} (w : ℕ) (toN : α → ℕ) (ofN : ℕ → Option α) (h1 : ∀ a, ofN (toN a) = some a)
    (h2 : ∀ n a, ofN n = some a → toN a = n) : Code α where
  w := w
  enc a := natBits w (toN a)
  dec l := if l.length = w then ofN (bitsVal l) else none
  ok a := toN a < 2 ^ w
  enc_length _ := natBits_length _ _
  dec_enc a ha := by
    change (if (natBits w (toN a)).length = w then ofN (bitsVal (natBits w (toN a))) else none) = some a
    change toN a < 2 ^ w at ha
    simp [bitsVal_natBits, Nat.mod_eq_of_lt ha, h1]
  dec_ok l a h := by
    change (if l.length = w then ofN (bitsVal l) else none) = some a at h
    change toN a < 2 ^ w
    split_ifs at h with hl
    · rw [h2 _ _ h, ← hl]
      exact bitsVal_lt l
  enc_dec l a hl h := by
    change (if l.length = w then ofN (bitsVal l) else none) = some a at h
    change natBits w (toN a) = l
    rw [if_pos hl] at h
    rw [h2 _ _ h, ← hl, natBits_bitsVal]

theorem numCode_read {α : Type} (w : ℕ) (toN : α → ℕ) (ofN : ℕ → Option α) (h1 : ∀ a, ofN (toN a) = some a)
    (h2 : ∀ n a, ofN n = some a → toN a = n) (u : List Bool) (o : ℕ) :
    (numCode w toN ofN h1 h2).read u o = ofN (readNat u o w) := by
  simp [Code.read, numCode, bitsVal_field]

/-- Trits of P6: the `Fin 3` value as a number (`3` invalid), 2 bits. -/
def tritOfN (n : ℕ) : Option (Fin 3) := if h : n < 3 then some ⟨n, h⟩ else none

theorem tritOfN_val (a : Fin 3) : tritOfN (a : ℕ) = some a := by
  simp [tritOfN, a.isLt]

theorem tritOfN_eq {n : ℕ} {a : Fin 3} (h : tritOfN n = some a) : (a : ℕ) = n := by
  unfold tritOfN at h
  split_ifs at h with hn
  · simp only [Option.some.injEq] at h
    rw [← h]

def tritNum : Code (Fin 3) := numCode 2 (fun a => (a : ℕ)) tritOfN tritOfN_val (fun _ _ h => tritOfN_eq h)

theorem tritNum_ok (a : Fin 3) : tritNum.ok a := by
  show (a : ℕ) < 2 ^ 2
  have := a.isLt
  omega

theorem zigzag_unzigzag (n : ℕ) : zigzag (unzigzag n) = n := by
  unfold unzigzag
  split_ifs with h
  · show 2 * (n / 2) = n
    omega
  · show 2 * (n / 2) + 1 = n
    omega

/-- Start blocks of P6: `zigzag β` in `w` bits. -/
def zigCode (w : ℕ) : Code ℤ :=
  numCode w zigzag (fun n => some (unzigzag n)) (fun a => by simp [unzigzag_zigzag])
    (fun n a h => by
      simp only [Option.some.injEq] at h
      rw [← h, zigzag_unzigzag])

/-- Owners of P6: `optCode` (`0` = none, `ι + 1` = `ι`), an owner must be `< I`. -/
def ownOfN (I n : ℕ) : Option (Option (Fin I)) :=
  if n = 0 then some none else if h : n - 1 < I then some (some ⟨n - 1, h⟩) else none

def ownToN {I : ℕ} (o : Option (Fin I)) : ℕ := optCode (o.map Fin.val)

theorem ownOfN_toN {I : ℕ} (o : Option (Fin I)) : ownOfN I (ownToN o) = some o := by
  cases o with
  | none => simp [ownOfN, ownToN, optCode]
  | some ι =>
    simp [ownOfN, ownToN, optCode, ι.isLt]

theorem ownOfN_eq {I n : ℕ} {o : Option (Fin I)} (h : ownOfN I n = some o) : ownToN o = n := by
  unfold ownOfN at h
  split_ifs at h with h0 h1
  · simp only [Option.some.injEq] at h
    rw [← h, h0]
    rfl
  · simp only [Option.some.injEq] at h
    rw [← h]
    show n - 1 + 1 = n
    omega

def ownCode (w I : ℕ) : Code (Option (Fin I)) :=
  numCode w ownToN (ownOfN I) ownOfN_toN (fun _ _ h => ownOfN_eq h)

/-! ## The directory layout of P6 -/

theorem width_trit (D : Dims) : D.width secTrit = 2 := by simp [Dims.width, Dims.kind, secTrit]
theorem width_start (D : Dims) : D.width secStart = D.bigW := by simp [Dims.width, Dims.kind, secStart]
theorem width_prev (D : Dims) : D.width secPrev = D.bigW := by simp [Dims.width, Dims.kind, secPrev]
theorem width_next (D : Dims) : D.width secNext = D.bigW := by simp [Dims.width, Dims.kind, secNext]

variable {K : Type}

/-- **The directory of P6** (sections 0-3 of `P1Wit.Layout`), tapes numbered by `ρ`. -/
def dirP6 (D : Dims) (ρ : K ≃ Fin D.r) : DirLayout K D.I D.N where
  cT := tritNum
  cT_ok := tritNum_ok
  tritOff i k := D.off secTrit + ((i : ℕ) * D.r + ρ k) * D.width secTrit
  betaOff ι k := D.off secStart + ((ι : ℕ) * D.r + ρ k) * D.width secStart
  nextOff ι k δ := D.off secNext + (((ι : ℕ) * D.r + ρ k) * 3 + δ) * D.width secNext
  prevOff ι k δ := D.off secPrev + (((ι : ℕ) * D.r + ρ k) * 3 + δ) * D.width secPrev
  cB := zigCode D.bigW
  cO := ownCode D.bigW D.I

variable (D : Dims) (ρ : K ≃ Fin D.r) (u : List Bool)

theorem dirP6_tritRead (i : Fin (D.I * D.N)) (k : K) :
    (dirP6 D ρ).cT.read u ((dirP6 D ρ).tritOff i k) = tritOfN (rdTrit D u i (ρ k)) := by
  show tritNum.read u _ = _
  rw [tritNum, numCode_read]
  simp only [rdTrit, readField, dirP6, width_trit]

/-- The stored skeleton is P6's trit section (an invalid code reads as `1`, the trit `0`). -/
theorem dirP6_sigmaS (i : Fin (D.I * D.N)) (k : K) :
    (dirP6 D ρ).sigmaS u i k = (tritOfN (rdTrit D u i (ρ k))).getD 1 := by
  simp only [DirLayout.sigmaS, dirP6_tritRead]

/-- **C1 on P6**: the stored trit is `< 3`. -/
theorem dirP6_C1_iff (i : Fin (D.I * D.N)) (k : K) :
    C1 (dirP6 D ρ) u i k ↔ rdTrit D u i (ρ k) < 3 := by
  unfold C1
  rw [dirP6_tritRead]
  unfold tritOfN
  split_ifs with h <;> simp [h]

theorem dirP6_betaS (ι : Fin D.I) (k : K) :
    (dirP6 D ρ).betaS u ι k = some (unzigzag (rdStart D u ι (ρ k))) := by
  simp only [DirLayout.betaS, dirP6, zigCode, numCode_read, rdStart, readField, width_start]

theorem dirP6_prevS (ι : Fin D.I) (k : K) (δ : Fin 3) :
    (dirP6 D ρ).prevS u ι k δ = ownOfN D.I (rdPrev D u ι (ρ k) δ) := by
  simp only [DirLayout.prevS, dirP6, ownCode, numCode_read, rdPrev, readField, width_prev]

theorem dirP6_nextS (ι : Fin D.I) (k : K) (δ : Fin 3) :
    (dirP6 D ρ).nextS u ι k δ = ownOfN D.I (rdNext D u ι (ρ k) δ) := by
  simp only [DirLayout.nextS, dirP6, ownCode, numCode_read, rdNext, readField, width_next]

/-! ## The directory is true -/

/-- The directory part of the witness is TRUE: valid trit codes, every start block the true `β` of the stored
skeleton, every owner field the true owner. -/
def DirTrue {I N : ℕ} (L : DirLayout K I N) (u : List Bool) : Prop :=
  (∀ i k, C1 L u i k) ∧ (∀ ι k, L.betaS u ι k = some (betaT N (L.sigmaS u) ι k)) ∧
    ∀ ι k δ, L.nextS u ι k δ = some (nextT N (L.sigmaS u) ι k δ) ∧
      L.prevS u ι k δ = some (prevT N (L.sigmaS u) ι k δ)

/-- **Stage 0 (C1-C3) of `P1Count.stages_iff`.** All instances of C1, C2 and C3 pass iff the directory is true. -/
theorem dir_iff {I N : ℕ} (L : DirLayout K I N) (u : List Bool) :
    ((∀ i k, C1 L u i k) ∧ (∀ ι k, C2 L u ι k) ∧ (∀ ι k δ nx, C3 L u ι k δ nx)) ↔ DirTrue L u := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨-, hβ, hown⟩ := dir_unique L u h1 h2 h3
    exact ⟨h1, hβ, hown⟩
  · rintro ⟨h1, hβ, hown⟩
    exact dir_true L u (L.sigmaS u) (C1_unique L u h1) hβ hown

/-! ## The families of decision D5 (index `i : ℕ`; an index beyond the count passes) -/

/-- Family 0, **C1**: index `i * r + ρ`, `i < I N`. -/
def C1F (i : ℕ) : Prop := ∀ h : i < D.I * D.N * D.r,
  C1 (dirP6 D ρ) u ⟨i / D.r, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩
    (ρ.symm ⟨i % D.r, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩)

/-- Family 1, **C2**: index `ι * r + ρ`, `ι < I`. -/
def C2F (i : ℕ) : Prop := ∀ h : i < D.I * D.r,
  C2 (dirP6 D ρ) u ⟨i / D.r, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩
    (ρ.symm ⟨i % D.r, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩)

/-- Family 2, **C3**: index `((ι * r + ρ) * 3 + δ) * 2 + nx` (`nx = 1`: next owner, `0`: previous owner). -/
def C3F (i : ℕ) : Prop := ∀ h : i < D.I * D.r * 3 * 2,
  C3 (dirP6 D ρ) u ⟨i / 2 / 3 / D.r, by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc i < D.I * D.r * 3 * 2 := h
        _ = 2 * (3 * (D.I * D.r)) := by ring⟩
    (ρ.symm ⟨i / 2 / 3 % D.r, Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at h)⟩)
    ⟨i / 2 % 3, Nat.mod_lt _ (by norm_num)⟩ (decide (i % 2 = 1))

theorem C1F_out {i : ℕ} (hi : D.I * D.N * D.r ≤ i) : C1F D ρ u i := fun h => absurd h (by omega)
theorem C2F_out {i : ℕ} (hi : D.I * D.r ≤ i) : C2F D ρ u i := fun h => absurd h (by omega)
theorem C3F_out {i : ℕ} (hi : D.I * D.r * 3 * 2 ≤ i) : C3F D ρ u i := fun h => absurd h (by omega)

theorem C1F_iff : (∀ i, C1F D ρ u i) ↔ ∀ i k, C1 (dirP6 D ρ) u i k := by
  constructor
  · intro hF i k
    have hr : (ρ k : ℕ) < D.r := (ρ k).isLt
    have hlt : (i : ℕ) * D.r + ρ k < D.I * D.N * D.r := by
      have := i.isLt
      calc (i : ℕ) * D.r + ρ k < (i + 1) * D.r := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ D.I * D.N * D.r := Nat.mul_le_mul_right _ this
    have h := hF _ hlt
    have e1 : ((i : ℕ) * D.r + ρ k) / D.r = i := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have e2 : ((i : ℕ) * D.r + ρ k) % D.r = ρ k := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hi : (⟨((i : ℕ) * D.r + ρ k) / D.r, by rw [e1]; exact i.isLt⟩ : Fin (D.I * D.N)) = i := Fin.ext e1
    have hk : ρ.symm ⟨((i : ℕ) * D.r + ρ k) % D.r, by rw [e2]; exact hr⟩ = k := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext e2
    have key : ∀ (i' : Fin (D.I * D.N)) (k' : K), i' = i → k' = k →
        C1 (dirP6 D ρ) u i' k' → C1 (dirP6 D ρ) u i k := by
      rintro _ _ rfl rfl h'
      exact h'
    exact key _ _ hi hk h
  · intro h i hi
    exact h _ _

theorem C2F_iff : (∀ i, C2F D ρ u i) ↔ ∀ ι k, C2 (dirP6 D ρ) u ι k := by
  constructor
  · intro hF ι k
    have hr : (ρ k : ℕ) < D.r := (ρ k).isLt
    have hlt : (ι : ℕ) * D.r + ρ k < D.I * D.r := by
      have := ι.isLt
      calc (ι : ℕ) * D.r + ρ k < (ι + 1) * D.r := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ D.I * D.r := Nat.mul_le_mul_right _ this
    have h := hF _ hlt
    have e1 : ((ι : ℕ) * D.r + ρ k) / D.r = ι := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have e2 : ((ι : ℕ) * D.r + ρ k) % D.r = ρ k := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hi : (⟨((ι : ℕ) * D.r + ρ k) / D.r, by rw [e1]; exact ι.isLt⟩ : Fin D.I) = ι := Fin.ext e1
    have hk : ρ.symm ⟨((ι : ℕ) * D.r + ρ k) % D.r, by rw [e2]; exact hr⟩ = k := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext e2
    have key : ∀ (i' : Fin D.I) (k' : K), i' = ι → k' = k →
        C2 (dirP6 D ρ) u i' k' → C2 (dirP6 D ρ) u ι k := by
      rintro _ _ rfl rfl h'
      exact h'
    exact key _ _ hi hk h
  · intro h i hi
    exact h _ _

theorem C3F_iff : (∀ i, C3F D ρ u i) ↔ ∀ ι k δ nx, C3 (dirP6 D ρ) u ι k δ nx := by
  constructor
  · intro hF ι k δ nx
    have hr : (ρ k : ℕ) < D.r := (ρ k).isLt
    have hδ : (δ : ℕ) < 3 := δ.isLt
    set b : ℕ := if nx then 1 else 0 with hb
    have hb2 : b < 2 := by rw [hb]; split <;> omega
    set j : ℕ := (((ι : ℕ) * D.r + ρ k) * 3 + δ) * 2 + b with hj
    have hlt : j < D.I * D.r * 3 * 2 := by
      have := ι.isLt
      have h1 : (ι : ℕ) * D.r + ρ k < D.I * D.r := by
        calc (ι : ℕ) * D.r + ρ k < (ι + 1) * D.r := by rw [Nat.add_mul, Nat.one_mul]; omega
          _ ≤ D.I * D.r := Nat.mul_le_mul_right _ this
      omega
    have h := hF j hlt
    have e0 : j / 2 = ((ι : ℕ) * D.r + ρ k) * 3 + δ := by omega
    have eb : j % 2 = b := by omega
    have e3 : j / 2 / 3 = (ι : ℕ) * D.r + ρ k := by rw [e0]; omega
    have eδ : j / 2 % 3 = δ := by rw [e0]; omega
    have e1 : j / 2 / 3 / D.r = ι := by
      rw [e3, Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
    have e2 : j / 2 / 3 % D.r = ρ k := by
      rw [e3, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hι : (⟨j / 2 / 3 / D.r, by rw [e1]; exact ι.isLt⟩ : Fin D.I) = ι := Fin.ext e1
    have hk : ρ.symm ⟨j / 2 / 3 % D.r, by rw [e2]; exact hr⟩ = k := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext e2
    have hδ' : (⟨j / 2 % 3, by rw [eδ]; exact hδ⟩ : Fin 3) = δ := Fin.ext eδ
    have hnx : decide (j % 2 = 1) = nx := by
      rw [eb, hb]
      cases nx <;> simp
    have key : ∀ (i' : Fin D.I) (k' : K) (δ'' : Fin 3) (b' : Bool), i' = ι → k' = k → δ'' = δ → b' = nx →
        C3 (dirP6 D ρ) u i' k' δ'' b' → C3 (dirP6 D ρ) u ι k δ nx := by
      rintro _ _ _ _ rfl rfl rfl rfl h'
      exact h'
    exact key _ _ _ _ hι hk hδ' hnx h
  · intro h i hi
    exact h _ _ _ _

/-- **Stage 0 in the indexed form of D5.** Every index of the families C1, C2, C3 passes iff the directory part of
the P6 witness is true. -/
theorem dirF_iff : ((∀ i, C1F D ρ u i) ∧ (∀ i, C2F D ρ u i) ∧ (∀ i, C3F D ρ u i)) ↔ DirTrue (dirP6 D ρ) u := by
  rw [C1F_iff, C2F_iff, C3F_iff]
  exact dir_iff _ u

end P1ChkDir
