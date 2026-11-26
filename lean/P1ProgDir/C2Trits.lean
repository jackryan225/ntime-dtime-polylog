import P1ProgDir.C2Reply
import P1ProgDir.FieldWords
import P1ProgDir.Rows
import P1ProgDir.SmallBatch
import P1ProgDir.ScanSlice

namespace P1ProgDir.SolC2Trits

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ProgDir.SolC2Reply P1ProgDir.SolGeometry P1ProgDir.SolFieldWords
open P1ProgDir.SolFieldRead P1Wit

theorem tally_of_length (r : Tally) : tally r.length = r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases a
    change () :: tally r.length = () :: r
    rw [ih]

def modWord (r : ℕ) [NeZero r] (w : Word) : Word :=
  (sub (w, scale r (qword (p := r) w))).1

theorem easy_modWord (r : ℕ) [NeZero r] : Easy (modWord r) :=
  (easy_sub (Easy.identity.pair (easy_scale r (easy_qword Easy.identity)))).fstCompose

theorem modWord_value (r : ℕ) [NeZero r] (w : Word) :
    value (modWord r w) = value w % r := by
  have h := Nat.div_add_mod (value w) r
  have hl : value (scale r (qword (p := r) w)) ≤ value w := by
    rw [scale_exact, qword_value]
    omega
  unfold modWord
  rw [sub_val_le _ _ hl, scale_exact, qword_value]
  omega

def laneTally (a b : ℕ) (n : Word) : Tally := tally (laneCount a b (value n))

theorem poly_laneTally (a b : ℕ) : Poly (laneTally a b) := by
  let p (n : Word) := powWord (hTally a b n)
  have hp : Poly p := (poly_hTally a b).compose easy_powWord.poly
  have hval (n : Word) : P1Batch.bval (p n) = laneCount a b (value n) := by
    simp only [p, P1Batch.bval_eq_value, powWord_value, hTally_length, laneCount]
  have hv : Dom (fun n : Word => size n) (fun n => P1Batch.bval (p n)) := by
    apply ((Code.Poly.length (poly_lambdaTally a b)).pow 10).mono
    intro n
    let l := P1Int.lpK2 a b (value n)
    let z := Nat.log 2 l
    rw [hval, laneCount, size_tally, lambdaTally_length]
    change 2 ^ (19 * z / 2) ≤ (2 * l + 1) ^ 10
    have hlog : 2 ^ z ≤ 2 * l + 1 := by
      by_cases h : l = 0
      · simp only [z, h, Nat.log_zero_right, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
      · exact (Nat.pow_log_le_self 2 h).trans (by omega)
    calc
      _ ≤ 2 ^ (z * 10) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (2 ^ z) ^ 10 := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left hlog _
  have hd : Dom (fun n : Word => size n) (fun n => (p n).length) := by
    apply (Code.Poly.length hp).mono
    intro n
    rw [size_word]
    omega
  obtain ⟨α, hα, hpre⟩ := hp
  refine ⟨_, hα.add (hv.add hd), (hpre.compose (P1Batch.countdown.on p)).conform
    (fun _ => rfl) (fun _ => rfl) (fun n => ?_)⟩
  rw [hval] <;> rfl

theorem poly_tally_mod (r : ℕ) [NeZero r] :
    Poly (fun w : Word => tally (value (modWord r w))) := by
  let p (w : Word) := modWord r w
  have e : Task (fun w => P1Batch.bval (p w) + (p w).length)
      (fun w => send (p w)) (fun w => send (tally (value (p w)))) :=
    (P1Batch.countdown.on p).conform (fun _ => rfl) (fun _ => rfl)
    (fun w => by rw [P1Batch.bval_eq_value])
  have hdom : Dom (fun w : Word => size w) (fun w => P1Batch.bval (p w) + (p w).length) := by
    apply ((Dom.const _ r).add (Code.Poly.length (easy_modWord r).poly)).mono
    intro w
    change P1Batch.bval (modWord r w) + (modWord r w).length ≤ r + size (modWord r w)
    rw [P1Batch.bval_eq_value, modWord_value, size_word]
    have h := Nat.mod_lt (value w) (Nat.pos_of_ne_zero (NeZero.ne r))
    omega
  exact ⟨_, (Dom.base _).add hdom, Task.compose (easy_modWord r) e⟩

def countWord (k : ℕ) (l : List Word) : Word :=
  born ((l.map fun w => bif eqWord (w, born k) then [()] else []).flatten).length

theorem easy_countWord (k : ℕ) : Easy (countWord k) := by
  have ht : Easy (fun w : Word => bif eqWord (w, born k) then [()] else []) :=
    (((Easy.identity.pair (Easy.const (born k))).compose easy_eqWord).pair Easy.identity).compose
      (Easy.ifst (Easy.const ([] : Tally)) (Easy.const [()]))
  have hf : Easy (List.flatten : List Tally → Tally) := by fun_prop
  exact (ht.mapping.compose hf).compose easy_chart

theorem countWord_value (k : ℕ) (l : List Word) :
    value (countWord k l) = ((l.map value).filter (· == k)).length := by
  unfold countWord
  rw [birthValue]
  induction l with
  | nil => rfl
  | cons w l ih =>
    by_cases h : value w = k
    · have he : eqWord (w, born k) = true := (eqWord_eq _).mpr (by rw [birthValue]; exact h)
      simpa [h, he] using ih
    · have he : eqWord (w, born k) = false := by
        cases e : eqWord (w, born k)
        · rfl
        · exact (h (((eqWord_eq (w, born k)).mp e).trans (birthValue k))).elim
      simpa [h, he] using ih

/-- All rows have the same tape offset. Duplicate that short offset once per row. -/
theorem poly_withOffset {Y : Type} [Codec Y] :
    Poly (fun p : List Y × Tally => p.1.zip (List.replicate p.1.length p.2)) := by
  let R := List Y × Tally
  let pair (p : R) := (p.1, List.replicate p.1.length p.2)
  have hgen := Code.generate (X := Tally)
  have hd : Dom (fun p : R => size p) (fun p =>
      (p.1.length + 1) * (size p.2 + 1)) := by
    apply ((Dom.base _).add (Dom.const _ 1)).pow 2 |>.mono
    intro p
    have h := Code.duration p.1
    rw [size_prod, pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hcopy : Poly (fun p : R => List.replicate p.1.length p.2) := by
    have he : Easy (fun p : R => (ruler p.1, p.2)) :=
      (Easy.ruler Easy.fst).pair Easy.snd
    have hgen' : Task (fun p : R => (p.1.length + 1) * size p.2)
        (fun p => send (ruler p.1, p.2)) (fun p => send (List.replicate p.1.length p.2)) :=
      (hgen.on (fun p : R => (ruler p.1, p.2))).conform
        (fun p => by
          change ((ruler p.1).length + 1) * size p.2 = _
          rw [ruler_length]) (fun _ => rfl) (fun p => by
          change send (List.replicate (ruler p.1).length p.2) = _
          rw [ruler_length])
    refine ⟨_, (Dom.base _).add (hd.mono ?_), Task.compose he hgen'⟩
    intro p
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hp : Poly pair := Poly.identity.fstCompose.pair hcopy
  have hsz := hp.length
  obtain ⟨α, hα, hpre⟩ := hp
  let z (p : R) : {i : List Y × List Tally // i.1.length = i.2.length} :=
    ⟨pair p, by simp only [pair, List.length_replicate]⟩
  exact ⟨_, hα.add hsz, hpre.compose (zip_spec.on z)⟩

def tritWord (p : Word × Tally) : Word :=
  (cutLists (tally 2, (cutLists (timesTally 2 p.2, p.1)).2)).1

theorem easy_tritWord : Easy tritWord := by
  have hp : Easy (fun p : Word × Tally => (timesTally 2 p.2, p.1)) :=
    (Easy.snd.compose (easy_timesTally 2)).pair Easy.fst
  have h := easy_cut hp
  exact (easy_cut ((Easy.const (tally 2)).pair h.sndCompose)).fstCompose

def trits (r : ℕ) (p : Tally × Tally × Word) : List Word :=
  let rows := SolRows.rows ((p.1, tally (r * 2)), p.2.2)
  (rows.zip (List.replicate rows.length p.2.1)).map tritWord

theorem poly_trits (r : ℕ) : Poly (trits r) := by
  let P := Tally × Tally × Word
  let input (p : P) := ((p.1, tally (r * 2)), p.2.2)
  have hinput : Easy input := (Easy.fst.pair (Easy.const _)).pair (Easy.snd.compose Easy.snd)
  have hrows : Poly SolRows.rows := by
    refine Code.Poly.of_bound SolRows.rows_task ?_
    refine (((Dom.base _).add (Dom.const _ 1)).pow 2 |>.add (Dom.base _)).mono ?_
    intro p
    rw [pow_two, size_prod, size_prod, size_tally, size_tally]
    let U := 2 * p.1.1.length + 1 + (2 * p.1.2.length + 1) + 1 + size p.2 + 1 + 1
    have h₁ : p.1.1.length + 1 ≤ U := by unfold U; omega
    have h₂ : p.1.2.length + 1 ≤ U := by unfold U; omega
    have h := Nat.mul_le_mul h₁ h₂
    unfold U at h
    omega
  exact ((hinput.poly.compose hrows).pair (Poly.identity.sndCompose.fstCompose)).compose
    (poly_withOffset.compose easy_tritWord.mapping.poly)

theorem trits_values (D : Dims) (w : Word) (i t : ℕ) (ht : t < D.r) :
    (trits D.r (tally D.N, tally t,
      (w.drop (i * (D.N * D.r * 2))).take (D.N * D.r * 2))).map value =
      (List.range D.N).map (fun g => rdTrit D w (i * D.N + g) t) := by
  let a := i * (D.N * D.r * 2)
  let l := D.N * D.r * 2
  let b := D.r * 2
  unfold trits SolRows.rows
  rw [SolRows.rows_eq]
  have hz (s : List Word) (r : Tally) :
      s.zip (List.replicate s.length r) = s.map (fun v => (v, r)) := by
    induction s with
    | nil => rfl
    | cons v s ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.map_cons, ih]
  simp only [tally_length, hz, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  have hs₁ : j * b + b ≤ l := by
    change j * (D.r * 2) + D.r * 2 ≤ D.N * D.r * 2
    rw [← Nat.succ_mul, Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hj'
  have hs₂ : 2 * t + 2 ≤ b := by unfold b; omega
  change value (tritWord (((((w.drop a).take l).drop (j * b)).take b), tally t)) =
    rdTrit D w (i * D.N + j) t
  simp only [tritWord, cutLists, timesTally_length, tally_length]
  rw [SolScanSlice.slice_of_slice _ _ _ _ _ hs₁]
  rw [List.drop_take, List.take_take, Nat.min_eq_left (show 2 ≤ b - 2 * t by omega), List.drop_drop]
  simp only [rdTrit, readField, readNat, SolOffsets.off_trit, P1ChkDir.width_trit, Nat.zero_add,
    bitsVal_eq_value]
  congr 2
  unfold a b
  ring

end P1ProgDir.SolC2Trits
