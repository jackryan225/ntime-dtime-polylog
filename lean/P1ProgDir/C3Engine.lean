import P1ProgDir.C3Input

namespace P1ProgDir.SolC3Engine

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ProgDir.SolC3Input P1ProgDir.SolC3Scan P1ProgDir.SolFieldWords P1ProgDir.SolScanSlice
open P1ProgDir.SolC2Trits (modWord_value)

abbrev Packed := P1Batch.Req × ScanArgs
abbrev SliceArgs := Word × Tally × ScanArgs

def packed (r : ℕ) [NeZero r] (p : Output) : Packed :=
  let z := scanArgs r p
  ((p.2.2.1.2.1, product (z.2.2.1, born z.2.2.2.1.length)), z)

theorem poly_packed (r : ℕ) [NeZero r] : Poly (packed r) := by
  have h := poly_scanArgs r
  have hI := h.sndCompose.sndCompose.fstCompose
  have hW := h.sndCompose.sndCompose.sndCompose.fstCompose.compose easy_chart.poly
  have ha : Poly (fun p : Output => p.2.2.1.2.1) :=
    Poly.identity.sndCompose.sndCompose.fstCompose.sndCompose.fstCompose
  exact (ha.pair (poly_mul hI hW)).pair h

theorem packed_size (r : ℕ) [NeZero r] :
    ∃ C : ℕ, ∀ p : Output, size (packed r p) ≤ C * (size p + 1) := by
  obtain ⟨A, hA⟩ := (easy_scanWithOffset r).length
  refine ⟨5 * (r + 3) * A + 3, ?_⟩
  intro p
  let z := scanArgs r p
  have hw : 2 * p.2.2.2.1.length + 1 ≤ size p := by simp only [size_prod, size_tally]; omega
  have ht : value (tapeWord r p.2) ≤ r :=
    ((modWord_value r _).trans_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne r)))).le
  have hcut : size (cutOffset r p.2) ≤ r * size p + 1 := by
    rw [cutOffset, size_tally, tally_length]
    have hm := Nat.mul_le_mul_right (p.2.2.2.1.length) ht
    have hn := Nat.mul_le_mul_left r (show 2 * p.2.2.2.1.length ≤ size p by omega)
    apply Nat.add_le_add_right
    exact (Nat.mul_le_mul_left 2 hm).trans ((show 2 * (r * p.2.2.2.1.length) =
      r * (2 * p.2.2.2.1.length) by ring).le.trans hn)
  have hsz : size z ≤ A * ((r + 3) * (size p + 1)) := by
    refine (hA (p, cutOffset r p.2)).trans (Nat.mul_le_mul_left _ ?_)
    rw [size_prod]
    calc
      _ ≤ size p + (r * size p + 1) + 1 := Nat.add_le_add_right (Nat.add_le_add_left hcut _) _
      _ ≤ (r + 3) * (size p + 1) := by
        rw [Nat.add_mul, Nat.mul_add r, Nat.mul_one]
        omega
  have haddr : size p.2.2.1.2.1 ≤ size p := by simp only [size_prod]; omega
  have hword : (z.2.2.1).length + z.2.2.2.1.length ≤ size z := by
    simp only [size_prod, size_word, size_tally]
    omega
  have hprod : size (product (z.2.2.1, born z.2.2.2.1.length)) ≤ 4 * size z + 1 := by
    rw [size_word, length_prod]
    change 2 * (2 * (z.2.2.1.length + (born z.2.2.2.1.length).length)) + 1 ≤ _
    have hlen := birthLen z.2.2.2.1.length
    omega
  change size p.2.2.1.2.1 + size (product (z.2.2.1, born z.2.2.2.1.length)) + 1 + size z + 1 ≤ _
  have he : 5 * size z ≤ (5 * (r + 3) * A) * (size p + 1) :=
    (Nat.mul_le_mul_left 5 hsz).trans_eq (by ring)
  rw [Nat.add_mul]
  omega

def rowInput (p : SliceArgs) : (Tally × Tally) × Word :=
  ((p.2.1, p.2.2.2.2.2.1), p.1)

def context (p : ScanArgs) : SolIndexedSweep.Context Context := (ruler p.2.2.1, p.2.2.2.2)

def rows (p : Packed) (w : Word) : List Word :=
  SolRows.rows (rowInput (P1Batch.fetch w p.1, tally (P1Batch.bval p.2.2.2.1), p.2))

def finish (p : Bool × Bool × Bool) : Bool := !p.2.1 || (p.2.2 && p.1)

def reply (p : Packed) (w : Word) : Bool :=
  finish (SolIndexedSweep.run rowTest (rows p w, context p.2), p.2.1, p.2.2.1)

theorem cost_parts (w : Word) (p : Packed)
    (hf : P1Batch.bval p.1.1 + P1Batch.bval p.1.2 ≤ w.length) :
    let n := P1Batch.bval p.2.2.2.1
    let h := size p
    size (P1Batch.fetch w p.1) ≤ 2 * w.length + 1 ∧
    size (context p.2) + 2 * (context p.2).1.length + 5 ≤ 3 * h + 10 ∧
    size (rows p w) ≤ 3 * (n + 1) * (h + 1) ∧
    (rows p w).length = n := by
  dsimp only
  let n := P1Batch.bval p.2.2.2.1
  let W := p.2.2.2.2.1.length
  let h := size p
  have hw : W + 1 ≤ h := by
    unfold W h
    simp only [size_prod, size_tally]
    omega
  have hd : 2 * p.2.2.2.1.length + size p.2.2.2.2.2 ≤ h := by
    unfold h
    simp only [size_prod, size_word]
    omega
  constructor
  · rw [size_word, P1Batch.fetch, List.length_take]
    have e := Nat.min_le_left (P1Batch.bval p.1.2) ((List.drop (P1Batch.bval p.1.1) w).length)
    omega
  constructor
  · change size (ruler p.2.2.2.1) + size p.2.2.2.2.2 + 1 +
      2 * (ruler p.2.2.2.1).length + 5 ≤ _
    rw [size_tally, ruler_length]
    omega
  have hrows : rows p w = (List.range n).map (fun j =>
      ((P1Batch.fetch w p.1).drop (j * W)).take W) := by
    unfold rows rowInput SolRows.rows
    rw [SolRows.rows_eq]
    simp only [tally_length, n, W]
  rw [hrows, List.length_map, List.length_range]
  refine ⟨?_, rfl⟩
  have hl : ∀ q ∈ (List.range n).map
      (fun j => ((P1Batch.fetch w p.1).drop (j * W)).take W), size q ≤ 2 * W + 1 := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    rw [size_word, List.length_take]
    have he := Nat.min_le_left W ((P1Batch.fetch w p.1).drop (j * W)).length
    omega
  have hsize (s : List Word) (hs : ∀ q ∈ s, size q ≤ 2 * W + 1) :
      size s ≤ s.length * (2 * W + 2) + 1 := by
    induction s with
    | nil => simp only [size_nil, List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
    | cons q s ih =>
      have hq := hs q List.mem_cons_self
      have ht := ih (fun u hu => hs u (List.mem_cons_of_mem _ hu))
      rw [size_cons, List.length_cons, Nat.succ_mul]
      omega
  refine (hsize _ hl).trans ?_
  rw [List.length_map, List.length_range]
  calc
    n * (2 * W + 2) + 1 ≤ n * (3 * (h + 1)) + 3 * (h + 1) := by
      have he := Nat.mul_le_mul_left n (show 2 * W + 2 ≤ 3 * (h + 1) by omega)
      omega
    _ = _ := by ring

/-- The large slice and fold both have linear cost in the physical data that
they traverse, plus one comparison context per row. -/
theorem task {X : Type} (p : X → Packed) (w : X → Word)
    (hf : ∀ x, P1Batch.bval (p x).1.1 + P1Batch.bval (p x).1.2 ≤ (w x).length) :
    Task (fun x => (w x).length + (P1Batch.bval (p x).2.2.2.1 + 1) * (size (p x) + 1))
      (fun x => send (p x, w x)) (fun x => send (reply (p x) (w x))) := by
  let z (x : X) := (p x).2
  let I (x : X) := P1Batch.bval (z x).2.2.1
  let seg (x : X) := P1Batch.fetch (w x) (p x).1
  let arg (x : X) : SliceArgs := (seg x, tally (I x), z x)
  let st (x : X) : Bool × Bool := ((z x).1, (z x).2.1)
  let ctx (x : X) := context (z x)
  let out (x : X) := rows (p x) (w x)
  have hpack : Easy (fun q : Packed × Word => ((q.1.1, q.2), q.1.2)) :=
    ((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)
  have h₁ := (hpack.on (fun x => (p x, w x))).compose
    ((boundedSlice (fun x => (p x).1) w hf).left (fun x => send (z x)))
  have h₂ := (((P1Batch.countdown.on (fun x => (z x).2.2.1)).left
    (fun x => send (z x))).right (fun x => send (seg x)))
  have hcopy : Easy (fun q : Word × ScanArgs => (q.1, q.2.2.2.1, q.2)) := by
    have hz : Easy (fun q : Word × ScanArgs => q.2) := Easy.snd
    exact Easy.fst.pair ((hz.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))).pair hz)
  have ht := (hcopy.on (fun x => (seg x, z x))).compose h₂
  have hargs : Easy (fun q : SliceArgs =>
      (rowInput q, context q.2.2, q.2.2.1, q.2.2.2.1)) := by
    have hz : Easy (fun q : SliceArgs => q.2.2) := Easy.snd.compose Easy.snd
    have hz' := hz.compose Easy.snd
    have hi : Easy (fun q : SliceArgs => q.2.1) := Easy.snd.compose Easy.fst
    have hw := hz'.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
    have hrows := (hi.pair hw).pair Easy.fst
    have hc : Easy (fun q : ScanArgs => context q) :=
      (Easy.ruler (Easy.snd.compose (Easy.snd.compose Easy.fst))).pair
        (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd)))
    exact hrows.pair ((hz.compose hc).pair ((hz.compose Easy.fst).pair (hz'.compose Easy.fst)))
  have h₃ := (hargs.on arg).compose
    ((SolRows.rows_task.on (fun x => rowInput (arg x))).left (fun x => send (ctx x, st x)))
  have hterm : Easy (fun q : List Word × SolIndexedSweep.Context Context × Bool × Bool =>
      ((q.1, q.2.1), q.2.2)) :=
    (Easy.fst.pair (Easy.snd.compose Easy.fst)).pair (Easy.snd.compose Easy.snd)
  have h₄ := (hterm.on (fun x => (out x, ctx x, st x))).compose
    (((SolIndexedSweep.task rowTest easy_rowTest).on (fun x => (out x, ctx x))).left
      (fun x => send (st x)))
  have h₅ := (Easy.finite finish).on (fun x => (SolIndexedSweep.run rowTest (out x, ctx x), st x))
  refine ((((h₁.compose ht).compose h₃).compose h₄).compose h₅).bound 64 ?_
  intro x
  obtain ⟨hs, hc, hr, hl⟩ := cost_parts (w x) (p x) (hf x)
  let m := (w x).length
  let H := size (p x)
  let J := I x
  let B := (J + 1) * (H + 1)
  change size (seg x) ≤ 2 * m + 1 at hs
  change size (ctx x) + 2 * (ctx x).1.length + 5 ≤ 3 * H + 10 at hc
  have hr' : size (out x) ≤ 3 * B := by
    change size (out x) ≤ _ at hr
    unfold B H J I z
    exact hr.trans_eq (by ring)
  change (out x).length = J at hl
  have hp : size (p x).1 + size (z x) + 1 = H := rfl
  have hI : 2 * (z x).2.2.1.length + 1 ≤ size (z x) := by
    simp only [size_prod, size_word]
    omega
  have hw : (z x).2.2.2.1.length + 1 ≤ H + 1 := by
    unfold H z
    simp only [size_prod, size_tally]
    omega
  have hrow : (J + 1) * ((z x).2.2.2.1.length + 1) ≤ B :=
    Nat.mul_le_mul_left _ hw
  have hsweep : (J + 1) * (size (ctx x) + 2 * (ctx x).1.length + 5) ≤ 10 * B := by
    calc
      _ ≤ (J + 1) * (10 * (H + 1)) := Nat.mul_le_mul_left _ (hc.trans (by omega))
      _ = 10 * B := by unfold B; ring
  have hBH : H + 1 ≤ B := Nat.le_mul_of_pos_left _ (by omega)
  have hBJ : J + 1 ≤ B := Nat.le_mul_of_pos_right _ (by omega)
  change size (p x, w x) + ((w x).length + size (p x).1) +
      (size (seg x, z x) + (size (seg x) + (I x + (z x).2.2.1.length))) +
      (size (arg x) + (((arg x).2.1.length + 1) * ((arg x).2.2.2.2.2.1.length + 1) + size (seg x))) +
      (size (out x, ctx x, st x) + (size (out x) +
        ((out x).length + 1) * (size (ctx x) + 2 * (ctx x).1.length + 5))) +
      size (SolIndexedSweep.run rowTest (out x, ctx x), st x) + 1 ≤ 64 * (m + B + 1)
  change size (p x, w x) + (m + size (p x).1) +
      (size (seg x, z x) + (size (seg x) + (J + (z x).2.2.1.length))) +
      (size (seg x, tally J, z x) + (((tally J).length + 1) * ((z x).2.2.2.1.length + 1) + size (seg x))) +
      (size (out x, ctx x, st x) + (size (out x) +
        ((out x).length + 1) * (size (ctx x) + 2 * (ctx x).1.length + 5))) +
      size (SolIndexedSweep.run rowTest (out x, ctx x), st x) + 1 ≤ 64 * (m + B + 1)
  change H + size (w x) + 1 + (m + size (p x).1) +
      (size (seg x) + size (z x) + 1 +
        (size (seg x) + (J + (z x).2.2.1.length))) +
      (size (seg x) + (size (tally J) + size (z x) + 1) + 1 +
        (((tally J).length + 1) * ((z x).2.2.2.1.length + 1) + size (seg x))) +
      (size (out x) + (size (ctx x) + (1 + 1 + 1) + 1) + 1 +
        (size (out x) + ((out x).length + 1) * (size (ctx x) + 2 * (ctx x).1.length + 5))) +
      (1 + (1 + 1 + 1) + 1) + 1 ≤ 64 * (m + B + 1)
  rw [size_word (w x), size_tally, tally_length, hl]
  have hm : (w x).length = m := rfl
  omega

end P1ProgDir.SolC3Engine
