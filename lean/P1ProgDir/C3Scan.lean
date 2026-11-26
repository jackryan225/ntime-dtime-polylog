import P1ProgDir.C3Index
import P1ProgDir.C3Step
import P1ProgDir.IndexedSweep
import P1ProgDir.Offsets
import P1ProgDir.FieldRead
import P1ProgDir.Rows
import P1ProgDir.ScanSlice

namespace P1ProgDir.SolC3Scan

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Wit P1ChkDir
open P1ProgDir.SolSigned P1ProgDir.SolC3Step P1ProgDir.SolReadbacks
open P1ProgDir.SolScanSlice P1ProgDir.SolFieldRead

abbrev Comparison := Bool × Bool × Word × Word × Word × Word
abbrev Context := Comparison × Tally × Tally × Tally

def block (c : Context) (row : Word) : Word := quotient (c.2.1, slice ((c.2.2.1, c.2.2.2), row))

def rowTest (p : Context × Word × Word) : Bool :=
  let c := p.1.1
  entryStep (c.1, c.2.1, c.2.2.1, c.2.2.2.1, p.2.1, c.2.2.2.2.1,
    c.2.2.2.2.2, block p.1 p.2.2)

theorem easy_rowTest : Easy rowTest := by
  let P := Context × Word × Word
  have hc : Easy (fun p : P => p.1.1) := Easy.fst.compose Easy.fst
  have hh : Easy (fun p : P => p.1.2.1) := Easy.fst.compose (Easy.snd.compose Easy.fst)
  have hk : Easy (fun p : P => p.1.2.2.1) := Easy.fst.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
  have hw : Easy (fun p : P => p.1.2.2.2) := Easy.fst.compose (Easy.snd.compose (Easy.snd.compose Easy.snd))
  have hr := ((hk.pair hw).pair (Easy.snd.compose Easy.snd)).compose easy_slice
  have hb := (hh.pair hr).compose easy_quotient
  have ha : Easy (fun p : P => p.1.1.1) := hc.compose Easy.fst
  have hn : Easy (fun p : P => p.1.1.2.1) := hc.compose (Easy.snd.compose Easy.fst)
  have hi : Easy (fun p : P => p.1.1.2.2.1) := hc.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))
  have ho : Easy (fun p : P => p.1.1.2.2.2.1) :=
    hc.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst)))
  have hl : Easy (fun p : P => p.1.1.2.2.2.2.1) :=
    hc.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.fst))))
  have hu : Easy (fun p : P => p.1.1.2.2.2.2.2) :=
    hc.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose (Easy.snd.compose Easy.snd))))
  exact (ha.pair (hn.pair (hi.pair (ho.pair ((Easy.snd.compose Easy.fst).pair
    (hl.pair (hu.pair hb))))))).compose easy_entryStep

def numericRowTest (c : Context) (j : ℕ) (row : Word) : Bool :=
  let a := c.1
  let i := value a.2.2.1
  let link := value a.2.2.2.1
  let b := signedValue (block c row)
  rowOK a.2.1
    (decide (if a.1 then i < j else j < i))
    (decide (if a.1 then j < link else link < j)) (decide (j = link))
    (decide (signedValue a.2.2.2.2.1 ≤ b ∧ b ≤ signedValue a.2.2.2.2.2))

theorem rowTest_eq (c : Context) (j row : Word) :
    rowTest (c, j, row) = numericRowTest c (value j) row := by
  unfold rowTest numericRowTest
  rw [entryStep_eq]

def startRows (D : Dims) (w : Word) : List Word :=
  SolRows.rows ((tally D.I, tally (D.r * D.bigW)),
    (w.drop (D.off secStart)).take (D.I * (D.r * D.bigW)))

theorem startRows_eq (D : Dims) (w : Word) :
    startRows D w =
      (List.range D.I).map (fun j => (w.drop (D.off secStart + j * (D.r * D.bigW))).take (D.r * D.bigW)) := by
  unfold startRows SolRows.rows
  rw [SolRows.rows_eq]
  simp only [tally_length]
  apply List.map_congr_left
  intro j hj
  apply slice_of_slice
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (List.mem_range.mp hj)

theorem startRows_length (D : Dims) (w : Word) : (startRows D w).length = D.I := by
  rw [startRows_eq, List.length_map, List.length_range]

theorem startRow_block (D : Dims) (w : Word) (c : Context) (j : Fin (startRows D w).length)
    (k : ℕ) (hk : k < D.r) (hoff : c.2.2.1.length = k * D.bigW)
    (hwidth : c.2.2.2.length = D.bigW) (hN : 2 ^ c.2.1.length = D.N) :
    signedValue (block c (startRows D w)[j]) = bigOf D.N (unzigzag (rdStart D w j k)) := by
  have hrow : (startRows D w)[j] =
      (w.drop (D.off secStart + j.val * (D.r * D.bigW))).take (D.r * D.bigW) := by
    change (startRows D w)[j.val] = _
    simp only [startRows_eq, List.getElem_map, List.getElem_range]
  have hb : k * D.bigW + D.bigW ≤ D.r * D.bigW := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hk
  unfold block
  rw [quotient_value, ← Int.natCast_pow, hN, hrow]
  simp only [slice, cutLists, hoff, hwidth]
  rw [slice_of_slice _ _ _ _ _ hb]
  simp only [signedValue, bigOf, rdStart, readField, readNat, width_start, bitsVal_eq_value]
  rw [show D.off secStart + j.val * (D.r * D.bigW) + k * D.bigW =
    D.off secStart + (j.val * D.r + k) * D.bigW by ring]

open Classical in
theorem scan_iff (D : Dims) (w : Word) (c : Context) (counter : Tally)
    (i : Fin D.I) (k : ℕ) (hk : k < D.r) (Q : ℤ) (nx : Bool) (link : Option (Fin D.I))
    (hcap : D.I < 2 ^ counter.length)
    (hnx : c.1.1 = nx) (hnull : c.1.2.1 = link.isNone)
    (hi : value c.1.2.2.1 = i)
    (hlink : ∀ j : Fin D.I, link = some j → value c.1.2.2.2.1 = j)
    (hlo : signedValue c.1.2.2.2.2.1 = Q - 1) (hhi : signedValue c.1.2.2.2.2.2 = Q + 1)
    (hoff : c.2.2.1.length = k * D.bigW)
    (hwidth : c.2.2.2.length = D.bigW) (hN : 2 ^ c.2.1.length = D.N) :
    SolIndexedSweep.run rowTest (startRows D w, counter, c) = true ↔
      linkValid (fun j => OwnsB D.N (unzigzag (rdStart D w j k)) Q) i nx link := by
  let owns (j : Fin D.I) := decide (OwnsB D.N (unzigzag (rdStart D w j k)) Q)
  have howns : (fun j => owns j = true) =
      (fun j : Fin D.I => OwnsB D.N (unzigzag (rdStart D w j k)) Q) := by
    funext j
    exact decide_eq_true_eq
  rw [SolIndexedSweep.run_iff rowTest (numericRowTest c) (startRows D w) (counter, c)
    (rowTest_eq c) (by rw [startRows_length]; exact hcap),
    ← howns, linkValid_iff_rowOK]
  have hstep (j : Fin (startRows D w).length) :
      numericRowTest c j.val (startRows D w)[j] =
        rowOK link.isNone
          (decide (if nx then i < j.cast (startRows_length D w) else j.cast (startRows_length D w) < i))
          (decide (if nx then j.cast (startRows_length D w) < link.getD i else link.getD i < j.cast (startRows_length D w)))
          (decide (some (j.cast (startRows_length D w)) = link)) (owns (j.cast (startRows_length D w))) := by
    have hb := startRow_block D w c j k hk hoff hwidth hN
    have he : (Q - 1 ≤ bigOf D.N (unzigzag (rdStart D w j k)) ∧
           bigOf D.N (unzigzag (rdStart D w j k)) ≤ Q + 1) =
          OwnsB D.N (unzigzag (rdStart D w j k)) Q := by
      unfold OwnsB
      exact propext (by omega)
    unfold numericRowTest owns
    simp only [hnx, hnull, hi, hlo, hhi, hb, he, Fin.val_cast, Fin.lt_def]
    cases hlink' : link with
    | none => rfl
    | some v =>
      simp only [Option.getD_some, Option.some.injEq, Fin.ext_iff, Fin.val_cast, hlink v hlink']
  constructor
  · intro h j
    let j' : Fin (startRows D w).length := j.cast (startRows_length D w).symm
    have he := h j'
    rw [hstep] at he
    simpa only [j', Fin.cast_cast, Fin.cast_refl, id_eq] using he
  · intro h j
    rw [hstep]
    exact h (j.cast (startRows_length D w))

end P1ProgDir.SolC3Scan
