import P1P5.Factor0Target
import P1Int.DirLinkProof
import P1ChkFinal.ProgC11
import P1ChkFinal.C10RcPoly

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1Wit.SolWitfill
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

/-- A request for consecutive fields from one section of the P6 directory. -/
def blockReq (sectionOff width first count : ℕ) : P1Batch.Req :=
  (binary (sectionOff + first * width), binary (count * width))

theorem blockReq_poly : Poly (fun p : ℕ × ℕ × ℕ × ℕ => blockReq p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold blockReq
  have binaryPoly : Poly (binary : ℕ → List Bool) := by
    obtain ⟨t, ht, h⟩ := (Poly.identity : Poly (fun n : ℕ => n))
    exact ⟨t, ht, h⟩
  exact ((show Poly (fun p : ℕ × ℕ × ℕ × ℕ => p.1 + p.2.2.1 * p.2.1) from by fun_prop).compose
    binaryPoly).pair ((show Poly (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2 * p.2.1) from by fun_prop).compose
    binaryPoly)

/-- Reading a field inside a fetched block agrees with reading the original section. -/
theorem readNat_fetch_block (u : List Bool) (sectionOff width first count j : ℕ) (hj : j < count) :
    readNat (P1Batch.fetch u (blockReq sectionOff width first count)) (j * width) width =
      readNat u (sectionOff + (first + j) * width) width := by
  simp only [readNat, P1Batch.fetch, blockReq, bval_binary, List.drop_take, List.drop_drop,
    List.take_take, Nat.add_mul, Nat.add_assoc]
  have hmul : (j + 1) * width ≤ count * width := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hw : width ≤ count * width - j * width := by omega
  rw [Nat.min_eq_left hw]

/-- Read the four directory records of one big interval in consecutive blocks. -/
def intervalReqs (r I N w i : ℕ) : List P1Batch.Req :=
  let trits := I * N * r * 2
  let starts := I * r * w
  let owners := I * r * 3 * w
  [blockReq 0 2 (i * N * r) (N * r),
   blockReq trits w (i * r) r,
   blockReq (trits + starts) w (i * r * 3) (r * 3),
   blockReq (trits + starts + owners) w (i * r * 3) (r * 3)]

theorem intervalReqs_poly (r : ℕ) :
    Poly (fun p : ℕ × ℕ × ℕ × ℕ => intervalReqs r p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := ℕ × ℕ × ℕ × ℕ
  let fields (off width first count : P → ℕ) (ho : Poly off) (hw : Poly width)
      (hf : Poly first) (hc : Poly count) :=
    (ho.pair (hw.pair (hf.pair hc))).compose blockReq_poly
  have h0 := fields (fun _ => 0) (fun _ => 2)
    (fun p => p.2.2.2 * p.2.1 * r) (fun p => p.2.1 * r)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h1 := fields (fun p => p.1 * p.2.1 * r * 2) (fun p => p.2.2.1)
    (fun p => p.2.2.2 * r) (fun _ => r)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 := fields (fun p => p.1 * p.2.1 * r * 2 + p.1 * r * p.2.2.1) (fun p => p.2.2.1)
    (fun p => p.2.2.2 * r * 3) (fun _ => r * 3)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h3 := fields (fun p => p.1 * p.2.1 * r * 2 + p.1 * r * p.2.2.1 + p.1 * r * 3 * p.2.2.1)
    (fun p => p.2.2.1) (fun p => p.2.2.2 * r * 3) (fun _ => r * 3)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have tail3 := (h3.pair (Code.Poly.const ([] : List P1Batch.Req))).compose Poly.cons
  have tail2 := (h2.pair tail3).compose Poly.cons
  have tail1 := (h1.pair tail2).compose Poly.cons
  exact (h0.pair tail1).compose Poly.cons

theorem total_intervalReqs (r I N w i : ℕ) :
    P1Batch.total (intervalReqs r I N w i) = N * r * 2 + r * w + 2 * (r * 3 * w) := by
  simp only [intervalReqs, P1Batch.total, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, blockReq, bval_binary, Nat.add_zero, Nat.two_mul]
  omega

section Fields

theorem off_secTrit (D : Dims) : D.off secTrit = 0 := rfl
theorem off_secStart (D : Dims) : D.off secStart = D.I * D.N * D.r * 2 := by
  simp only [Dims.off, secStart, offAt, Dims.count, Dims.width, Dims.kind, Nat.zero_add, if_true]
theorem off_secPrev (D : Dims) : D.off secPrev = D.I * D.N * D.r * 2 + D.I * D.r * D.bigW := by
  simp only [Dims.off, secPrev, offAt, Dims.count, Dims.width, Dims.kind, Nat.zero_add, Nat.reduceEqDiff,
    if_true, if_false]
theorem off_secNext (D : Dims) :
    D.off secNext = D.I * D.N * D.r * 2 + D.I * D.r * D.bigW + D.I * D.r * 3 * D.bigW := by
  simp only [Dims.off, secNext, offAt, Dims.count, Dims.width, Dims.kind, Nat.zero_add, Nat.reduceEqDiff,
    if_true, if_false]

theorem rdTrit_interval (D : Dims) (u : List Bool) (i j tape : ℕ)
    (hj : j < D.N) (ht : tape < D.r) :
    readNat (P1Batch.fetch u ((intervalReqs D.r D.I D.N D.bigW i).getD 0 ([], [])))
      ((j * D.r + tape) * 2) 2 = rdTrit D u (i * D.N + j) tape := by
  change readNat (P1Batch.fetch u (blockReq 0 2 (i * D.N * D.r) (D.N * D.r)))
    ((j * D.r + tape) * 2) 2 = _
  rw [readNat_fetch_block _ _ _ _ _ _ (idx_lt hj ht)]
  simp only [rdTrit, readField, off_secTrit, Dims.width, D.kind_trit, Nat.add_mul, Nat.add_assoc]

theorem rdStart_interval (D : Dims) (u : List Bool) (i tape : ℕ) (ht : tape < D.r) :
    readNat (P1Batch.fetch u ((intervalReqs D.r D.I D.N D.bigW i).getD 1 ([], [])))
      (tape * D.bigW) D.bigW = rdStart D u i tape := by
  change readNat (P1Batch.fetch u (blockReq (D.I * D.N * D.r * 2) D.bigW (i * D.r) D.r))
    (tape * D.bigW) D.bigW = _
  rw [readNat_fetch_block _ _ _ _ _ _ ht]
  simp only [rdStart, readField, off_secStart, Dims.width, D.kind_start]

theorem rdPrev_interval (D : Dims) (u : List Bool) (i tape δ : ℕ) (ht : tape < D.r) (hδ : δ < 3) :
    readNat (P1Batch.fetch u ((intervalReqs D.r D.I D.N D.bigW i).getD 2 ([], [])))
      ((tape * 3 + δ) * D.bigW) D.bigW = rdPrev D u i tape δ := by
  change readNat (P1Batch.fetch u (blockReq (D.I * D.N * D.r * 2 + D.I * D.r * D.bigW)
    D.bigW (i * D.r * 3) (D.r * 3))) ((tape * 3 + δ) * D.bigW) D.bigW = _
  rw [readNat_fetch_block _ _ _ _ _ _ (idx_lt ht hδ)]
  simp only [rdPrev, readField, off_secPrev, Dims.width, D.kind_prev, Nat.add_mul, Nat.add_assoc]

theorem rdNext_interval (D : Dims) (u : List Bool) (i tape δ : ℕ) (ht : tape < D.r) (hδ : δ < 3) :
    readNat (P1Batch.fetch u ((intervalReqs D.r D.I D.N D.bigW i).getD 3 ([], [])))
      ((tape * 3 + δ) * D.bigW) D.bigW = rdNext D u i tape δ := by
  change readNat (P1Batch.fetch u (blockReq (D.I * D.N * D.r * 2 + D.I * D.r * D.bigW +
    D.I * D.r * 3 * D.bigW) D.bigW (i * D.r * 3) (D.r * 3))) ((tape * 3 + δ) * D.bigW) D.bigW = _
  rw [readNat_fetch_block _ _ _ _ _ _ (idx_lt ht hδ)]
  simp only [rdNext, readField, off_secNext, Dims.width, D.kind_next, Nat.add_mul, Nat.add_assoc]

end Fields

/-- The directory records at an encoded tuple are exactly the corresponding fixed fields. -/
theorem readDirectory_encTuple {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R t).length ≤ m) :
    let w := List.ofFn (encTuple R m t)
    let f := ofTuple R t
    (∀ (i : Fin (D.I * D.N)) (k : Fin D.r), rdTrit D w i k = f.trit i k) ∧
    (∀ (i : Fin D.I) (k : Fin D.r), rdStart D w i k = f.start i k) ∧
    (∀ (i : Fin D.I) (k : Fin D.r) (δ : Fin 3), rdPrev D w i k δ = f.prevOwn i k δ) ∧
    (∀ (i : Fin D.I) (k : Fin D.r) (δ : Fin 3), rdNext D w i k δ = f.nextOwn i k δ) := by
  dsimp only
  have hw : List.ofFn (encTuple R m t) = enc D m (ofTuple R t) (tuplePayload R t) :=
    ofFn_encFn _ _ _ _ hm
  rw [hw]
  exact ⟨fun i k => rdTrit_enc D m _ _ (ofTuple_inRange R t) i.isLt k.isLt,
    fun i k => rdStart_enc D m _ _ (ofTuple_inRange R t) i.isLt k.isLt,
    fun i k δ => rdPrev_enc D m _ _ (ofTuple_inRange R t) i.isLt k.isLt δ.isLt,
    fun i k δ => rdNext_enc D m _ _ (ofTuple_inRange R t) i.isLt k.isLt δ.isLt⟩

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.rdTrit_interval
