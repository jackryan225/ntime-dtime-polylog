import P1SolGreedy.MotifFormat

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

def widthRequest (p : BaseRow × NumberWord × WireWords) : P1Batch.Req :=
  let (row, lanes, y, k, w) := p
  slotAt .width (row, joinWords (y, lanes, w), k)

@[fun_prop] theorem widthRequest_poly : Poly widthRequest := by unfold widthRequest; dsimp only; fun_prop

theorem widthRequest_value (D : Dims) (ℓ : ℕ) (z : WireWords) :
    requestNumbers (widthRequest (levelRow D ℓ, bin (D.lv ℓ).lanes, z)) =
      requestNumbers (fieldReq D (secLev ℓ .width)
        ((P1Batch.bval z.1 * (D.lv ℓ).lanes + P1Batch.bval z.2.2) * (D.lv ℓ).slots + P1Batch.bval z.2.1)) := by
  change requestNumbers (slotAt .width (levelRow D ℓ,
    joinWords (z.1, bin (D.lv ℓ).lanes, z.2.2), z.2.1)) = _
  rw [requestNumbers_slotAt, bval_joinWords, bval_bin]

def termRequest (p : BaseRow × MotifStride × NumberWord × NumberWord × NumberWord) : P1Batch.Req :=
  let (row, (_, keys, arity), y, key, c) := p
  fieldWords (rowSection .terms row, joinWords (joinWords (y, keys, key), arity, c))

@[fun_prop] theorem termRequest_poly : Poly termRequest := by unfold termRequest; dsimp only; fun_prop

theorem termRequest_value (D : Dims) (ℓ : ℕ) (y key c : NumberWord) :
    requestNumbers (termRequest (levelRow D ℓ,
      (bin (D.lv ℓ).lanes, bin (D.lv ℓ).termKeys, bin ((D.lv ℓ).termArity + 1)), y, key, c)) =
      requestNumbers (fieldReq D (secLev ℓ .terms)
        ((P1Batch.bval y * (D.lv ℓ).termKeys + P1Batch.bval key) * ((D.lv ℓ).termArity + 1) + P1Batch.bval c)) := by
  change requestNumbers (fieldWords (rowSection .terms (levelRow D ℓ),
    joinWords (joinWords (y, bin (D.lv ℓ).termKeys, key), bin ((D.lv ℓ).termArity + 1), c))) = _
  rw [requestNumbers_rowField, bval_joinWords, bval_joinWords, bval_bin, bval_bin]

def energyRequest (p : BaseRow × NumberWord × NumberWord) : P1Batch.Req :=
  fieldWords (rowSection .energy p.1, joinWords (p.2.1, [false, true], p.2.2))

@[fun_prop] theorem energyRequest_poly : Poly energyRequest := by unfold energyRequest; fun_prop

theorem energyRequest_value (D : Dims) (ℓ : ℕ) (y c : NumberWord) :
    requestNumbers (energyRequest (levelRow D ℓ, y, c)) =
      requestNumbers (fieldReq D (secLev ℓ .energy) (P1Batch.bval y * 2 + P1Batch.bval c)) := by
  unfold energyRequest
  rw [requestNumbers_rowField, bval_joinWords]
  rfl

def motifColourRequest (p : BaseRow × NumberWord) : P1Batch.Req :=
  fieldWords (rowSection .colour p.1, p.2)

@[fun_prop] theorem motifColourRequest_poly : Poly motifColourRequest := by unfold motifColourRequest; fun_prop

theorem cacheRead_field' (D : Dims) (u : List Bool) (s i : ℕ) (qs : List P1Batch.Req)
    (q : P1Batch.Req) (hq : ∃ r ∈ qs, requestNumbers q = requestNumbers r)
    (he : requestNumbers q = requestNumbers (fieldReq D s i)) :
    P1Batch.bval (cacheRead (qs.map (fun r => (r, P1Batch.fetch u r)), q)) = readField D u s i := by
  rw [cacheRead_fetch _ _ _ hq, fetch_of_requestNumbers _ he, bval_bitsVal, ← readField_eq]

/-- Check a mask bit using the public table of colour positions. Invalid stored colours select zero. -/
def maskBit (p : MotifRow × NumberWord × NumberWord) : Bool :=
  let col := boundWord (p.1.2.1, p.2.2)
  let power := selectRow ([true] : NumberWord) (col, p.1.2.2.2.2.2.2.1)
  let shifted := (Carry.nat_div (p.2.1, power)).1
  numberEq ((Carry.nat_div (shifted, [false, true])).2, [true])

@[fun_prop] theorem maskBit_poly : Poly maskBit := by
  have h := selectRow_poly ([true] : NumberWord)
  unfold maskBit
  dsimp only
  fun_prop

theorem maskBit_value (all : Bool) (D : Dims) (ℓ a g : ℕ) (w col : NumberWord)
    (c : ColorWord a) (hw : P1Batch.bval w = bwNum c) :
    maskBit (motifRow all D ℓ a g, w, col) =
      decide (c (finOr0 (2 * 2 ^ a + 1) (P1Batch.bval col)) = 1) := by
  let n := 2 * 2 ^ a + 1
  let b := finOr0 n (P1Batch.bval col)
  let v := boundWord (bin n, col)
  have hv : P1Batch.bval v = b.val := bval_boundWord n col
  have hsel : selectRow ([true] : NumberWord) (v, colourShiftTable n) = bin (2 ^ (n - 1 - b.val)) := by
    unfold colourShiftTable
    rw [selectRow_table, hv, ite_eq_left b.isLt]
  change numberEq ((Carry.nat_div
    ((Carry.nat_div (w, selectRow _ (v, colourShiftTable n))).1, [false, true])).2, [true]) = _
  rw [hsel, Bool.eq_iff_iff, numberEq_spec, decide_eq_true_eq]
  dsimp only
  rw [(bval_divide _ _).2, (bval_divide _ _).1, bval_bin, hw]
  change (bwNum c / 2 ^ (n - 1 - b.val)) % 2 = 1 ↔ c b = 1
  have H := bitWord_test_at c b
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq] at H
  exact H

end P1SolGreedy.SolDemand
