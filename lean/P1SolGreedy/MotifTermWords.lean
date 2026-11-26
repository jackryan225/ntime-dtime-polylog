import P1SolGreedy.MotifGeometry

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

def squareWord (x : NumberWord) : NumberWord := Carry.times0 (x, x)

@[fun_prop] theorem squareWord_poly : Poly squareWord := by unfold squareWord; fun_prop

theorem squareWord_value (x : NumberWord) : P1Batch.bval (squareWord x) = P1Batch.bval x ^ 2 := by
  rw [squareWord, bval_mul, pow_two]

def weightedSquare (p : NumberWord × NumberWord) : NumberWord :=
  Carry.times0 (p.1, squareWord p.2)

@[fun_prop] theorem weightedSquare_poly : Poly weightedSquare := by unfold weightedSquare; fun_prop

theorem weightedSquare_value (s x : NumberWord) :
    P1Batch.bval (weightedSquare (s, x)) = P1Batch.bval s * P1Batch.bval x ^ 2 := by
  rw [weightedSquare, bval_mul, squareWord_value]

def copiesWords (L : ℕ) (v : NumberWord × NumberWord) : NumberWord :=
  let weight := MotifAdmission.weight demandMass
  let den := MotifAdmission.denominator demandMass
  ceilRootWords (Bits.add (weightedSquare (bin (weight false), v.1), weightedSquare (bin (weight true), v.2)),
    bin (L ^ 2 * den))

@[fun_prop] theorem copiesWords_poly (L : ℕ) : Poly (copiesWords L) := by
  unfold copiesWords
  dsimp only
  fun_prop

theorem copiesWords_value (L : ℕ) (v : NumberWord × NumberWord) (w : Bool → ℕ)
    (h : (P1Batch.bval v.1, P1Batch.bval v.2) = (w false, w true)) :
    P1Batch.bval (copiesWords L v) = MotifAdmission.copies demandMass w L := by
  have hfalse : P1Batch.bval v.1 = w false := congrArg Prod.fst h
  have htrue : P1Batch.bval v.2 = w true := congrArg Prod.snd h
  unfold copiesWords MotifAdmission.copies MotifAdmission.energy
  dsimp only
  rw [bval_ceilRootWords, bval_add, weightedSquare_value, weightedSquare_value, bval_bin, bval_bin, bval_bin,
    hfalse, htrue, Fintype.sum_bool]
  rw [Nat.add_comm]

def termIndexWord (p : Bool × NumberWord) : NumberWord :=
  Bits.add ([true], Bits.add ((bif p.1 then [false, false, true] else []), p.2))

@[fun_prop] theorem termIndexWord_poly : Poly termIndexWord := by unfold termIndexWord; fun_prop

theorem termIndexWord_value (l : Bool) (j : NumberWord) :
    P1Batch.bval (termIndexWord (l, j)) = 1 + (if l then 4 else 0) + P1Batch.bval j := by
  unfold termIndexWord
  rw [bval_add, bval_add]
  cases l <;> change 1 + (_ + P1Batch.bval j) = 1 + _ + P1Batch.bval j <;> rw [Nat.add_assoc] <;> rfl

def termValueWord (p : (MotifFields × WireWords) × NumberWord) : NumberWord :=
  cacheRead (p.1.1.2, leafTermAt ((p.1.1.1, p.1.2), p.2))

@[fun_prop] theorem termValueWord_poly : Poly termValueWord := by unfold termValueWord; fun_prop

def termWeightTable (l : Bool) : List (NumberWord × NumberWord) :=
  (List.range 4).map fun j => (bin j, bin (MotifAdmission.weight supplyMass (l, finOr0 4 j)))

def layoutWeightTable : List (NumberWord × NumberWord) :=
  (List.range 4).map fun j => (bin j, bin (P1P7.layoutCoeff (finOr0 4 j)))

def weightedTerm (l : Bool) (p : (MotifFields × WireWords) × NumberWord) : NumberWord :=
  weightedSquare (selectRow [] (p.2, termWeightTable l), termValueWord (p.1, termIndexWord (l, p.2)))

@[fun_prop] theorem weightedTerm_poly (l : Bool) : Poly (weightedTerm l) := by
  have hs := selectRow_poly ([] : NumberWord)
  unfold weightedTerm
  fun_prop

def emptyTermPair : MotifFields × WireWords := (emptyMotifFields, emptyWireWords)

def termGroup (l : Bool) (p : MotifFields × WireWords) : NumberWord :=
  sumWords (Code.polyPush (weightedTerm l) (p, wordRange (tally 4)))

@[fun_prop] theorem termGroup_poly (l : Bool) : Poly (termGroup l) := by
  have hm := Poly.push emptyTermPair ([] : NumberWord) (weightedTerm_poly l)
  unfold termGroup
  fun_prop

def nonzeroTerm (p : (MotifFields × WireWords) × NumberWord) : Bool :=
  !numberEq (termValueWord p, [])

@[fun_prop] theorem nonzeroTerm_poly : Poly nonzeroTerm := by unfold nonzeroTerm; fun_prop

def zeroTerm (p : MotifFields × WireWords) : Bool :=
  !hasTrue (Code.polyPush nonzeroTerm (p, wordRange (tally 9)))

@[fun_prop] theorem zeroTerm_poly : Poly zeroTerm := by
  have h := Poly.push emptyTermPair ([] : NumberWord) nonzeroTerm_poly
  unfold zeroTerm
  fun_prop

def validTermWords (L radNum radDen : ℕ) (p : MotifFields × WireWords) : Bool :=
  let copies := copiesWords L (wordDemand p)
  let energy := Bits.add (termGroup false p, termGroup true p)
  let used := Carry.times0 (energy, bin (radDen ^ 2))
  let cap := weightedSquare (bin (MotifAdmission.denominator supplyMass),
    Carry.times0 (copies, bin (L * radNum)))
  bitAnd (numberEq (termValueWord (p, []), [true]), !Carry.lt_ (cap, used))

@[fun_prop] theorem validTermWords_poly (L radNum radDen : ℕ) : Poly (validTermWords L radNum radDen) := by
  unfold validTermWords
  dsimp only
  fun_prop

def decideTermWords (L radNum radDen : ℕ) (s : MotifFields) : Bool :=
  let q := fieldContext s
  let p := (s, indexedWire q)
  bif q.1.2.1 then (bif wordMotif p then validTermWords L radNum radDen p else zeroTerm p) else true

theorem decideTermWords_poly (L radNum radDen : ℕ) : Poly (decideTermWords L radNum radDen) := by
  unfold decideTermWords
  dsimp only
  fun_prop

def energyTerm (l : Bool) (p : ((MotifFields × WireWords) × NumberWord) × NumberWord) : NumberWord :=
  let j := p.2
  let scale := selectRow [] (j, layoutWeightTable)
  let v := termValueWord (p.1.1, termIndexWord (l, j))
  weightedSquare (scale, Bits.add (v, p.1.2))

@[fun_prop] theorem energyTerm_poly (l : Bool) : Poly (energyTerm l) := by
  have hs := selectRow_poly ([] : NumberWord)
  unfold energyTerm
  dsimp only
  fun_prop

def wireEnergy (L selector : ℕ) (l : Bool) (p : MotifFields × WireWords) : NumberWord :=
  bif bitAnd (wordMotif p, numberEq (termValueWord (p, []), [true])) then
    let overhead := Carry.times0 (copiesWords L (wordDemand p), bin selector)
    sumWords (Code.polyPush (energyTerm l) ((p, overhead), wordRange (tally 4)))
  else []

@[fun_prop] theorem wireEnergy_poly (L selector : ℕ) (l : Bool) : Poly (wireEnergy L selector l) := by
  have h := Poly.push (emptyTermPair, ([] : NumberWord)) ([] : NumberWord) (energyTerm_poly l)
  unfold wireEnergy
  dsimp only
  fun_prop

def sumRootEnergy (L selector : ℕ) (l : Bool) (s : MotifFields) : NumberWord :=
  sumWords (Code.polyPush (wireEnergy L selector l) (s, arcRoots true (fieldContext s)))

@[fun_prop] theorem sumRootEnergy_poly (L selector : ℕ) (l : Bool) : Poly (sumRootEnergy L selector l) := by
  have h := Poly.push emptyMotifFields emptyWireWords (wireEnergy_poly L selector l)
  unfold sumRootEnergy
  fun_prop

def energyIndex (l : Bool) : NumberWord := if l then [] else [true]

def energyWord (l : Bool) (p : MotifFields × NumberWord) : NumberWord :=
  cacheRead (p.1.2, energyRequest (motifLevel (fieldContext p.1), p.2, energyIndex l))

@[fun_prop] theorem energyWord_poly (l : Bool) : Poly (energyWord l) := by unfold energyWord; fun_prop

def groupRecurrence (L selector : ℕ) (l : Bool) (s : MotifFields) : Bool :=
  let Y := motifRoot (fieldContext s)
  let prev := bif numberEq (Y, []) then [] else energyWord l (s, prevAddress Y)
  numberEq (energyWord l (s, Y), Bits.add (prev, sumRootEnergy L selector l s))

@[fun_prop] theorem groupRecurrence_poly (L selector : ℕ) (l : Bool) : Poly (groupRecurrence L selector l) := by
  unfold groupRecurrence
  dsimp only
  fun_prop

def decideEnergyWords (L selector : ℕ) (s : MotifFields) : Bool :=
  bif (fieldContext s).1.2.1 then bitAnd (groupRecurrence L selector false s, groupRecurrence L selector true s) else true

theorem decideEnergyWords_poly (L selector : ℕ) : Poly (decideEnergyWords L selector) := by
  unfold decideEnergyWords
  fun_prop

end P1SolGreedy.SolDemand
