import P1SolGreedy.C6Words
import P1SolGreedy.DemandWidthCore

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev WireWords := NumberWord × NumberWord × NumberWord
abbrev LaneWords := NumberWord × NumberWord × NumberWord × NumberWord
abbrev WireRadices := NumberWord × NumberWord × NumberWord × NumberWord × NumberWord

def wireRadices (a g : ℕ) : WireRadices :=
  (bin (2 ^ a), bin (2 ^ (2 * 2 ^ a + 1)), bin (2 ^ packingTagBits (2 ^ a)),
    bin (2 ^ g), bin (2 ^ packingLaneBits a g))

def wireNumbers (w : WireWords) : ℕ × ℕ × ℕ :=
  (P1Batch.bval w.1, P1Batch.bval w.2.1, P1Batch.bval w.2.2)

def codeWire {a g : ℕ} (e : Wire ℕ a g) : WireWords :=
  let p := (packingArcEquiv ℕ a g).symm e
  (bin p.1.1, bin p.1.2, bin (bwNum p.2))

def MatchesWire {a g : ℕ} (w : WireWords) (e : Wire ℕ a g) : Prop :=
  wireNumbers w = wireNumbers (codeWire e)

theorem matchesWire_parts {a g : ℕ} (w : WireWords) (e : Wire ℕ a g) :
    MatchesWire w e ↔ P1Batch.bval w.1 = e.1.1.1 ∧ P1Batch.bval w.2.1 = e.1.2.val ∧
      P1Batch.bval w.2.2 = bwNum ((packingArcEquiv ℕ a g).symm e).2 := by
  simp only [MatchesWire, wireNumbers, codeWire, bval_bin, Prod.mk.injEq]
  rfl

def joinWords (p : NumberWord × NumberWord × NumberWord) : NumberWord :=
  Bits.add (Carry.times0 (p.1, p.2.1), p.2.2)

@[fun_prop] theorem joinWords_poly : Poly joinWords := by unfold joinWords; fun_prop

theorem bval_joinWords (x r y : NumberWord) :
    P1Batch.bval (joinWords (x, r, y)) = P1Batch.bval x * P1Batch.bval r + P1Batch.bval y := by
  rw [joinWords, bval_add, bval_mul]

def joinLane (p : WireRadices × LaneWords) : NumberWord :=
  let (s, _, t, r, _) := p.1
  let (mask, label, tag, lane) := p.2
  joinWords (joinWords (joinWords (mask, s, label), t, tag), r, lane)

@[fun_prop] theorem joinLane_poly : Poly joinLane := by unfold joinLane; dsimp only; fun_prop

def splitLane (p : WireRadices × NumberWord) : LaneWords :=
  let (s, _, t, r, _) := p.1
  let x := Carry.nat_div (p.2, r)
  let y := Carry.nat_div (x.1, t)
  let z := Carry.nat_div (y.1, s)
  (z.1, z.2, y.2, x.2)

@[fun_prop] theorem splitLane_poly : Poly splitLane := by unfold splitLane; dsimp only; fun_prop

def laneNumbers (w : LaneWords) : ℕ × ℕ × ℕ × ℕ :=
  (P1Batch.bval w.1, P1Batch.bval w.2.1, P1Batch.bval w.2.2.1, P1Batch.bval w.2.2.2)

theorem packedLane_sum {a g : ℕ} (w : BitWord (packingLaneBits a g)) :
    bwNum w = (((bwNum (packingFields a g w).1 * 2 ^ a + bwNum (packingFields a g w).2.1) *
      2 ^ packingTagBits (2 ^ a) + bwNum (packingFields a g w).2.2.1) * 2 ^ g +
      bwNum (packingFields a g w).2.2.2) := by
  rw [show bwNum w = (bitWordFinEquiv _ w).val from rfl, packingFields_number, pow_add 2 (packingTagBits (2 ^ a)) g]
  unfold bwNum
  ring

theorem div_joinPow {d x y : ℕ} (hy : y < 2 ^ d) : (x * 2 ^ d + y) / 2 ^ d = x := by
  rw [Nat.mul_comm x, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hy, Nat.add_zero]

set_option maxHeartbeats 600000 in
theorem splitLane_code {a g : ℕ} (v : NumberWord) (w : BitWord (packingLaneBits a g))
    (hv : P1Batch.bval v = bwNum w) :
    laneNumbers (splitLane (wireRadices a g, v)) =
      (bwNum (packingFields a g w).1, bwNum (packingFields a g w).2.1,
        bwNum (packingFields a g w).2.2.1, bwNum (packingFields a g w).2.2.2) := by
  have hr : bwNum (packingFields a g w).2.2.2 < 2 ^ g := (bitWordFinEquiv g _).isLt
  have ht : bwNum (packingFields a g w).2.2.1 < 2 ^ packingTagBits (2 ^ a) := (bitWordFinEquiv _ _).isLt
  have hs : bwNum (packingFields a g w).2.1 < 2 ^ a := (bitWordFinEquiv a _).isLt
  simp only [splitLane, laneNumbers, wireRadices, (bval_divide _ _).1, (bval_divide _ _).2,
    bval_bin, hv, packedLane_sum w, div_joinPow hr, div_joinPow ht, div_joinPow hs,
    Nat.mul_add_mod_of_lt hr, Nat.mul_add_mod_of_lt ht, Nat.mul_add_mod_of_lt hs]

theorem joinLane_code {a g : ℕ} (v : LaneWords) (w : BitWord (packingLaneBits a g))
    (hv : laneNumbers v = (bwNum (packingFields a g w).1, bwNum (packingFields a g w).2.1,
        bwNum (packingFields a g w).2.2.1, bwNum (packingFields a g w).2.2.2)) :
    P1Batch.bval (joinLane (wireRadices a g, v)) = bwNum w := by
  simp only [laneNumbers, Prod.mk.injEq] at hv
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hv
  simp only [joinLane, wireRadices, bval_joinWords, bval_bin, h₁, h₂, h₃, h₄, packedLane_sum w]

/-- One address, far slot and lane displacement supplied by the requested slot fields. -/
def shiftedWire (p : WireRadices × WireWords × NumberWord × NumberWord × NumberWord) : WireWords :=
  (p.2.2.1, boundWord (p.1.1, p.2.2.2.1), xorWords (p.2.1.2.2, boundWord (p.1.2.2.2.2, p.2.2.2.2)))

@[fun_prop] theorem shiftedWire_poly : Poly shiftedWire := by unfold shiftedWire; fun_prop

theorem shiftedWire_code {a g : ℕ} (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e)
    (Z j δ : NumberWord) :
    MatchesWire (shiftedWire (wireRadices a g, w, Z, j, δ))
      (packingArcEquiv ℕ a g ((P1Batch.bval Z, finOr0 _ (P1Batch.bval j)),
        ((packingArcEquiv ℕ a g).symm e).2 + bwOf _ (P1Batch.bval δ))) := by
  have h := ((matchesWire_parts w e).mp hw).2.2
  have hδ : (bitWordFinEquiv (packingLaneBits a g) (bwOf _ (P1Batch.bval δ))).val =
      (finOr0 (2 ^ packingLaneBits a g) (P1Batch.bval δ)).val := by
    unfold bwOf
    exact congrArg Fin.val (Equiv.apply_symm_apply _ _)
  unfold MatchesWire wireNumbers codeWire
  rw [Equiv.symm_apply_apply]
  dsimp only [shiftedWire, wireRadices]
  rw [bval_bin, bval_boundWord, bval_bin, bval_xorWords, bval_boundWord, h, bval_bin]
  change _ = (_, _, (bitWordFinEquiv _ (_ + _)).val)
  rw [bitWord_code_add, hδ]
  rfl

/-- Lexicographic bundle rank key in the coordinate order of the stored checks. -/
def wireRankKey (p : WireRadices × WireWords) : NumberWord :=
  let (s, c, t, _, _) := p.1
  let (mask, label, tag, _) := splitLane (p.1, p.2.2.2)
  joinWords (joinWords (joinWords (joinWords (p.2.1, t, tag), s, p.2.2.1), c, mask), s, label)

@[fun_prop] theorem wireRankKey_poly : Poly wireRankKey := by unfold wireRankKey; dsimp only; fun_prop

set_option maxHeartbeats 600000 in
theorem wireRankKey_code {a g : ℕ} (w : WireWords) (e : Wire ℕ a g) (hw : MatchesWire w e) :
    P1Batch.bval (wireRankKey (wireRadices a g, w)) = sKey e := by
  obtain ⟨hb, hk, hl⟩ := (matchesWire_parts w e).mp hw
  let v := ((packingArcEquiv ℕ a g).symm e).2
  have he : packingFields a g v = (e.2.1, e.2.2, e.1.1.2) :=
    (packingFields a g).apply_symm_apply _
  have hs := splitLane_code w.2.2 v hl
  rw [he] at hs
  simp only [laneNumbers, Prod.mk.injEq] at hs
  obtain ⟨hm, hlabel, htag, _⟩ := hs
  let f := splitLane (wireRadices a g, w.2.2)
  change P1Batch.bval
    (joinWords (joinWords (joinWords (joinWords (w.1, bin (2 ^ packingTagBits (2 ^ a)), f.2.2.1),
      bin (2 ^ a), w.2.1), bin (2 ^ (2 * 2 ^ a + 1)), f.1), bin (2 ^ a), f.2.1)) = _
  simp only [bval_joinWords, bval_bin, hb, hk, f, hm, hlabel, htag, sKey]

/-- The greedy colour indexes the mask from its most significant end. -/
theorem bitWord_test_at {c : ℕ} (u : BitWord c) (j : Fin c) :
    (bitWordFinEquiv c u).val.testBit (c - 1 - j.val) = decide (u j = 1) := by
  induction c with
  | zero => exact j.elim0
  | succ n ih =>
    rw [bitWordFinEquiv_val, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bitWordFinEquiv n (Fin.tail u)).isLt]
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, lt_self_iff_false, ite_false, Nat.sub_self]
      generalize u 0 = b
      decide +revert
    | succ j =>
      have h : n - (j.val + 1) < n := by have := j.isLt; omega
      rw [Fin.val_succ, Nat.add_sub_cancel, ite_eq_left h, show n - (j.val + 1) = n - 1 - j.val by omega, ih]
      rfl

end P1SolGreedy.SolDemand
