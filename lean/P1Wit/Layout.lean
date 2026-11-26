import Mathlib.Tactic.Ring

/-!
# P1Wit.Layout: the witness format of Lemma P (task P6 of research/g3/leanplan/PLAN.md)

Lane P1-lean-W2-P6 (brief ORG/briefs/P1-lean-W2-P6.md). Paper: research/papers/ntime-dtime-polylog.tex,
subsection `subsec:witness` (segments S0-S3, panels (P1)-(P4)), `rem:G1` (addresses), `lem:unique`, `lem:space`;
corrections of PLAN.md section 9 (C11 repaired, C14 added, OpenAI's lane-0 key, terms keyed at the wire's source base).

Mathlib-light on purpose (no OpenAI import): the checker lanes import this file.

## The format

A witness is a bit list `u` of length `m`. It consists of a FIXED PART of `fixedLen D` bits (`D : Dims` holds the sizes,
all computable from `n` and the fixed data), then the payload string `z`, then zeros up to `m`.

The fixed part is a sequence of SECTIONS `s = 0, 1, ..., D.nSec - 1`. Section `s` holds `D.count s` FIELDS of
`D.width s` bits each. Field `i` of section `s` starts at bit `D.off s + i * D.width s`
(`D.off s` = sum of `count * width` of the earlier sections). A field holds a natural number `< 2 ^ width`,
LEAST significant bit first (`natBits`, `bitsVal`). Every content is stored as a natural number; the typed
codes are below (`zigzag` for integers, `optCode` for `Option ℕ`, trits as `0, 1, 2`).

Sections (paper names in brackets):
* `0` trits [S0]: index `i * r + ρ`, small interval `i < I * N`, tape `ρ < r`; value `0, 1, 2` = the net lane's
  `Fin 3` value (block change `+ 1`); code `3` is invalid (check C1).
* `1` start blocks [S1]: index `ι * r + ρ`; value `zigzag β_ρ(ι N)`.
* `2`, `3` previous and next owners [S1]: index `(ι * r + ρ) * 3 + δ` (`δ = 0, 1, 2` for the big block
  `q_ρ(ι) + δ - 1`); value `optCode` of the owner (`0` = none).
* `4` guess-block owners [check C14, PLAN.md sec. 9, 09:42Z]: index `Q < nGB` (the big blocks of the input tape that
  CONTAIN a guess cell, `P1ChkDir.nGuessBlocks`, board 11:02:50Z); value `optCode` of the LEAST owner of `Q`.
* for each level `ℓ ≤ top` (paper `Λ = top`), twelve sections `secLev ℓ k = 5 + 12 ℓ + k.toNat` [S2]:
  `layout` (one bit, only if substep `ℓ` is shrinking), the base record (P1) `outAddr, outDisp, outFar, inAddr,
  inDisp, inFar` (index `y * slots + k`: base address `y`, slot `k`; `Disp` = lane displacement as a number
  `< 2 ^ laneW` (OpenAI `bitWordFinEquiv`), `Far` = slot number at the other end), the widths (P2) `width`
  (index `(y * lanes + l) * slots + k`, lane `l`), and for a shrinking substep (P3) `colour`, `offset` (index `y`),
  `energy` (index `y * 2 + c`, `c = 0`: `E_1`, `c = 1`: `E_2`), and the term slots `terms`
  (index `(y * termKeys + key) * (termArity + 1) + c`: `c = 0` presence flag `0` or `1`, `c = e + 1` the `e`-th number
  of the admitted outer index; keys follow OpenAI's keying at the wire's SOURCE base, e.g. `key = l * slots + k` for
  a shrinking substep, the remaining lane for a refresh; the integration fixes the key map).
* `5 + 12 (top + 1)`: `Omega` (P4): index `y < bases` of the final level, the prefix `Ω(y)`.
* `6 + 12 (top + 1)`: the λ-chain `j_0, ..., j_P` (PLAN.md sec. 1, task P9): index `j < chainLen`.
After the fixed part: `z` (bits of each final arc at its source position, order base, lane, out-slot; `Ω(y)` is the
offset of base `y` inside `z`), then zeros [S3].

Deviation from the paper, on purpose: the paper stores the panel of a base contiguously ("array of panels"); here each
kind of field of a level is one section ("structure of arrays"). Every field still sits at an offset computable from
`(n, level, address, index)`, which is all that `rem:G1`, the checks and the batched look-ups use.
The paper's trit code (`00 ↦ 0, 01 ↦ 1, 10 ↦ -1`) is replaced by the net lane's `Fin 3` value; immaterial.

## Contents
* `enc D m F z`: the witness of the field contents `F` (σ, ι, the chain and the true records) and the payload `z`.
* `readField D u s i`, and one reader per field family (`rdTrit`, ..., `rdChain`).
* `readField_enc`, `rdOutAddr_enc`, ... (`decode_enc`): readers return the stored values.
* `enc_injective`; `enc_dec` (every witness whose tail after the payload is zero is `enc` of its own fields);
  `enc_length` (the witness has length `m` when the content fits).
-/

namespace P1Wit

/-! ## Bits of one field (least significant bit first) -/

/-- The `w` low bits of `v`, least significant bit first. -/
def natBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, v => decide (v % 2 = 1) :: natBits w (v / 2)

/-- The number spelled by a bit list, least significant bit first. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsVal bs

@[simp] theorem natBits_length (w v : ℕ) : (natBits w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [natBits, ih]

theorem bitsVal_natBits (w v : ℕ) : bitsVal (natBits w v) = v % 2 ^ w := by
  induction w generalizing v with
  | zero => simp [natBits, bitsVal, Nat.mod_one]
  | succ w ih =>
    simp only [natBits, bitsVal, ih]
    rw [show 2 ^ (w + 1) = 2 * 2 ^ w by ring, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b bs ih =>
    simp only [bitsVal, List.length_cons]
    rw [Nat.pow_succ]
    split <;> omega

theorem natBits_bitsVal (l : List Bool) : natBits l.length (bitsVal l) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, natBits, bitsVal]
    have h2 : ((if b = true then 1 else 0) + 2 * bitsVal bs) / 2 = bitsVal bs := by
      split <;> omega
    have h1 : decide (((if b = true then 1 else 0) + 2 * bitsVal bs) % 2 = 1) = b := by
      cases b
      · simp
      · simp [Nat.add_mul_mod_self_left]
    rw [h1, h2, ih]

/-- The number in the `w` bits of `u` that start at bit `o`. -/
def readNat (u : List Bool) (o w : ℕ) : ℕ := bitsVal ((u.drop o).take w)

theorem readNat_append (pre mid post : List Bool) (w : ℕ) (hmid : mid.length = w) :
    readNat (pre ++ mid ++ post) pre.length w = bitsVal mid := by
  unfold readNat
  rw [List.append_assoc, List.drop_left, List.take_left' hmid]

theorem readNat_natBits (pre post : List Bool) (w v : ℕ) :
    readNat (pre ++ natBits w v ++ post) pre.length w = v % 2 ^ w := by
  rw [readNat_append pre _ post w (natBits_length w v), bitsVal_natBits]

theorem readNat_lt (u : List Bool) (o w : ℕ) : readNat u o w < 2 ^ w := by
  unfold readNat
  have h1 := bitsVal_lt ((u.drop o).take w)
  have h2 : ((u.drop o).take w).length ≤ w := by simp
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

/-! ## Concatenation of a sequence of bit lists -/

/-- `f 0 ++ f 1 ++ ... ++ f (n - 1)`. -/
def cat (f : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => cat f n ++ f n

theorem cat_split (f : ℕ → List Bool) {i n : ℕ} (h : i < n) :
    ∃ rest, cat f n = cat f i ++ f i ++ rest := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h' : i < n
    · obtain ⟨rest, hr⟩ := ih h'
      exact ⟨rest ++ f n, by rw [cat, hr]; simp [List.append_assoc]⟩
    · have hi : i = n := by omega
      subst hi
      exact ⟨[], by simp [cat]⟩

theorem cat_length_const (f : ℕ → List Bool) (w : ℕ) (hf : ∀ i, (f i).length = w) (n : ℕ) :
    (cat f n).length = n * w := by
  induction n with
  | zero => simp [cat]
  | succ n ih => rw [cat, List.length_append, ih, hf]; ring

theorem cat_congr (f g : ℕ → List Bool) (n : ℕ) (h : ∀ i < n, f i = g i) : cat f n = cat g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cat, cat, ih (fun i hi => h i (by omega)), h n (by omega)]

/-! ## Sections: `c` fields of `w` bits -/

/-- Field `i` of a section of width `w` with contents `val`. -/
def fieldAt (w : ℕ) (val : ℕ → ℕ) (i : ℕ) : List Bool := natBits w (val i)

/-- A section: `c` fields of `w` bits, field `i` holding `val i`. -/
def secBits (c w : ℕ) (val : ℕ → ℕ) : List Bool := cat (fieldAt w val) c

theorem secBits_length (c w : ℕ) (val : ℕ → ℕ) : (secBits c w val).length = c * w :=
  cat_length_const _ w (fun i => natBits_length w (val i)) c

/-- Offset of section `s`: the total size of the sections before it. -/
def offAt (count width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => offAt count width s + count s * width s

/-- Section `s` of a layout. -/
def secAt (count width : ℕ → ℕ) (val : ℕ → ℕ → ℕ) (s : ℕ) : List Bool :=
  secBits (count s) (width s) (val s)

/-- The first `n` sections of a layout. -/
def fixedCat (count width : ℕ → ℕ) (val : ℕ → ℕ → ℕ) (n : ℕ) : List Bool :=
  cat (secAt count width val) n

theorem fixedCat_length (count width : ℕ → ℕ) (val : ℕ → ℕ → ℕ) (n : ℕ) :
    (fixedCat count width val n).length = offAt count width n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold fixedCat at *
    rw [cat, List.length_append, ih, secAt, secBits_length, offAt]

/-- The generic decoding lemma: field `i` of section `s` is read back (modulo `2 ^ width`). -/
theorem read_fixedCat (count width : ℕ → ℕ) (val : ℕ → ℕ → ℕ) {n s i : ℕ} (hs : s < n)
    (hi : i < count s) (post : List Bool) :
    readNat (fixedCat count width val n ++ post) (offAt count width s + i * width s) (width s) =
      val s i % 2 ^ width s := by
  obtain ⟨rest, hr⟩ := cat_split (secAt count width val) hs
  obtain ⟨rest', hr'⟩ := cat_split (fieldAt (width s) (val s)) hi
  have hsec : secAt count width val s =
      cat (fieldAt (width s) (val s)) i ++ natBits (width s) (val s i) ++ rest' := hr'
  have hlen : (cat (secAt count width val) s ++ cat (fieldAt (width s) (val s)) i).length =
      offAt count width s + i * width s := by
    rw [List.length_append,
      cat_length_const (fieldAt (width s) (val s)) (width s) (fun j => natBits_length _ _) i]
    have := fixedCat_length count width val s
    unfold fixedCat at this
    rw [this]
  have heq : fixedCat count width val n ++ post =
      (cat (secAt count width val) s ++ cat (fieldAt (width s) (val s)) i) ++
        natBits (width s) (val s i) ++ (rest' ++ rest ++ post) := by
    unfold fixedCat
    rw [hr, hsec]
    simp only [List.append_assoc]
  rw [heq, ← hlen, readNat_natBits]

theorem fixedCat_congr (count width : ℕ → ℕ) (val val' : ℕ → ℕ → ℕ) (n : ℕ)
    (h : ∀ s < n, ∀ i < count s, val s i = val' s i) :
    fixedCat count width val n = fixedCat count width val' n := by
  unfold fixedCat
  apply cat_congr
  intro s hs
  unfold secAt secBits
  apply cat_congr
  intro i hi
  unfold fieldAt
  rw [h s hs i hi]

/-- Reading every field of a section back from `u` gives the bits of `u` there. -/
theorem cat_read (u : List Bool) (o w : ℕ) :
    ∀ c, o + c * w ≤ u.length →
      cat (fieldAt w (fun i => readNat u (o + i * w) w)) c = (u.drop o).take (c * w)
  | 0, _ => by simp [cat]
  | c + 1, h => by
    have hc : (c + 1) * w = c * w + w := by ring
    rw [hc] at h
    rw [cat, cat_read u o w c (by omega), fieldAt]
    have hl : ((u.drop (o + c * w)).take w).length = w := by
      simp only [List.length_take, List.length_drop]
      omega
    have hx := natBits_bitsVal ((u.drop (o + c * w)).take w)
    rw [hl] at hx
    rw [readNat, hx, hc, List.take_add, List.drop_drop]

/-- Reading every field of every section back from `u` gives the first `offAt n` bits of `u`. -/
theorem fixedCat_read (u : List Bool) (count width : ℕ → ℕ) :
    ∀ n, offAt count width n ≤ u.length →
      fixedCat count width (fun s i => readNat u (offAt count width s + i * width s) (width s)) n =
        u.take (offAt count width n)
  | 0, _ => by simp [fixedCat, cat, offAt]
  | n + 1, h => by
    have h1 : offAt count width n + count n * width n ≤ u.length := h
    have ih := fixedCat_read u count width n (by omega)
    unfold fixedCat at ih ⊢
    rw [cat, ih, secAt, secBits, cat_read u _ _ _ h1, offAt, List.take_add]

/-! ## Typed codes -/

/-- Integers as naturals: `k ↦ 2k`, `-(k+1) ↦ 2k+1` (used for the start blocks `β`). -/
def zigzag : ℤ → ℕ
  | Int.ofNat k => 2 * k
  | Int.negSucc k => 2 * k + 1

def unzigzag (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

theorem unzigzag_zigzag (z : ℤ) : unzigzag (zigzag z) = z := by
  cases z with
  | ofNat k =>
    have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    show (if 2 * k % 2 = 0 then Int.ofNat (2 * k / 2) else Int.negSucc (2 * k / 2)) = Int.ofNat k
    simp only [h1, h2, ↓reduceIte]
  | negSucc k =>
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    show (if (2 * k + 1) % 2 = 0 then Int.ofNat ((2 * k + 1) / 2) else Int.negSucc ((2 * k + 1) / 2)) =
      Int.negSucc k
    simp only [h1, h2, Nat.one_ne_zero, ↓reduceIte]

theorem zigzag_injective : Function.Injective zigzag := fun a b h => by
  rw [← unzigzag_zigzag a, ← unzigzag_zigzag b, h]

/-- `Option ℕ` as a natural: `none ↦ 0`, `some k ↦ k + 1` (owners). -/
def optCode : Option ℕ → ℕ
  | none => 0
  | some k => k + 1

def optDecode (n : ℕ) : Option ℕ := if n = 0 then none else some (n - 1)

theorem optDecode_optCode (o : Option ℕ) : optDecode (optCode o) = o := by
  cases o with
  | none => rfl
  | some k =>
    show (if k + 1 = 0 then none else some (k + 1 - 1)) = some k
    simp

theorem optCode_injective : Function.Injective optCode := fun a b h => by
  rw [← optDecode_optCode a, ← optDecode_optCode b, h]

/-! ## Sizes -/

/-- Sizes of level `ℓ` of the compression (an OpenAI `State a g` with addresses `X.baseIndex`). -/
structure LevelDims where
  /-- number of bases `|B_ℓ|`; addresses `0, ..., bases - 1` -/
  bases : ℕ
  /-- slots per base in each direction, `d_ℓ = 2 ^ a` -/
  slots : ℕ
  /-- bits of a slot number (far slot fields) -/
  slotW : ℕ
  /-- lanes per base, `2 ^ g` -/
  lanes : ℕ
  /-- bits of a lane displacement, `g` -/
  laneW : ℕ
  /-- substep `ℓ` (from level `ℓ` to `ℓ + 1`) is a shrinking substep; `false` for refresh and for the final level -/
  shrink : Bool
  /-- bits of a greedy colour (shrinking substeps) -/
  colW : ℕ
  /-- bits of a tag offset (shrinking substeps) -/
  tagW : ℕ
  /-- term slots per base (OpenAI keys at the wire's source base; `0` at the final level) -/
  termKeys : ℕ
  /-- numbers per term (an admitted outer index `S → ℕ` has `|S|` numbers) -/
  termArity : ℕ

/-- All sizes of the witness format at one input length (computable from `n` and the fixed data). -/
structure Dims where
  /-- number of tapes of the verifier -/
  r : ℕ
  /-- number of big intervals -/
  I : ℕ
  /-- small intervals per big interval (= lanes at level 0) -/
  N : ℕ
  /-- big blocks of the input tape that contain a guess cell (check C14; `P1ChkDir.nGuessBlocks`) -/
  nGB : ℕ
  /-- the final level `Λ`: levels `0, ..., top`, substeps `0, ..., top - 1` -/
  top : ℕ
  /-- the sizes of each level -/
  lv : ℕ → LevelDims
  /-- bits of the big numbers: addresses, directory entries, energy prefixes, `Ω` -/
  bigW : ℕ
  /-- bits of an arc width and of a number of a term -/
  wW : ℕ
  /-- number of entries `j_0, ..., j_P` of the λ-chain -/
  chainLen : ℕ
  /-- bits of one chain entry -/
  chainW : ℕ

/-- The twelve kinds of fields of one level. -/
inductive Mem where
  | layout | outAddr | outDisp | outFar | inAddr | inDisp | inFar | width | colour | offset | energy | terms
  deriving DecidableEq, Repr

def Mem.toNat : Mem → ℕ
  | .layout => 0
  | .outAddr => 1
  | .outDisp => 2
  | .outFar => 3
  | .inAddr => 4
  | .inDisp => 5
  | .inFar => 6
  | .width => 7
  | .colour => 8
  | .offset => 9
  | .energy => 10
  | .terms => 11

def Mem.ofCode : ℕ → Mem
  | 0 => .layout
  | 1 => .outAddr
  | 2 => .outDisp
  | 3 => .outFar
  | 4 => .inAddr
  | 5 => .inDisp
  | 6 => .inFar
  | 7 => .width
  | 8 => .colour
  | 9 => .offset
  | 10 => .energy
  | _ => .terms

theorem Mem.ofCode_toNat (k : Mem) : Mem.ofCode k.toNat = k := by cases k <;> rfl

theorem Mem.toNat_lt (k : Mem) : k.toNat < 12 := by cases k <;> decide

theorem Mem.toNat_ofNat (k : ℕ) (hk : k < 12) : (Mem.ofCode k).toNat = k := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | k + 12, h => omega

/-- What a section number holds. -/
inductive Kind where
  | trit | start | prevOwn | nextOwn | guess
  | lev (ℓ : ℕ) (k : Mem)
  | Omega | chain | unused

/-! ### Section numbers -/

def secTrit : ℕ := 0
def secStart : ℕ := 1
def secPrev : ℕ := 2
def secNext : ℕ := 3
def secGuess : ℕ := 4
/-- Section of the fields of kind `k` of level `ℓ`. -/
def secLev (ℓ : ℕ) (k : Mem) : ℕ := 5 + 12 * ℓ + k.toNat

namespace Dims

variable (D : Dims)

def secOmega : ℕ := 5 + 12 * (D.top + 1)
def secChain : ℕ := 6 + 12 * (D.top + 1)
/-- Number of sections of the fixed part. -/
def nSec : ℕ := 7 + 12 * (D.top + 1)

def kind (s : ℕ) : Kind :=
  if s = 0 then .trit
  else if s = 1 then .start
  else if s = 2 then .prevOwn
  else if s = 3 then .nextOwn
  else if s = 4 then .guess
  else if s < 5 + 12 * (D.top + 1) then .lev ((s - 5) / 12) (Mem.ofCode ((s - 5) % 12))
  else if s = 5 + 12 * (D.top + 1) then .Omega
  else if s = 6 + 12 * (D.top + 1) then .chain
  else .unused

end Dims

/-- Number of fields of kind `k` of a level. -/
def LevelDims.count (L : LevelDims) : Mem → ℕ
  | .layout => if L.shrink then 1 else 0
  | .outAddr | .outDisp | .outFar | .inAddr | .inDisp | .inFar => L.bases * L.slots
  | .width => L.bases * L.lanes * L.slots
  | .colour | .offset => if L.shrink then L.bases else 0
  | .energy => if L.shrink then L.bases * 2 else 0
  | .terms => L.bases * L.termKeys * (L.termArity + 1)

namespace Dims

variable (D : Dims)

/-- Width of a field of kind `k` of a level. -/
def levWidth (L : LevelDims) : Mem → ℕ
  | .layout => 1
  | .outAddr | .inAddr => D.bigW
  | .outDisp | .inDisp => L.laneW
  | .outFar | .inFar => L.slotW
  | .width => D.wW
  | .colour => L.colW
  | .offset => L.tagW
  | .energy => D.bigW
  | .terms => D.wW

/-- Number of fields of section `s`. -/
def count (s : ℕ) : ℕ :=
  match D.kind s with
  | .trit => D.I * D.N * D.r
  | .start => D.I * D.r
  | .prevOwn | .nextOwn => D.I * D.r * 3
  | .guess => D.nGB
  | .lev ℓ k => (D.lv ℓ).count k
  | .Omega => (D.lv D.top).bases
  | .chain => D.chainLen
  | .unused => 0

/-- Bits per field of section `s`. -/
def width (s : ℕ) : ℕ :=
  match D.kind s with
  | .trit => 2
  | .start | .prevOwn | .nextOwn | .guess | .Omega => D.bigW
  | .lev ℓ k => D.levWidth (D.lv ℓ) k
  | .chain => D.chainW
  | .unused => 0

/-- First bit of section `s`. -/
def off (s : ℕ) : ℕ := offAt D.count D.width s

/-- Length of the fixed part; the payload `z` starts here. -/
def fixedLen : ℕ := D.off D.nSec

end Dims

/-! ## Field contents -/

/-- The contents of all fields, as natural numbers (already coded: `zigzag`, `optCode`, `bitWordFinEquiv`, ...).
Indices outside the ranges of `Dims` are never stored. -/
structure Fields where
  /-- small interval `i`, tape `ρ` ↦ `0, 1, 2` (block change `+ 1`) -/
  trit : ℕ → ℕ → ℕ
  /-- big interval `ι`, tape `ρ` ↦ `zigzag β_ρ(ι N)` -/
  start : ℕ → ℕ → ℕ
  /-- `ι, ρ, δ` ↦ `optCode` of the previous owner of big block `q_ρ(ι) + δ - 1` -/
  prevOwn : ℕ → ℕ → ℕ → ℕ
  /-- `ι, ρ, δ` ↦ `optCode` of the next owner -/
  nextOwn : ℕ → ℕ → ℕ → ℕ
  /-- guess big block `Q` ↦ `optCode` of its least owner (check C14) -/
  guess : ℕ → ℕ
  /-- level `ℓ` ↦ layout bit (`0` = `false` = paper layout 1, `1` = `true`) -/
  layout : ℕ → ℕ
  /-- `ℓ, y, k` ↦ address of the head base of out-slot `k` of base `y` -/
  outAddr : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, k` ↦ lane displacement of out-slot `k` -/
  outDisp : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, k` ↦ in-slot number at the head of out-slot `k` -/
  outFar : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, k` ↦ address of the tail base of in-slot `k` -/
  inAddr : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, k` ↦ lane displacement of in-slot `k` -/
  inDisp : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, k` ↦ out-slot number at the tail of in-slot `k` -/
  inFar : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, l, k` ↦ width of the actual arc of out-slot `k` at position `(y, l)` -/
  width : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y` ↦ greedy colour -/
  colour : ℕ → ℕ → ℕ
  /-- `ℓ, y` ↦ tag offset (as a number, OpenAI `bitWordFinEquiv`) -/
  offset : ℕ → ℕ → ℕ
  /-- `ℓ, y, c` ↦ energy prefix `E_{c+1}(y)` -/
  energy : ℕ → ℕ → ℕ → ℕ
  /-- `ℓ, y, key, c` ↦ term slot: `c = 0` presence flag, `c = e + 1` number `e` of the admitted index -/
  terms : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- final base `y` ↦ `Ω(y)` -/
  Omega : ℕ → ℕ
  /-- `j` ↦ chain entry `j_j` -/
  chain : ℕ → ℕ

namespace Fields

variable (F : Fields)

/-- Contents of field `i` of the section of kind `k` of level `ℓ`. -/
def levVal (L : LevelDims) (ℓ : ℕ) : Mem → ℕ → ℕ
  | .layout, _ => F.layout ℓ
  | .outAddr, i => F.outAddr ℓ (i / L.slots) (i % L.slots)
  | .outDisp, i => F.outDisp ℓ (i / L.slots) (i % L.slots)
  | .outFar, i => F.outFar ℓ (i / L.slots) (i % L.slots)
  | .inAddr, i => F.inAddr ℓ (i / L.slots) (i % L.slots)
  | .inDisp, i => F.inDisp ℓ (i / L.slots) (i % L.slots)
  | .inFar, i => F.inFar ℓ (i / L.slots) (i % L.slots)
  | .width, i => F.width ℓ (i / L.slots / L.lanes) (i / L.slots % L.lanes) (i % L.slots)
  | .colour, i => F.colour ℓ i
  | .offset, i => F.offset ℓ i
  | .energy, i => F.energy ℓ (i / 2) (i % 2)
  | .terms, i => F.terms ℓ (i / (L.termArity + 1) / L.termKeys) (i / (L.termArity + 1) % L.termKeys)
      (i % (L.termArity + 1))

/-- Contents of field `i` of section `s`. -/
def val (D : Dims) (s i : ℕ) : ℕ :=
  match D.kind s with
  | .trit => F.trit (i / D.r) (i % D.r)
  | .start => F.start (i / D.r) (i % D.r)
  | .prevOwn => F.prevOwn (i / 3 / D.r) (i / 3 % D.r) (i % 3)
  | .nextOwn => F.nextOwn (i / 3 / D.r) (i / 3 % D.r) (i % 3)
  | .guess => F.guess i
  | .lev ℓ k => F.levVal (D.lv ℓ) ℓ k i
  | .Omega => F.Omega i
  | .chain => F.chain i
  | .unused => 0

/-- Every stored content fits into its field. -/
def InRange (D : Dims) : Prop := ∀ s < D.nSec, ∀ i < D.count s, F.val D s i < 2 ^ D.width s

/-- Two field contents agree on every stored field. -/
def Agree (D : Dims) (F' : Fields) : Prop := ∀ s < D.nSec, ∀ i < D.count s, F.val D s i = F'.val D s i

end Fields

/-! ## The encoder -/

/-- The fixed part of the witness. -/
def fixedBits (D : Dims) (F : Fields) : List Bool := fixedCat D.count D.width (F.val D) D.nSec

/-- **P6 encoder.** The witness of the field contents `F` (σ in the trits, ι in the term slots, the λ-chain, and the
true records: directory, panels, colours, offsets, energy prefixes, layout bits, `Ω`) and the payload `z`:
the fixed part, then `z`, then zeros up to length `m`. -/
def enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) : List Bool :=
  fixedBits D F ++ z ++ List.replicate (m - (D.fixedLen + z.length)) false

/-- The same witness as a function `Fin m → Bool` (the form of `P1Int.LemmaP`). -/
def encFn (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) : Fin m → Bool :=
  fun i => (enc D m F z).getD i false

/-! ## Readers (the checker lanes use these) -/

/-- Field `i` of section `s` of the bit list `u`. -/
def readField (D : Dims) (u : List Bool) (s i : ℕ) : ℕ := readNat u (D.off s + i * D.width s) (D.width s)

def rdTrit (D : Dims) (u : List Bool) (i ρ : ℕ) : ℕ := readField D u secTrit (i * D.r + ρ)
def rdStart (D : Dims) (u : List Bool) (ι ρ : ℕ) : ℕ := readField D u secStart (ι * D.r + ρ)
def rdPrev (D : Dims) (u : List Bool) (ι ρ δ : ℕ) : ℕ := readField D u secPrev ((ι * D.r + ρ) * 3 + δ)
def rdNext (D : Dims) (u : List Bool) (ι ρ δ : ℕ) : ℕ := readField D u secNext ((ι * D.r + ρ) * 3 + δ)
def rdGuess (D : Dims) (u : List Bool) (Q : ℕ) : ℕ := readField D u secGuess Q
def rdLayout (D : Dims) (u : List Bool) (ℓ : ℕ) : ℕ := readField D u (secLev ℓ .layout) 0
def rdOutAddr (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .outAddr) (y * (D.lv ℓ).slots + k)
def rdOutDisp (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .outDisp) (y * (D.lv ℓ).slots + k)
def rdOutFar (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .outFar) (y * (D.lv ℓ).slots + k)
def rdInAddr (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .inAddr) (y * (D.lv ℓ).slots + k)
def rdInDisp (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .inDisp) (y * (D.lv ℓ).slots + k)
def rdInFar (D : Dims) (u : List Bool) (ℓ y k : ℕ) : ℕ :=
  readField D u (secLev ℓ .inFar) (y * (D.lv ℓ).slots + k)
def rdWidth (D : Dims) (u : List Bool) (ℓ y l k : ℕ) : ℕ :=
  readField D u (secLev ℓ .width) ((y * (D.lv ℓ).lanes + l) * (D.lv ℓ).slots + k)
def rdColour (D : Dims) (u : List Bool) (ℓ y : ℕ) : ℕ := readField D u (secLev ℓ .colour) y
def rdOffset (D : Dims) (u : List Bool) (ℓ y : ℕ) : ℕ := readField D u (secLev ℓ .offset) y
def rdEnergy (D : Dims) (u : List Bool) (ℓ y c : ℕ) : ℕ := readField D u (secLev ℓ .energy) (y * 2 + c)
def rdTerms (D : Dims) (u : List Bool) (ℓ y key c : ℕ) : ℕ :=
  readField D u (secLev ℓ .terms) ((y * (D.lv ℓ).termKeys + key) * ((D.lv ℓ).termArity + 1) + c)
def rdOmega (D : Dims) (u : List Bool) (y : ℕ) : ℕ := readField D u D.secOmega y
def rdChain (D : Dims) (u : List Bool) (j : ℕ) : ℕ := readField D u D.secChain j
/-- The payload part of `u` (with the zero tail): it starts at bit `D.fixedLen`. -/
def rdPayload (D : Dims) (u : List Bool) : List Bool := u.drop D.fixedLen

/-- The field contents that a bit list spells (used for uniqueness: a passing witness is `enc` of these). -/
def dec (D : Dims) (u : List Bool) : Fields where
  trit i ρ := rdTrit D u i ρ
  start ι ρ := rdStart D u ι ρ
  prevOwn ι ρ δ := rdPrev D u ι ρ δ
  nextOwn ι ρ δ := rdNext D u ι ρ δ
  guess Q := rdGuess D u Q
  layout ℓ := rdLayout D u ℓ
  outAddr ℓ y k := rdOutAddr D u ℓ y k
  outDisp ℓ y k := rdOutDisp D u ℓ y k
  outFar ℓ y k := rdOutFar D u ℓ y k
  inAddr ℓ y k := rdInAddr D u ℓ y k
  inDisp ℓ y k := rdInDisp D u ℓ y k
  inFar ℓ y k := rdInFar D u ℓ y k
  width ℓ y l k := rdWidth D u ℓ y l k
  colour ℓ y := rdColour D u ℓ y
  offset ℓ y := rdOffset D u ℓ y
  energy ℓ y c := rdEnergy D u ℓ y c
  terms ℓ y key c := rdTerms D u ℓ y key c
  Omega y := rdOmega D u y
  chain j := rdChain D u j

end P1Wit
