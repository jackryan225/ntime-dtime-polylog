import P1ChkFinal.C10Bits
import P1Batch.Defs
import OAI.Computability.IntegerMultiplication.Bits.Word
import Mathlib.Data.Nat.Log

/-! Numeric codes for C10. All finite axes are listed in increasing numerical order. -/

namespace P1ChkFinal.AstraC10

open OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open P1P7

/-- Minimal LSB-first word, including the empty word for zero. -/
def binary (n : ℕ) : Bits.Word := Bits.short (Nat.clog 2 (n + 1)) n

theorem value_binary (n : ℕ) : Bits.value (binary n) = n := by
  have h := Nat.le_pow_clog (b := 2) (by decide) (n + 1)
  exact (Bits.value_short _ _).trans (Nat.mod_eq_of_lt (by omega))

theorem bval_binary (n : ℕ) : P1Batch.bval (binary n) = n := by
  have eq (w : List Bool) : P1Batch.bval w = Bits.value w := by
    induction w with
    | nil => rfl
    | cons b w ih => cases b <;> simp only [P1Batch.bval, Bits.value, ih] <;> rfl
  exact (eq _).trans (value_binary n)

/-- This instance is scoped so importing a C10 proof does not select an encoding for other tasks. -/
scoped instance binaryCodec : Code.Codec ℕ := ⟨fun n => Code.send (binary n)⟩

/-- Address, displacement and far slot, respectively. -/
abbrev EndCode := ℕ × ℕ × ℕ

/-- Outgoing record, incoming record, and the widths of the outgoing slot by lane number. -/
abbrev SlotCode := EndCode × EndCode × List ℕ
abbrev PanelCode := List SlotCode

def laneList {G : ℕ} {T : Type} (f : BitWord G → T) : List T :=
  List.ofFn fun i : Fin (2 ^ G) => f ((bitWordFinEquiv G).symm i)

def codeSlot {a G : ℕ} (p : PanelT a G) (k : Fin (2 ^ a)) : SlotCode :=
  (((p.1 k).1, bwNum (p.1 k).2, p.2.1 k),
   ((p.2.2.1 k).1, bwNum (p.2.2.1 k).2, p.2.2.2.1 k),
   laneList (p.2.2.2.2 k))

def codePanel {a G : ℕ} (p : PanelT a G) : PanelCode := List.ofFn (codeSlot p)

/-- The term table has axes residual lane, port, and expander slot. -/
abbrev RefreshDatumCode := PanelCode × List (List (List ℕ))

def codeRefreshDatum {a g dH : ℕ} (d : RefreshDatum a g dH) : RefreshDatumCode :=
  (codePanel d.1, laneList fun l =>
    List.ofFn fun j : Fin (2 ^ a) => List.ofFn fun h : Fin dH => d.2 l (j, h))

/-- The shrink term table has axes old lane, outgoing slot, and term field. -/
abbrev ShrinkDatumCode := PanelCode × ℕ × ℕ × List (List (List ℕ))

def shrinkTermCode : Option ((Bool × Fin 4) → ℕ) → List ℕ
  | none => 0 :: List.replicate 8 0
  | some v => 1 :: ((List.ofFn fun j => v (false, j)) ++ (List.ofFn fun j => v (true, j)))

def codeShrinkDatum {a g : ℕ} (d : ShrinkDatum a g) : ShrinkDatumCode :=
  (codePanel d.1, d.2.1.val, bwNum d.2.2.1, laneList fun w : BitWord (packingLaneBits a g) =>
    let z := packingFields a g w
    List.ofFn fun i : Fin (2 ^ a) => shrinkTermCode (d.2.2.2 i z.2.2.1 z.2.2.2 z.1 z.2.1))

/-- In a true ball a repeated address is represented by the same value at each occurrence. -/
def ballList {T : Type} (nb : ℕ → List ℕ) (old : ℕ → Option T) (x r : ℕ) :
    List (ℕ × Option T) :=
  (bfs nb x r).map fun y => (y, old y)

/-- A bounded table read. Its polynomial program caps even a malformed binary index by the list length. -/
def readAt {T : Type} (d : T) (xs : List T) (i : ℕ) : T := xs[i]?.getD d

@[simp] theorem readAt_ofFn {T : Type} {n : ℕ} (d : T) (f : Fin n → T) (i : Fin n) :
    readAt d (List.ofFn f) i.val = f i := by
  simp [readAt, List.getElem?_ofFn, i.isLt]

@[simp] theorem readAt_laneList {T : Type} {g : ℕ} (d : T) (f : BitWord g → T) (l : BitWord g) :
    readAt d (laneList f) (bwNum l) = f l := by
  unfold laneList bwNum
  rw [readAt_ofFn, Equiv.symm_apply_apply]

@[simp] theorem length_laneList {T : Type} {g : ℕ} (f : BitWord g → T) :
    (laneList f).length = 2 ^ g := List.length_ofFn

@[simp] theorem readAt_panel {a G : ℕ} (p : PanelT a G) (k : Fin (2 ^ a)) :
    readAt default (codePanel p) k.val = codeSlot p k :=
  readAt_ofFn _ _ _

theorem codePanel_injective {a G : ℕ} : Function.Injective (@codePanel a G) := by
  intro p q h
  have row (k : Fin (2 ^ a)) : codeSlot p k = codeSlot q k := by
    simpa only [readAt_panel] using congrArg (fun xs => readAt default xs k.val) h
  have wn {v w : BitWord G} (e : bwNum v = bwNum w) : v = w :=
    (bitWordFinEquiv G).injective (Fin.ext e)
  refine Prod.ext (funext fun k => Prod.ext ?_ (wn ?_))
    (Prod.ext (funext fun k => ?_) (Prod.ext (funext fun k => Prod.ext ?_ (wn ?_))
      (Prod.ext (funext fun k => ?_) (funext fun k => funext fun l => ?_))))
  · exact congrArg (fun r : SlotCode => r.1.1) (row k)
  · exact congrArg (fun r : SlotCode => r.1.2.1) (row k)
  · exact congrArg (fun r : SlotCode => r.1.2.2) (row k)
  · exact congrArg (fun r : SlotCode => r.2.1.1) (row k)
  · exact congrArg (fun r : SlotCode => r.2.1.2.1) (row k)
  · exact congrArg (fun r : SlotCode => r.2.1.2.2) (row k)
  · have eq := congrArg (fun r : SlotCode => readAt 0 r.2.2 (bwNum l)) (row k)
    simpa only [codeSlot, readAt_laneList] using eq

end P1ChkFinal.AstraC10
