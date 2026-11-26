import P1SolGreedy.C5Words
import P1SolGreedy.PackedWords

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev TagRadices := NumberWord × NumberWord × NumberWord
abbrev TagRow := TagRadices × Tally × Tally
abbrev TagFormat := PublicFmt × List (NumberWord × TagRow)
abbrev TagContext := C5Context × TagRow

/-- Lane range, residual-lane radix, and tag range, plus public enumeration limits. -/
def tagRow (a g : ℕ) : TagRow :=
  ((bin (2 ^ packingLaneBits a g), bin (2 ^ g), bin (2 ^ packingTagBits (2 ^ a))),
    tally (2 ^ a), tally (2 ^ packingTagBits (2 ^ a)))

def defaultTagRow : TagRow := (([], [], []), [], [])

def tagFormat (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) : TagFormat :=
  (fmtGreedy D M, (List.range (D.top + 1)).map fun ℓ => (bin ℓ, tagRow (ag ℓ).1 (ag ℓ).2))

def FmtHypTags (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ) : Prop :=
  Poly (fun n : NumberWord => tagFormat (dims (P1Batch.bval n)) (M (P1Batch.bval n)) (ag (P1Batch.bval n)))

def setupTag (p : TagFormat × NumberWord) : TagContext :=
  let level := (Carry.nat_div (p.2, p.1.1.1)).2
  (setupC5 (p.1.1, p.2), selectRow defaultTagRow (level, p.1.2))

theorem setupTag_poly : Poly setupTag := by
  have h₁ := setupC5_poly
  have h₂ := selectRow_poly defaultTagRow
  unfold setupTag
  dsimp only
  fun_prop

def setupC6 (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ) (z : IndexWord) : TagContext :=
  setupTag (tagFormat (dims (P1Batch.bval z.1)) (M (P1Batch.bval z.1)) (ag (P1Batch.bval z.1)), z.2)

theorem setupC6_poly (dims : ℕ → Dims) (M : ℕ → ℕ) (ag : ℕ → ℕ → ℕ × ℕ) (hf : FmtHypTags dims M ag) :
    Poly (setupC6 dims M ag) := (Poly.onleft hf).compose setupTag_poly

theorem setupTag_length (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    P1Batch.bval (setupTag (tagFormat D M ag, i)).1.1 = M := bval_bin _

theorem setupTag_spec (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord) :
    let p := setupTag (tagFormat D M ag, i)
    let ℓ := P1Batch.bval i % 2 ^ levBits D
    (p.1.2.1 = true ↔ ShrinkIdx D (P1Batch.bval i)) ∧
    P1Batch.bval p.1.2.2.1 = P1Batch.bval i / 2 ^ levBits D ∧
    (ℓ ≤ D.top → p.1.2.2.2 = levelRow D ℓ ∧ p.2 = tagRow (ag ℓ).1 (ag ℓ).2) := by
  obtain ⟨h₀, h₁, h₂⟩ := setupBase_spec D M i
  refine ⟨h₀, h₁, fun h => ⟨?_, ?_⟩⟩
  · change (setupBase (fmtGreedy D M, i)).2.2 = _
    exact h₂.trans (ite_eq_left h)
  · change selectRow defaultTagRow ((Carry.nat_div (i, bin (2 ^ levBits D))).2,
      (List.range (D.top + 1)).map (fun ℓ => (bin ℓ, tagRow (ag ℓ).1 (ag ℓ).2))) = _
    rw [selectRow_table, (bval_divide _ _).2, bval_bin, ite_eq_left (Nat.lt_succ_of_le h)]

theorem setupTag_inRange (D : Dims) (M : ℕ) (ag : ℕ → ℕ × ℕ) (i : NumberWord)
    (h : ShrinkIdx D (P1Batch.bval i)) :
    let ℓ := P1Batch.bval i % 2 ^ levBits D
    let q := setupTag (tagFormat D M ag, i)
    q = ((bin M, true, q.1.2.2.1, levelRow D ℓ), tagRow (ag ℓ).1 (ag ℓ).2) := by
  obtain ⟨h₀, _, h₂⟩ := setupTag_spec D M ag i
  exact Prod.ext (Prod.ext rfl (Prod.ext (h₀.mpr h) (Prod.ext rfl (h₂ h.1).1))) (h₂ h.1).2

end P1SolGreedy.SolDemand
