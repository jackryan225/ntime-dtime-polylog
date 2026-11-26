import P1SolC10SA.Primitives
import OAI.Computability.VPVNP.PackedShrinkStep

namespace P1SolC10SA.SolShrink

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid

def splitWidthNum (w q i : ℕ) : ℕ :=
  bif decide (i < w % q) then w / q + 1 else w / q

theorem splitWidthNum_spec (w q : ℕ) (i : Fin q) : splitWidthNum w q i.val = splitWidth w q i := by
  by_cases h : i.val < w % q <;> simp [splitWidthNum, splitWidth, h]

@[fun_prop] theorem splitWidthNum_poly : Poly (fun p : ℕ × ℕ × ℕ => splitWidthNum p.1 p.2.1 p.2.2) := by
  unfold splitWidthNum
  apply Code.Poly.choose (ltOn_poly (by fun_prop) (by fun_prop)) <;> fun_prop

def ceilRootNum (n d : ℕ) : ℕ :=
  bif decide (n = 0) then 0 else Nat.sqrt ((n - 1) / d) + 1

theorem ceilRootNum_spec (n d : ℕ) : ceilRootNum n d = MotifAdmission.ceilRoot n d := by
  by_cases h : n = 0 <;>
    simp [ceilRootNum, MotifAdmission.ceilRoot, MotifAdmission.floorRoot_eq, h]

@[fun_prop] theorem ceilRootNum_poly : Poly (fun p : ℕ × ℕ => ceilRootNum p.1 p.2) := by
  unfold ceilRootNum
  apply Code.Poly.choose (eqOn_poly poly_fst (Code.Poly.const 0)) <;> fun_prop

section Term

variable {k : Type*} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

noncomputable def supplyWidthNum (ab cd v : ℕ) : ℕ :=
  let num := MotifAdmission.weight demandMass false * (ab * ab) +
    MotifAdmission.weight demandMass true * (cd * cd)
  let den := B.scale ^ 2 * MotifAdmission.denominator demandMass
  v + ceilRootNum num den * B.selectorBits

@[fun_prop] theorem supplyWidthNum_poly :
    Poly (fun p : ℕ × ℕ × ℕ => supplyWidthNum B p.1 p.2.1 p.2.2) := by
  unfold supplyWidthNum
  dsimp only
  fun_prop

theorem supplyWidthNum_spec (ab cd : ℕ) (v : Bool × Fin 4 → ℕ) (i : Bool × Fin 4) :
    supplyWidthNum B ab cd (v i) =
      MotifConversion.supplyWidths B (demandWidths ab cd) v i := by
  simp only [supplyWidthNum, ceilRootNum_spec, MotifConversion.supplyWidths,
    MotifConversion.repetitions, MotifAdmission.copies, MotifAdmission.energy,
    Fintype.sum_bool, demandWidths, pow_two, Nat.add_comm]

end Term

end P1SolC10SA.SolShrink
