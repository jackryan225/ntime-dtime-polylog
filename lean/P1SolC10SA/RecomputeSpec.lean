import P1SolC10SA.PayloadSpec

namespace P1SolC10SA.SolShrink

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7

/-- The C10 panel fields in outgoing-slot order and residual-lane order. -/
def statePanelRows {d n : ℕ} (Y : State d n) (v : Y.Base) : List SlotRow :=
  List.ofFn fun k : Fin (2 ^ d) =>
    (stateEnd Y false v k, stateEnd Y true v k,
      List.ofFn fun l : Fin (2 ^ n) => outWidths Y v k ((bitWordFinEquiv n).symm l))

theorem laneCount_spec {a g : ℕ} {terms : OldTerms}
    (h : terms.length = 2 ^ packingLaneBits a g) : laneCount a terms = 2 ^ g := by
  have hpow : 2 ^ packingLaneBits a g = (2 ^ colourBits a * oldDegree a * tagCount a) * 2 ^ g := by
    simp only [packingLaneBits, pow_add, colourBits, oldDegree, tagCount, Nat.mul_assoc]
  rw [laneCount, h, hpow, Nat.mul_div_cancel_left]
  positivity

theorem limitedPositions_spec {a g : ℕ} {terms : OldTerms}
    (h : terms.length = 2 ^ packingLaneBits a g) :
    limitedPositions terms (laneCount a terms) = List.ofFn (fun i : Fin (2 ^ g) => i.val) := by
  have hg : 2 ^ g ≤ terms.length := by
    rw [h]
    exact Nat.pow_le_pow_right (by decide) (by unfold packingLaneBits; omega)
  have he : min terms.length (laneCount a terms) = 2 ^ g := by
    rw [laneCount_spec h, Nat.min_eq_right hg]
  exact congrArg (fun n => List.ofFn (fun i : Fin n => i.val)) he

section Correctness

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)

noncomputable local instance : DecidableEq X.Base := Classical.decEq _

theorem panelSlot_spec {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
    (layout : Bool) (j : TagW a) (i : Fin (2 ^ b)) :
    let w := fun m t => X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t
    let Y := outState X ready layout w
    let ls := List.ofFn (fun l : Fin (2 ^ g) => l.val)
    panelSlot B a (SD a b) ((2 ^ g, db, layout), baseMotifRows a (2 ^ g) db,
      ballIds a b (2 ^ g) db, ls, addr X x, wordNum j) i.val =
      (stateEnd Y false (x,j) i, stateEnd Y true (x,j) i,
        List.ofFn fun l : Fin (2 ^ g) => outWidths Y (x,j) i ((bitWordFinEquiv g).symm l)) := by
  let w := fun m t => X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t
  let p := (x,j)
  let Y := outState X ready layout w
  let keyId (incoming : Bool) := idAt a (∑ t, SD a b t)
    (localFibre a b (2 ^ g) db incoming layout (packedCode X p)) i.val
  let ls := List.ofFn (fun l : Fin (2 ^ g) => l.val)
  change (endRecord a (∑ t, SD a b t) false (2 ^ g, db, layout) (ballIds a b (2 ^ g) db)
      (addr X x) (wordNum j) i.val (keyId false),
    endRecord a (∑ t, SD a b t) true (2 ^ g, db, layout) (ballIds a b (2 ^ g) db)
      (addr X x) (wordNum j) i.val (keyId true),
    widthColumn B a (SD a b) (2 ^ g, db, layout) (baseMotifRows a (2 ^ g) db) (keyId false) ls) =
    (stateEnd Y false p i, stateEnd Y true p i,
      List.ofFn fun l : Fin (2 ^ g) => outWidths Y p i ((bitWordFinEquiv g).symm l))
  exact Prod.ext (endRecord_spec X ready layout w h.toLocalRows false j i)
    (Prod.ext (endRecord_spec X ready layout w h.toLocalRows true j i) (by
      simp only [widthColumn, ls, List.map_ofFn, Function.comp_def]
      apply congrArg List.ofFn
      funext l
      have eq : wordNum ((bitWordFinEquiv g).symm l) = l.val :=
        congrArg Fin.val ((bitWordFinEquiv g).apply_symm_apply l)
      rw [← eq]
      exact widthAt_spec B X s h ready layout j i ((bitWordFinEquiv g).symm l)))

theorem recompute_spec {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
    (hterm : (rootTerms db (addr X x)).length = 2 ^ packingLaneBits a g) (j : TagW a) :
    recompute B a b (((addr X x, db), layoutBit B X s), wordNum j) =
      some (statePanelRows (X.shrinkNext B ready s) (x,j)) := by
  unfold recompute
  dsimp only
  rw [limitedPositions_spec hterm, laneCount_spec hterm]
  let layout := layoutBit B X s
  let w := fun m t => X.packingData.termWidths B X.shrinkNumber X.packingWidth s m layout t
  change _ = some (statePanelRows (outState X ready layout w) (x,j))
  apply congrArg some
  unfold statePanelRows
  apply congrArg List.ofFn
  funext i
  exact panelSlot_spec B ready X s h (layoutBit B X s) j i

end Correctness

end P1SolC10SA.SolShrink
