import P1Int.FormAg
import P1Int.FormC11Defs
import P1Int.FormC14Defs
import P1ChkFinal.D5Steps

/-!
# The concrete groups and index of `D5Steps` at the fixed code (P1-lean-integ, statements only)

* `c12G u`: the right side of `P1ChkFinal.d5_c12_step` at `fixedDims` (payload long enough, zero tail).
* `c13G bs l Wof u`: the right side of `P1ChkFinal.d5_c13_step` at `fixedDims` (the stored chain is a chain `j` with
  `ChainOK bs l (Wof x (ofFn u)) j`); `Wof` = the cone lane's evaluation of `W_v` from the witness.
* `fixedGroups H bs l Wof`: the `D5Groups` (dir, c14, c4, greedy, c10, c11, c12, c13).
* `fixedIndex cnt`: the `D5Index` (top = `fixedDims.top`; level of a per-level index `i % 2 ^ clog 2 (top + 1)`,
  i.e. `i % 2 ^ levBits D` of P1ChkGreedy; the counts `cnt` are fixed with the dispatcher).
* `FormFixAsmTarget`: `FormFix` for these groups, from the piece `C14FixTarget` (Sol formc14, running) and the proved
  pieces `dir_fix`, `finalPanelOnly`, `c11_fix`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)

/-- **Group `c12` at the fixed code.** -/
def c12G (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  P1ChkFinal.pre (P1ChkFinal.wsOf (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u))
      (P1ChkFinal.finN (fixedDims Bt V a b x d bigBias termBias)) ≤
    (P1Wit.rdPayload (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u)).length ∧
  ∀ c ∈ (P1Wit.rdPayload (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u)).drop
      (P1ChkFinal.pre (P1ChkFinal.wsOf (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u))
        (P1ChkFinal.finN (fixedDims Bt V a b x d bigBias termBias))), c = false

/-- **Group `c13` at the fixed code** (`Wof`: the evaluation of `W_v` from the witness, cone lane). -/
def c13G (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2)
    (Wof : List Bool → List Bool → ℕ → F) (u : Fin (fixedM Bt a b x) → Bool) : Prop :=
  ∃ j : Fin (P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias) + 1) → Fin d,
    (∀ v : Fin (P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias) + 1),
      (j v : ℕ) = P1Wit.rdChain (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) v) ∧
    P1Count.ChainOK bs l
      (fun i : Fin (P1ChkFinal.finP (fixedDims Bt V a b x d bigBias termBias)) => Wof x (List.ofFn u) i) j

/-- **The groups of `D5Steps` at the fixed code.** -/
def fixedGroups (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) (bs : Module.Basis (Fin d) (ZMod 2) F)
    (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F) :
    D5Groups (Fin (fixedM Bt a b x) → Bool) where
  dir := dirG Bt κ hκ V a b x d bigBias termBias H
  c14 := c14G Bt κ hκ V a b x d bigBias termBias H
  c4 := c4G Bt κ hκ V a b x d bigBias termBias H
  greedy := fun lv u => greedyG Bt κ hκ V a b x d bigBias termBias H lv u
  c10 := fun lv u => c10G Bt κ hκ V a b x d bigBias termBias H lv u
  c11 := c11G Bt V a b x d bigBias termBias
  c12 := c12G Bt V a b x d bigBias termBias
  c13 := c13G Bt V a b x d bigBias termBias bs l Wof

/-- **The index of `D5Steps` at the fixed code** (counts `cnt` from the dispatcher). -/
def fixedIndex (cnt : ℕ → ℕ) : D5Index where
  top := (fixedDims Bt V a b x d bigBias termBias).top
  cnt := cnt
  lev := fun _ i => i % 2 ^ Nat.clog 2 ((fixedDims Bt V a b x d bigBias termBias).top + 1)

/-- **Target: `FormFix` for the fixed groups**, from the piece `C14FixTarget`. -/
def FormFixAsmTarget (H : FixedRecords Bt κ hκ V a b x d bigBias termBias) : Prop :=
  C14FixTarget Bt κ hκ V a b x d bigBias termBias H →
    ∀ (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (Wof : List Bool → List Bool → ℕ → F)
      (cnt : ℕ → ℕ),
      FormFix Bt κ hκ V a b x bigBias termBias H (fixedIndex Bt V a b x d bigBias termBias cnt)
        (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof)

end

end P11

end P1Int
