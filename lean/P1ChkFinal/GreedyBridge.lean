import P1Int.TrueH
import P1Int.FormAg
import P1ChkFinal.GreedyShrinkTarget
import P1ChkFinal.C7R
import P1Int.FormLev

/-!
# P1ChkFinal.GreedyBridge: the two encoding bridges of the field `D5Steps.greedy` (statements; lane P1-lean-greedy)

At the true records `H = trueH .. hH`, a level `ℓ < top`, a witness `u` and a tuple `t` that agrees with `u` on the trit
section, on all sections of the levels `< ℓ` and on the panel sections of level `ℓ` (what the earlier groups give: `c4G` for
`ℓ = 0`, `c10G (ℓ - 1)` else), there is the state `X` of level `ℓ` (the state of `t`'s execution at depth `ℓ`) whose panels
are the stored ones, and
* (shrinking level) `ShrinkTrue Bt.shrink D u ℓ X ↔ greedyG ℓ u`;
* (refresh level) `(∃ c, storedTm D u ℓ X = trueBlockTerms .. X c) ↔ greedyG ℓ u`.
Why true: the trit section fixes the skeleton `σ` (embedding), the term tables of the levels `< ℓ` fix the choices before `ℓ`
(`tableAt_injective`), so every tuple of `greedyG ℓ u` has the same state at level `ℓ`; conversely the selection / refresh
choice at `ℓ`, any continuation (non-empty choices), a payload and a chain give a tuple `t'` with `LevUpTo (ℓ + 1)`.
-/

namespace P1ChkFinal.GreedyBridge

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.SpectralGeometry OAI.Computability.VPVNP.Compression.Refresh
open P1Int P1Int.P11

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
  (hH : TrueHFacts Bt κ hκ V a b x d bigBias termBias)

/-- **Bridge at a shrinking level** (statement). -/
def BridgeShrinkTarget : Prop :=
  ∀ (ℓ : ℕ), ℓ < (fixedDims Bt V a b x d bigBias termBias).top →
    ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).shrink = true →
    ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    SecEq Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t P1Wit.secTrit →
    LevUpTo Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t ℓ →
    (∀ kk : P1Wit.Mem, panelKind kk = true →
      SecEq Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t (P1Wit.secLev ℓ kk)) →
    ∃ (a' g' : ℕ) (X : State a' (packingLaneBits a' g')),
      ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).bases = Fintype.card X.Base ∧
      ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).slots = 2 ^ a' ∧
      genuineAg (fun n => P1Wit.SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1 (lpTime a b n)
        (a * (n ^ 2 + 1)) d bigBias termBias) x.length ℓ = (a', g') ∧
      (∀ z : X.Base, P1ChkFinal.PanelMatch (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) ℓ
        (P1P7.addr X z) (P1P7.panel X z)) ∧
      (P1ChkFinal.GreedyStep.ShrinkTrue Bt.shrink (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) ℓ X ↔
        greedyG Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) ℓ u)

/-- **Bridge at a refresh level** (statement); `a = S.degreeExponent (Fin.last S.steps)` (the port exponent). -/
def BridgeRefreshTarget : Prop :=
  ∀ (ℓ : ℕ), ℓ < (fixedDims Bt V a b x d bigBias termBias).top →
    ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).shrink = false →
    ∀ (u : Fin (fixedM Bt a b x) → Bool) (t : (fixedCD Bt κ hκ V a b x).Tup d),
    SecEq Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t P1Wit.secTrit →
    LevUpTo Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t ℓ →
    (∀ kk : P1Wit.Mem, panelKind kk = true →
      SecEq Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) u t (P1Wit.secLev ℓ kk)) →
    ∃ (g' : ℕ) (X : State (S.degreeExponent (Fin.last S.steps)) (S.degreeExponent (Fin.last S.steps) + g')),
      ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).bases = Fintype.card X.Base ∧
      ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).termKeys = 2 ^ g' ∧
      ((fixedDims Bt V a b x d bigBias termBias).lv ℓ).laneW - S.degreeExponent (Fin.last S.steps) = g' ∧
      (∀ z : X.Base, P1ChkFinal.PanelMatch (fixedDims Bt V a b x d bigBias termBias) (List.ofFn u) ℓ
        (P1P7.addr X z) (P1P7.panel X z)) ∧
      ((∃ c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos S.expanderExponent)
          (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh,
          P1ChkFinal.C7R.storedTm (dH := 2 ^ S.expanderExponent) (fixedDims Bt V a b x d bigBias termBias)
            (List.ofFn u) ℓ X =
          P1ChkGreedy.trueBlockTerms S.graph (Nat.two_pow_pos S.expanderExponent)
            (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh X c) ↔
        greedyG Bt κ hκ V a b x d bigBias termBias (trueH Bt κ hκ V a b x d bigBias termBias hH) ℓ u)

/-! Consistency (argued, the Lean test timed out in elaboration at `trueH`, grd-40): with integ's PROVED `levels_sound`,
`greedyG ℓ (fixedEnc t)` gives a tuple `t'` that meets the premise for `u = fixedEnc t`, so the bridges say the code of every
tuple stores the true greedy data of its level state: the design of `TrueRecords.panelAt` (colour, offset, energy at
`y * 2 + eCode l`, `layoutBit` = `C9_true` comparison) and `tableAt` (term slots at `arcKey` / `refreshAddress`). -/

end P1ChkFinal.GreedyBridge
