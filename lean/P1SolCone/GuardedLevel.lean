import P1SolCone.TerminalGuard
import P1SolCone.CheckedBudget

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

abbrev LevelCode (F : Type) := List (LabelRow F)
abbrev ConeStateCode (F : Type) := Bool × List KeyCode × List (LevelCode F)

def encodeConeState {F : Type} : CheckedTableState F → ConeStateCode F
  | none => (false,[],[])
  | some (keys, levels) => (true,keys,levels.map P1P5.encLevel)

theorem widthsWithin_poly : Poly (fun p : ℕ × (List ℕ × List ℕ) => widthsWithin p.1 p.2) := by
  unfold widthsWithin
  let X := ℕ × List ℕ × List ℕ
  have test : Poly (fun p : X × ℕ => decide (p.2 ≤ p.1.1)) :=
    poly_le Easy.snd.poly Easy.fst.poly.fstCompose
  have f : Poly (fun p : X => p.2.1) := by unfold X; fun_prop
  have g : Poly (fun p : X => p.2.2) := by unfold X; fun_prop
  exact ((poly_allParameter f test).pair (poly_allParameter g test)).compose
    (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

section Level

variable {U F : Type} [Codec U] [Inhabited U] [CommRing F] [Fintype F]

/-- Retain the already assembled levels and produce the next level only after the guards. -/
def advanceConeCode (cap : ℕ) (allowed : U × KeyCode → Bool)
    (pre : U × PositionCode → List PositionCode) (halves : U × PositionCode → List HalfCode)
    (kernel : U × KeyCode × List KeyCode → Label F) (p : U × ConeStateCode F) : ConeStateCode F :=
  bif p.2.1 && p.2.2.1.all (fun q => allowed (p.1,q)) then
    let table := phaseTable cap pre halves kernel (p.1,p.2.2.1)
    (true,table.1,table.2 :: p.2.2.2)
  else (false,[],[])

theorem advanceConeCode_poly (cap : ℕ) {allowed : U × KeyCode → Bool}
    {pre : U × PositionCode → List PositionCode} {halves : U × PositionCode → List HalfCode}
    {kernel : U × KeyCode × List KeyCode → Label F}
    (ha : Poly allowed) (hp : Poly pre) (hh : Poly halves) (hk : Poly kernel) :
    Poly (advanceConeCode cap allowed pre halves kernel) := by
  let Q := U × ConeStateCode F
  have keys : Poly (fun p : Q => p.2.2.1) := by unfold Q; fun_prop
  have prep : Poly (fun p : Q × KeyCode => (p.1.1,p.2)) := by unfold Q; fun_prop
  have live : Poly (fun p : Q => p.2.1) := by unfold Q; fun_prop
  have check := (live.pair (poly_allParameter keys (prep.compose ha))).compose
    (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly
  have pair : Poly (fun p : Q => (p.1,p.2.2.1)) := Easy.fst.poly.pair keys
  have table := pair.compose (phaseTable_poly cap hp hh hk)
  have tail : Poly (fun p : Q => p.2.2.2) := by unfold Q; fun_prop
  exact Poly.choose check ((Code.Poly.const true).pair (table.fstCompose.pair
    ((table.sndCompose.pair tail).compose Poly.cons))) (Code.Poly.const (false,[],[]))

end Level

section Conformance

theorem assembleLevel_congr_on {F : Type}
    (pre pre' : PositionCode → List PositionCode) (half half' : PositionCode → List HalfCode)
    (k k' : KeyCode → List KeyCode → F) (keys : List KeyCode)
    (hp : ∀ q ∈ keys, pre q.1 = pre' q.1)
    (hh : ∀ q ∈ keys, ∀ y ∈ pre' q.1, half y = half' y)
    (hk : ∀ q ∈ keys, ∀ ps ∈ placedCodes half' (pre' q.1), k q ps = k' q ps) :
    assembleLevel pre half k keys = assembleLevel pre' half' k' keys := by
  have ep : ((keys.map Prod.fst).dedup.flatMap pre) = ((keys.map Prod.fst).dedup.flatMap pre') := by
    apply List.flatMap_congr
    intro pos hpos
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hpos)
    exact hp q hq
  have eold : needKeys pre half keys = needKeys pre' half' keys := by
    unfold needKeys
    rw [ep]
    apply List.flatMap_congr
    intro y hy
    obtain ⟨pos,hpos,hpre⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hy)
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hpos)
    rw [hh q hq y hpre]
  unfold assembleLevel
  dsimp only
  rw [eold]
  apply Prod.ext
  · rfl
  · apply List.map_congr_left
    intro q hq
    have eh : (pre' q.1).map half = (pre' q.1).map half' := List.map_congr_left (hh q hq)
    have eplace : placedCodes half (pre' q.1) = placedCodes half' (pre' q.1) := by
      simp only [placedCodes, eh]
    rw [hp q hq, eplace]
    apply List.map_congr_left
    intro ps hps
    rw [hk q hq ps hps]

/-- Compare one guarded step using equality only on the frontier and its placed inputs. -/
theorem advanceConeCode_eq {U F : Type} [Codec U] [Inhabited U] [CommRing F] [Fintype F]
    (cap : ℕ) (allowed : U × KeyCode → Bool)
    (pre : U × PositionCode → List PositionCode) (half : U × PositionCode → List HalfCode)
    (kernel : U × KeyCode × List KeyCode → Label F)
    (ok' : ℕ → KeyCode → Bool) (pre' : ℕ → PositionCode → List PositionCode)
    (half' : ℕ → PositionCode → List HalfCode) (kernel' : ℕ → KeyCode → List KeyCode → F)
    (l : ℕ) (u : U) (keys : List KeyCode) (levels : List (P1P5.Level F))
    (ha : ∀ q ∈ keys, allowed (u,q) = ok' l q)
    (hcap : ∀ q, ok' l q = true → (pre' l q.1).length ≤ cap)
    (hp : ∀ q ∈ keys, pre (u,q.1) = pre' l q.1)
    (hh : ∀ q ∈ keys, ok' l q = true → ∀ y ∈ pre' l q.1, half (u,y) = half' l y)
    (hk : ∀ q ∈ keys, ∀ ps ∈ placedCodes (half' l) (pre' l q.1), (kernel (u,q,ps)).val = kernel' l q ps) :
    advanceConeCode cap allowed pre half kernel (u, encodeConeState (some (keys,levels))) =
      encodeConeState (advanceChecked ok' pre' half' kernel' (some (keys,levels)) l) := by
  have test : keys.all (fun q => allowed (u,q)) = keys.all (ok' l) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro h q hq
    · exact (ha _ hq).symm ▸ h q hq
    · exact ha _ hq ▸ h q hq
  unfold advanceConeCode advanceChecked encodeConeState
  dsimp only [Option.bind]
  rw [Bool.true_and, test]
  by_cases ok : keys.all (ok' l) = true
  · have pass := List.all_eq_true.mp ok
    rw [ok]
    have tree := phaseTable_eq cap pre half kernel u keys (fun q hq => by
      rw [hp q hq]
      exact hcap q (pass q hq))
    dsimp only at tree
    rw [tree]
    have c := assembleLevel_congr_on (fun y => pre (u,y)) (pre' l)
      (fun y => half (u,y)) (half' l) (fun q ps => (kernel (u,q,ps)).val) (kernel' l) keys hp
      (fun q hq => hh q hq (pass q hq)) hk
    rw [c]
    rfl
  · rw [Bool.eq_false_iff.mpr ok]
    rfl

end Conformance

end P1SolCone.SolCone
