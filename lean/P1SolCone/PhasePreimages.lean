import P1SolCone.PhaseOwner
import P1SolCone.KernelDispatch

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

theorem poly_filterParameter {U A : Type} [Codec U] [Codec A] [Inhabited U] [Inhabited A]
    {xs : U → List A} {test : U × A → Bool} (hx : Poly xs) (ht : Poly test) :
    Poly (fun u => (xs u).filter fun a => test (u,a)) := by
  have single : Poly (fun p : U × A => [p.2]) :=
    (Easy.snd.poly.pair (Code.Poly.const ([] : List A))).compose Poly.cons
  have h := (poly_mapParameter hx (Poly.choose ht single
    (Code.Poly.const ([] : List A)))).compose Easy.flatten.poly
  convert h using 1
  funext u
  generalize xs u = vals
  induction vals with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons, List.map_cons, List.flatten_cons, ← ih]
    cases test (u,a) <;> rfl

def phaseOldLanes (h : PhaseHeader) : ℕ := packetNat h.2.2.2.2 5

@[fun_prop] theorem phaseOldLanes_poly : Poly phaseOldLanes := by unfold phaseOldLanes; fun_prop

theorem phaseOldLanes_actual (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) :
    phaseOldLanes (actualPhaseHeader D u l y clock) = (D.lv l).lanes := by
  change packetNat (phaseFormat D l) 5 = _
  rw [packetNat_phaseFormat]
  rfl

def rawShrinkCandidates (a : ℕ) (h : PhaseHeader) (cache : FieldCache) (p : PositionCode) :
    List PositionCode :=
  let root := p.1 / 2 ^ J a
  let lanes := capRange (h.1,phaseOldLanes h)
  ((root :: rawNeighbors h cache root).flatMap (fun y => lanes.map (y, ·))).dedup

theorem rawShrinkCandidates_poly (a : ℕ) :
    Poly (fun p : PhaseHeader × FieldCache × PositionCode => rawShrinkCandidates a p.1 p.2.1 p.2.2) := by
  unfold rawShrinkCandidates
  let U := PhaseHeader × FieldCache × PositionCode
  have rt : Poly (fun p : U => p.2.2.1 / 2 ^ J a) := by unfold U; fun_prop
  have args : Poly (fun p : U => (p.1,p.2.1,p.2.2.1 / 2 ^ J a)) := by unfold U; fun_prop
  have heads := (rt.pair (args.compose rawNeighbors_poly)).compose Poly.cons
  have lanes : Poly (fun p : U × ℕ => capRange (p.1.1.1,phaseOldLanes p.1.1)) := by
    exact (show Poly (fun p : U × ℕ => (p.1.1.1,phaseOldLanes p.1.1)) from by unfold U; fun_prop).compose capRange_poly
  have rows := (Easy.snd.poly.pair lanes).compose
    (Poly.push (default : ℕ) (default : ℕ) (Code.Poly.identity (X := ℕ × ℕ)))
  exact ((poly_mapParameter heads rows).compose Easy.flatten.poly).compose (poly_lastDedup poly_eqPosition)

def rawShrinkPreimages (a : ℕ) (h : PhaseHeader) (cache : FieldCache) (p : PositionCode) :
    List PositionCode :=
  (rawShrinkCandidates a h cache p).filter (fun old =>
    decide (rawShrinkOwner a h cache old = p.1 * phaseChildLanes h + p.2))

set_option maxHeartbeats 1600000 in
theorem rawShrinkPreimages_poly (a : ℕ) :
    Poly (fun p : PhaseHeader × FieldCache × PositionCode => rawShrinkPreimages a p.1 p.2.1 p.2.2) := by
  unfold rawShrinkPreimages
  let U := PhaseHeader × FieldCache × PositionCode
  have args : Poly (fun p : U × PositionCode => (p.1.1,p.1.2.1,p.2)) := by unfold U; fun_prop
  have rhs : Poly (fun p : U × PositionCode => p.1.2.2.1 * phaseChildLanes p.1.1 + p.1.2.2.2) := by unfold U; fun_prop
  have ht : Poly (fun p : U × PositionCode =>
      decide (rawShrinkOwner a p.1.1 p.1.2.1 p.2 = p.1.2.2.1 * phaseChildLanes p.1.1 + p.1.2.2.2)) :=
    poly_eqNat (args.compose (rawShrinkOwner_poly a)) rhs
  exact poly_filterParameter (U := U) (A := PositionCode) (rawShrinkCandidates_poly a) ht

set_option maxHeartbeats 1200000 in
theorem rawShrinkPreimages_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y a g : ℕ) (clock : Tally) (ys : List ℕ) (p : PositionCode)
    (hcover : ∀ q ∈ p.1 / 2 ^ J a :: actualRawNeighbors D u l (p.1 / 2 ^ J a), q ∈ ys)
    (hslot : (D.lv l).slots = 2 ^ a) (hs : (D.lv l).slots ≤ clock.length)
    (hlanes : (D.lv l).lanes = 2 ^ packingLaneBits a g) (hl : (D.lv l).lanes ≤ clock.length)
    (hg : (D.lv (l+1)).lanes = 2 ^ g) (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    rawShrinkPreimages a h (rawRoundCache extra u h ys) p = shrinkPreimages D u l a g p := by
  let h := actualPhaseHeader D u l y clock
  let C := rawRoundCache extra u h ys
  let root := p.1 / 2 ^ J a
  have hb : rawNeighbors h C root = actualRawNeighbors D u l root :=
    rawNeighbors_eq extra D u l y clock ys root (hcover _ List.mem_cons_self) hs hw
  have hlane : capRange (h.1,phaseOldLanes h) = List.range (2 ^ packingLaneBits a g) := by
    change List.range (min (phaseOldLanes h) clock.length) = _
    rw [phaseOldLanes_actual D u l y clock, min_eq_left hl, hlanes]
  have he : rawShrinkCandidates a h C p = shrinkCandidates D u l a g root := by
    unfold rawShrinkCandidates shrinkCandidates
    dsimp only
    rw [hb, hlane]
    unfold actualRawNeighbors
    rw [hslot]
  change rawShrinkPreimages a h C p = _
  unfold rawShrinkPreimages shrinkPreimages
  rw [he, phaseChildLanes_actual D u l y clock, hg]
  apply List.filter_congr
  intro old hold
  have hm : old ∈ (root :: actualRawNeighbors D u l root).flatMap
      (fun z => (List.range (2 ^ packingLaneBits a g)).map (z,·)) := by
    have hmem := List.mem_dedup.mp hold
    unfold actualRawNeighbors
    rw [hslot]
    exact hmem
  obtain ⟨z,hz,hr⟩ := List.mem_flatMap.mp hm
  obtain ⟨lane,hs',rfl⟩ := List.mem_map.mp hr
  rw [rawShrinkOwner_eq extra D u l y a g clock ys _ (hcover _ hz) hs hw hslot hg (List.mem_range.mp hs')]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]

def rawRefreshPreimage (h : PhaseHeader) (p : PositionCode) : PositionCode :=
  let d := packetNat h.2.2.2.2 4
  (p.1 / d, p.1 % d * phaseChildLanes h + p.2)

theorem rawRefreshPreimage_poly :
    Poly (fun p : PhaseHeader × PositionCode => rawRefreshPreimage p.1 p.2) := by
  unfold rawRefreshPreimage
  dsimp only
  fun_prop

theorem rawRefreshPreimage_eq (D : Dims) (u : List Bool) (l y a g : ℕ) (clock : Tally)
    (p : PositionCode) (hslot : (D.lv l).slots = 2 ^ a) (hlanes : (D.lv (l+1)).lanes = 2 ^ g) :
    rawRefreshPreimage (actualPhaseHeader D u l y clock) p = refreshPreimage a g p := by
  have eq : packetNat (phaseFormat D l) 4 = (D.lv l).slots := by rw [packetNat_phaseFormat]; rfl
  unfold rawRefreshPreimage refreshPreimage join
  dsimp only
  rw [phaseChildLanes_actual, hlanes]
  change (p.1 / packetNat (phaseFormat D l) 4,p.1 % packetNat (phaseFormat D l) 4 * 2 ^ g + p.2) = _
  rw [eq,hslot]

end P1SolCone.SolCone
