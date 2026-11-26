import P1SolCone.PhaseSelect
import P1SolCone.PhaseWidths
import P1SolCone.GuardedLevel

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def phaseRoots (limit : ℕ) (h : PhaseHeader) (keys : List KeyCode) : List ℕ :=
  ((keys.map (fun q => rawPhaseRoot limit h q.1.1)).dedup)

theorem phaseRoots_poly (limit : ℕ) :
    Poly (fun p : PhaseHeader × List KeyCode => phaseRoots limit p.1 p.2) := by
  unfold phaseRoots
  have a : Poly (fun p : (PhaseHeader × List KeyCode) × KeyCode => (p.1.1,p.2.1.1)) := by fun_prop
  exact (poly_mapParameter Easy.snd.poly (a.compose (rawPhaseRoot_poly limit))).compose
    (poly_lastDedup (poly_eqNat Easy.fst.poly Easy.snd.poly))

theorem phaseRoots_mem (limit : ℕ) (h : PhaseHeader) (ks : List KeyCode) (key : KeyCode) (hk : key ∈ ks) :
    rawPhaseRoot limit h key.1.1 ∈ phaseRoots limit h ks :=
  List.mem_dedup.mpr (List.mem_map_of_mem hk)

def phaseParents (limit : ℕ) (h : PhaseHeader) (c : FieldCache) (keys : List KeyCode) : List PositionCode :=
  (((keys.map Prod.fst).dedup.flatMap (fun p => rawPhasePreimages limit (h,c,p)))).dedup

theorem phaseParents_poly (limit : ℕ) :
    Poly (fun p : PhaseHeader × FieldCache × List KeyCode => phaseParents limit p.1 p.2.1 p.2.2) := by
  unfold phaseParents
  let A := PhaseHeader × FieldCache × List KeyCode
  have ks : Poly (fun p : A => p.2.2) := by unfold A; fun_prop
  have ps := (ks.compose (Code.Poly.maps _ Easy.fst.poly)).compose (poly_lastDedup poly_eqPosition)
  have a : Poly (fun p : A × PositionCode => (p.1.1,p.1.2.1,p.2)) := by unfold A; fun_prop
  exact ((poly_mapParameter ps (a.compose (rawPhasePreimages_poly limit))).compose Easy.flatten.poly).compose
    (poly_lastDedup poly_eqPosition)

theorem phaseParents_mem (limit : ℕ) (h : PhaseHeader) (c : FieldCache) (ks : List KeyCode)
    (key : KeyCode) (hk : key ∈ ks) (p : PositionCode) (hp : p ∈ rawPhasePreimages limit (h,c,key.1)) :
    p ∈ phaseParents limit h c ks :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨key.1,List.mem_dedup.mpr (List.mem_map_of_mem hk),hp⟩)

/-- Shared small data at one phase after obtaining the raw panels and the explicit width fields. -/
abbrev PhaseLocal := PhaseHeader × FieldCache × FieldCache × Tally × ℕ

def localParents (lim : ℕ) (p : PhaseLocal × PositionCode) : List PositionCode :=
  rawPhasePreimages lim (p.1.1,p.1.2.1,p.2)

theorem localParents_poly (lim : ℕ) : Poly (localParents lim) :=
  (show Poly (fun p : PhaseLocal × PositionCode => (p.1.1,p.1.2.1,p.2)) from by fun_prop).compose
    (rawPhasePreimages_poly lim)

def localWidths (p : PhaseLocal × PositionCode) : List ℕ × List ℕ :=
  rawHalfWidths p.1.1 p.1.2.1 p.1.2.2.1 p.2

theorem localWidths_poly : Poly localWidths :=
  (show Poly (fun p : PhaseLocal × PositionCode => (p.1.1,p.1.2.1,p.1.2.2.1,p.2)) from by fun_prop).compose
    rawHalfWidths_poly

def localHalves (slots : ℕ) (p : PhaseLocal × PositionCode) : List HalfCode :=
  fueledHalves slots (p.1.2.2.2.1,localWidths p)

theorem localHalves_poly (slots : ℕ) : Poly (localHalves slots) :=
  ((show Poly (fun p : PhaseLocal × PositionCode => p.1.2.2.2.1) from by fun_prop).pair localWidths_poly).compose
    (fueledHalves_poly slots)

def localAllowed (lim parents : ℕ) (p : PhaseLocal × KeyCode) : Bool :=
  let sites := localParents lim (p.1,p.2.1)
  decide (sites.length ≤ parents) && sites.all fun y => widthsWithin p.1.2.2.2.2 (localWidths (p.1,y))

theorem localAllowed_poly (lim parents : ℕ) : Poly (localAllowed lim parents) := by
  unfold localAllowed
  let A := PhaseLocal × KeyCode
  have r : Poly (fun p : A => (p.1, p.2.1)) := by unfold A; fun_prop
  have sites := r.compose (localParents_poly lim)
  have len := poly_lengthNat sites
  have count := poly_le len (Code.Poly.const parents)
  have q : Poly (fun p : A × PositionCode => (p.1.1,p.2)) := by unfold A; fun_prop
  have w : Poly (fun p : A × PositionCode => p.1.1.2.2.2.2) := by unfold A; fun_prop
  have safe := poly_allParameter sites ((w.pair (q.compose localWidths_poly)).compose widthsWithin_poly)
  exact (count.pair safe).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

end P1SolCone.SolCone
