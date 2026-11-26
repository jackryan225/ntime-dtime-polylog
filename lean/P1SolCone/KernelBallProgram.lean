import P1SolCone.PhaseCoverage

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Build the ordered C10 neighborhood from a shared phase cache. Its visit list keeps
repeated addresses, even when multiple visits refer to the same cached fields. -/
theorem poly_bfs_fixed {A : Type} [Codec A] [Inhabited A]
    {nbrs : A × ℕ → List ℕ} (h : Poly nbrs) (r : ℕ) :
    Poly (fun p : A × ℕ => bfs (fun y => nbrs (p.1,y)) p.2 r) := by
  induction r with
  | zero => exact (Easy.snd.poly.pair (Code.Poly.const ([] : List ℕ))).compose Poly.cons
  | succ r ih =>
    have prep : Poly (fun p : (A × ℕ) × ℕ => (p.1.1,p.2)) := by fun_prop
    exact ih.app ((poly_mapParameter ih (prep.compose h)).compose Easy.flatten.poly)

theorem poly_ballList_fixed {A T : Type} [Codec A] [Inhabited A] [Codec T]
    {nbrs : A × ℕ → List ℕ} {data : A × ℕ → Option T} (h : Poly nbrs) (hd : Poly data) (r : ℕ) :
    Poly (fun p : A × ℕ => ballList (fun y => nbrs (p.1,y)) (fun y => data (p.1,y)) p.2 r) := by
  unfold ballList
  have prep : Poly (fun p : (A × ℕ) × ℕ => (p.1.1,p.2)) := by fun_prop
  exact poly_mapParameter (poly_bfs_fixed h r) (Easy.snd.poly.pair (prep.compose hd))

def cachedValidNeighbors (h : PhaseHeader) (c : FieldCache) (y : ℕ) : List ℕ :=
  bif decide (y < packetNat h.2.2.2.2 3) then rawNeighbors h c y else []

theorem cachedValidNeighbors_poly :
    Poly (fun p : PhaseHeader × FieldCache × ℕ => cachedValidNeighbors p.1 p.2.1 p.2.2) := by
  unfold cachedValidNeighbors
  have test : Poly (fun p : PhaseHeader × FieldCache × ℕ =>
      decide (p.2.2 < packetNat p.1.2.2.2.2 3)) := by fun_prop
  exact Poly.choose test rawNeighbors_poly (Code.Poly.const [])

theorem cachedValidNeighbors_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (z : ℕ) (hz : z ∈ ys)
    (hc : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    cachedValidNeighbors h (rawRoundCache extra u h ys) z = validRawNeighbors D u l z := by
  let h := actualPhaseHeader D u l y clock
  have hb : packetNat h.2.2.2.2 3 = (D.lv l).bases := by
    change packetNat (phaseFormat D l) 3 = _
    rw [packetNat_phaseFormat]
    rfl
  change cachedValidNeighbors h _ z = _
  unfold cachedValidNeighbors validRawNeighbors
  simp only [hb]
  by_cases hvalid : z < (D.lv l).bases
  · simp only [hvalid, decide_true, Bool.cond_true, if_true]
    exact rawNeighbors_eq extra D u l y clock ys z hz hc hw
  · simp only [hvalid, decide_false, Bool.cond_false, if_false]

theorem ballList_congr_on {T : Type} {next next' : ℕ → List ℕ} {data data' : ℕ → Option T}
    {root r : ℕ} (hn : ∀ j < r, ∀ z ∈ bfs next root j, next' z = next z)
    (hd : ∀ z ∈ bfs next root r, data' z = data z) :
    ballList next' data' root r = ballList next data root r := by
  unfold ballList
  rw [bfs_congr_cached hn]
  apply List.map_congr_left
  intro z hz
  rw [hd z hz]

end P1SolCone.SolCone
