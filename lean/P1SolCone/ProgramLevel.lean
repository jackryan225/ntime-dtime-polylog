import P1SolCone.ProgramLists
import P1P5.LevelsPolyDefs

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal.AstraC10 P1ProgEng.SolKWR
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Map with access to shared encoded data. -/
theorem poly_mapParameter {U A B : Type} [Codec U] [Codec A] [Codec B] [Inhabited U] [Inhabited A]
    {xs : U → List A} {f : U × A → B} (hx : Poly xs) (hf : Poly f) :
    Poly (fun u => (xs u).map fun a => f (u, a)) :=
  (Code.Poly.identity.pair hx).compose (Poly.push (default : U) (default : A) hf)

/-- A variable-size Cartesian product of two given lists. -/
theorem poly_productList {A B : Type} [Codec A] [Codec B] [Inhabited A] [Inhabited B] :
    Poly (fun p : List A × List B => p.1.flatMap (fun a => p.2.map (a, ·))) := by
  have pairRow : Poly (fun p : List A × List B => p.1.map (fun a => p.2.map (a, ·))) :=
    poly_mapParameter Easy.fst.poly (by
      have inPair : Poly (fun x : (List A × List B) × A => (x.2, x.1.2)) := by fun_prop
      exact inPair.compose (Poly.push (default : A) (default : B) Code.Poly.identity))
  exact pairRow.compose Easy.flatten.poly

/-- Zip by the first list's indices and truncate to the second list's length. -/
theorem poly_zipLists {A B : Type} [Codec A] [Codec B] [Inhabited A] [Inhabited B] :
    Poly (fun p : List A × List B => p.1.zip p.2) := by
  have hrows : Poly (fun p : List A × List B =>
      List.ofFn (fun i : Fin p.1.length => (readAt default p.1 i.val, readAt default p.2 i.val))) :=
    poly_tabLike (l := Prod.fst) (f := fun q : (List A × List B) × ℕ =>
      (readAt default q.1.1 q.2, readAt default q.1.2 q.2)) Easy.fst.poly (by fun_prop)
  have h := poly_take (poly_lengthNat (Easy.snd.poly : Poly (Prod.snd : List A × List B → _))) hrows
  convert h using 1
  funext p
  apply List.ext_getElem
  · simp only [List.length_zip, List.length_take, List.length_ofFn, Nat.min_comm]
  · intro i hi hj
    have hbds := Nat.lt_min.mp (show i < min p.1.length p.2.length from by simpa only [List.length_zip] using hi)
    obtain ⟨ha, hb⟩ := hbds
    simp only [List.getElem_zip, List.getElem_take, List.getElem_ofFn, readAt,
      List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some]

/-- Enumerate the halves with a common exponential fuel and fixed slot cap. -/
def fueledHalves (slots : ℕ) (p : Tally × (List ℕ × List ℕ)) : List HalfCode :=
  let vals (ws : List ℕ) := assignments ((ws.map fun w => boundedWords (w, p.1)).take slots)
  (vals p.2.1).flatMap fun out => (vals p.2.2).map (out, ·)

theorem fueledHalves_poly (slots : ℕ) : Poly (fueledHalves slots) := by
  have make {ws : Tally × (List ℕ × List ℕ) → List ℕ} (hw : Poly ws) :
      Poly (fun p : Tally × (List ℕ × List ℕ) =>
        assignments (((ws p).map fun w => boundedWords (w, p.1)).take slots)) := by
    have word : Poly (fun q : (Tally × (List ℕ × List ℕ)) × ℕ => boundedWords (q.2, q.1.1)) :=
      (show Poly (fun q : (Tally × (List ℕ × List ℕ)) × ℕ => (q.2, q.1.1)) from by fun_prop).compose
        boundedWords_poly
    exact (poly_mapParameter hw word).compose (boundedAssignments_poly ([] : List Bool) slots)
  exact ((make (by fun_prop : Poly (fun p : Tally × (List ℕ × List ℕ) => p.2.1))).pair
    (make (by fun_prop : Poly (fun p : Tally × (List ℕ × List ℕ) => p.2.2)))).compose poly_productList

theorem fueledHalves_eq (cap : ℕ) (fuel : Tally) (widths : List ℕ × List ℕ)
    (h1 : widths.1.length ≤ cap) (h2 : widths.2.length ≤ cap)
    (hf : ∀ w ∈ widths.1 ++ widths.2, 2 ^ w ≤ fuel.length) :
    fueledHalves cap (fuel, widths) = halfCodes widths := by
  unfold fueledHalves halfCodes
  simp only [List.take_of_length_le (by simpa only [List.length_map] using h1 :
    (((widths.1).map fun w => boundedWords (w, fuel))).length ≤ cap),
    List.take_of_length_le (by simpa only [List.length_map] using h2 :
    (((widths.2).map fun w => boundedWords (w, fuel))).length ≤ cap)]
  have hleft : widths.1.map (fun w => boundedWords (w, fuel)) = widths.1.map bitWords := by
    apply List.map_congr_left
    intro w hw
    exact boundedWords_eq _ _ (hf w (List.mem_append_left _ hw))
  have hright : widths.2.map (fun w => boundedWords (w, fuel)) = widths.2.map bitWords := by
    apply List.map_congr_left
    intro w hw
    exact boundedWords_eq _ _ (hf w (List.mem_append_right _ hw))
  rw [hleft, hright]

section Level

variable {U R : Type} [Codec U] [Inhabited U] [CommRing R] [Fintype R]

abbrev LabelRow (R : Type) := List (Label R × List Tally)
private abbrev PhaseQuery (U : Type) := U × List KeyCode
private abbrev PhaseRowQuery (U : Type) := PhaseQuery U × KeyCode
private abbrev PhaseEntryQuery (U : Type) := PhaseRowQuery U × List KeyCode


/-- Produce the predecessor keys of a level from the explicit local providers. -/
def phaseOldKeys (pre : U × PositionCode → List PositionCode)
    (halves : U × PositionCode → List HalfCode) (p : U × List KeyCode) : List KeyCode :=
  needKeys (fun y => pre (p.1,y)) (fun y => halves (p.1,y)) p.2

theorem phaseOldKeys_poly
    {pre : U × PositionCode → List PositionCode} {halves : U × PositionCode → List HalfCode}
    (hp : Poly pre) (hh : Poly halves) : Poly (phaseOldKeys pre halves) := by
  unfold phaseOldKeys needKeys
  have indices : Poly (fun q : PhaseQuery U => (q.2.map Prod.fst).dedup) :=
    Easy.snd.poly.compose ((Code.Poly.maps _ Easy.fst.poly).compose (poly_lastDedup poly_eqPosition))
  have old : Poly (fun q : PhaseQuery U => (((q.2.map Prod.fst).dedup.flatMap (fun y => pre (q.1,y))).dedup)) := by
    have h : Poly (fun p : PhaseQuery U × PositionCode => (p.1.1, p.2)) := by fun_prop
    exact ((poly_mapParameter indices (h.compose hp)).compose Easy.flatten.poly).compose
      (poly_lastDedup poly_eqPosition)
  have entries : Poly (fun p : PhaseQuery U × PositionCode => (halves (p.1.1,p.2)).map (p.2, ·)) := by
    have h : Poly (fun p : PhaseQuery U × PositionCode => (p.1.1,p.2)) := by fun_prop
    exact (Easy.snd.poly.pair (h.compose hh)).compose
      (Poly.push (default : PositionCode) (default : HalfCode) Code.Poly.identity)
  exact (poly_mapParameter old entries).compose Easy.flatten.poly

/-- Read all assignments for the ordered list of placed positions. -/
def phaseAssignments (cap : ℕ) (halves : U × PositionCode → List HalfCode)
    (p : U × List PositionCode) : List (List KeyCode) :=
  ((assignments (((p.2.map fun y => halves (p.1,y))).take cap))).map (p.2.zip ·)

theorem phaseAssignments_poly (cap : ℕ) (halves : U × PositionCode → List HalfCode) (hh : Poly halves) :
    Poly (phaseAssignments cap halves) := by
  have h : Poly (fun p : (U × List PositionCode) × PositionCode => (p.1.1,p.2)) := by fun_prop
  have axes := poly_mapParameter (Easy.snd.poly : Poly (Prod.snd : U × List PositionCode → _)) (h.compose hh)
  have vals := axes.compose (boundedAssignments_poly (default : HalfCode) cap)
  exact (Easy.snd.poly.pair vals).compose (Poly.push ([] : List PositionCode) ([] : List HalfCode) poly_zipLists)

theorem phaseAssignments_eq (cap : ℕ) (halves : U × PositionCode → List HalfCode)
    (u : U) (sites : List PositionCode) (h : sites.length ≤ cap) :
    phaseAssignments cap halves (u,sites) = placedCodes (fun y => halves (u,y)) sites := by
  unfold phaseAssignments placedCodes
  rw [List.take_of_length_le (by simpa only [List.length_map] using h)]

/-- Ordered level rows, with pointers already converted to tally. -/
def phaseTable (cap : ℕ) (pre : U × PositionCode → List PositionCode)
    (halves : U × PositionCode → List HalfCode)
    (kernel : U × KeyCode × List KeyCode → Label R)
    (p : U × List KeyCode) : List KeyCode × List (LabelRow R) :=
  let old := phaseOldKeys pre halves p
  (old, p.2.map fun key =>
    (phaseAssignments cap halves (p.1, pre (p.1,key.1))).map fun ps =>
      (kernel (p.1,key,ps), ps.map fun a => tally (old.idxOf a)))

theorem phaseTable_poly (cap : ℕ) {pre : U × PositionCode → List PositionCode}
    {halves : U × PositionCode → List HalfCode} {kernel : U × KeyCode × List KeyCode → Label R}
    (hp : Poly pre) (hh : Poly halves) (hk : Poly kernel) :
    Poly (phaseTable cap pre halves kernel) := by
  have old := phaseOldKeys_poly hp hh
  have preKey : Poly (fun q : PhaseRowQuery U => (q.1.1,q.2.1)) := by fun_prop
  have vals : Poly (fun q : PhaseRowQuery U => phaseAssignments cap halves (q.1.1, pre (q.1.1,q.2.1))) :=
    ((show Poly (fun q : PhaseRowQuery U => q.1.1) from by fun_prop).pair (preKey.compose hp)).compose
      (phaseAssignments_poly cap halves hh)
  have dataPart : Poly (fun q : PhaseEntryQuery U => (q.1.1.1,q.1.2,q.2)) := by fun_prop
  have keySet : Poly (fun q : PhaseEntryQuery U => phaseOldKeys pre halves q.1.1) :=
    (show Poly (fun q : PhaseEntryQuery U => q.1.1) from by fun_prop).compose old
  have pointers : Poly (fun q : PhaseEntryQuery U => q.2.map fun a => tally ((phaseOldKeys pre halves q.1.1).idxOf a)) :=
    (keySet.pair Easy.snd.poly).compose
      (Poly.push ([] : List KeyCode) (default : KeyCode) (poly_indexTally poly_eqKey))
  have row := poly_mapParameter vals ((dataPart.compose hk).pair pointers)
  exact old.pair (poly_mapParameter (Easy.snd.poly : Poly (Prod.snd : PhaseQuery U → _)) row)

theorem phaseTable_eq (cap : ℕ) (pre : U × PositionCode → List PositionCode)
    (halves : U × PositionCode → List HalfCode)
    (kernel : U × KeyCode × List KeyCode → Label R) (u : U) (keys : List KeyCode)
    (hcap : ∀ q ∈ keys, (pre (u,q.1)).length ≤ cap) :
    let pureLevel := assembleLevel (fun y => pre (u,y)) (fun y => halves (u,y))
      (fun q vs => (kernel (u,q,vs)).val) keys
    phaseTable cap pre halves kernel (u,keys) = (pureLevel.1, P1P5.encLevel pureLevel.2) := by
  unfold phaseTable
  simp only [phaseOldKeys, assembleLevel, P1P5.encLevel, List.map_map, Function.comp_def, Prod.mk.injEq, true_and]
  apply List.map_congr_left
  intro q hq
  rw [phaseAssignments_eq _ _ _ _ (hcap q hq)]

end Level

end P1SolCone.SolCone
