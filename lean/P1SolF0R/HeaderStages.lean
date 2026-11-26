import P1SolF0R.HeaderPlan
import P1SolF0R.TwoBatches
import P1SolF0R.Prepare

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Net P1ChkFinal.AstraC10 P1SolC10P.SolC10prog
open scoped P1ChkFinal.AstraC10

noncomputable section

abbrev Request := P1P5.KW.PosCode
abbrev Planned := HeaderPlan × HalfCode
abbrev Offered (F : Type) := Label F × List Request
abbrev PlannedList (F : Type) := Label F × List Planned

theorem poly_flatMapWith {A X Y : Type} [Codec A] [Codec X] [Codec Y] [Inhabited A] [Inhabited X]
    {f : X → List A} {g : X × A → List Y} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => (f x).flatMap (fun j => g (x, j))) := by
  convert poly_flatten (poly_mapWith hf hg) using 1
  funext x
  induction f x with
  | nil => rfl
  | cons j js ih => simp only [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]

def reqSite (K : Type) [Fintype K] (p : PublicClocks × Request) : SiteCode :=
  codedBase K (p.1.1.2.2.2.1, p.2.1.1)

@[fun_prop] private theorem reqSite_poly (K : Type) [Fintype K] : Poly (reqSite K) :=
  (show Poly (fun p : PublicClocks × Request => (p.1.1.2.2.2.1, p.2.1.1)) from
    by fun_prop).compose (codedBase_poly K)

def reqInterval (K : Type) [Fintype K] (p : PublicClocks × Request) : List P1Batch.Req :=
  let a := p.1.1
  intervalReqs (Fintype.card K) a.1 a.2.1 a.2.2.2.2.1 (reqSite K p).1.2

theorem reqInterval_length (K : Type) [Fintype K] (p : PublicClocks × Request) :
    (reqInterval K p).length = 4 := rfl

theorem reqInterval_poly (K : Type) [Fintype K] : Poly (reqInterval K) := by
  have hp : Poly (fun p : PublicClocks × Request =>
      (p.1.1.1, p.1.1.2.1, p.1.1.2.2.2.2.1, (reqSite K p).1.2)) := by
    fun_prop
  exact hp.compose (intervalReqs_poly (Fintype.card K))

def witnessRequests {F : Type} (K : Type) [Fintype K] (p : PublicClocks × Offered F) :
    List P1Batch.Req :=
  p.2.2.flatMap fun q => reqInterval K (p.1, q)

theorem witnessRequests_poly {F : Type} [Fintype F] [Inhabited (Label F)] (K : Type) [Fintype K] :
    Poly (witnessRequests (F := F) K) := by
  have hr : Poly (fun z : (PublicClocks × Offered F) × Request => reqInterval K (z.1.1, z.2)) :=
    (show Poly (fun z : (PublicClocks × Offered F) × Request => (z.1.1, z.2)) from by fun_prop).compose (reqInterval_poly K)
  exact poly_flatMapWith (by fun_prop) hr

def planAt (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (p : (PublicClocks × List Request × List (List Bool)) × ℕ) : Planned :=
  let q := readAt ((0, 0), [], []) p.1.2.1 p.2
  let a := p.1.1
  (headerPlan V tape cross ((a, reqSite V.K (a, q)), (q.1.2, chunkAt (p.1.2.2, p.2))), q.2)

theorem planAt_poly (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) {cross : CrossIn → Bool}
    (hc : Poly cross) : Poly (planAt V tape cross) := by
  have hq : Poly (fun p : ((PublicClocks × List Request × List (List Bool)) × ℕ) => readAt ((0, 0), [], []) p.1.2.1 p.2) := by fun_prop
  let q (p : ((PublicClocks × List Request × List (List Bool)) × ℕ)) : Request := readAt ((0, 0), [], []) p.1.2.1 p.2
  have hq' : Poly q := hq
  have hs := ((show Poly (fun p : ((PublicClocks × List Request × List (List Bool)) × ℕ) => p.1.1) from by fun_prop).pair hq').compose (reqSite_poly V.K)
  have ht := (show Poly (fun p : ((PublicClocks × List Request × List (List Bool)) × ℕ) => (p.1.2.2, p.2)) from by fun_prop).compose chunkAt_poly
  have hi : Poly (fun p : ((PublicClocks × List Request × List (List Bool)) × ℕ) => ((p.1.1, reqSite V.K (p.1.1, q p)), ((q p).1.2, chunkAt (p.1.2.2, p.2)))) :=
    ((show Poly (fun p : ((PublicClocks × List Request × List (List Bool)) × ℕ) => p.1.1) from by fun_prop).pair hs).pair
      ((hq'.fstCompose.sndCompose).pair ht)
  exact (hi.compose (headerPlan_poly V tape hc)).pair hq'.sndCompose

def planHeaders {F : Type} (V : FiniteMultiTapeMachine) (tape : V.K → ℕ) (cross : CrossIn → Bool)
    (p : (PublicClocks × Offered F) × List (List Bool)) : PlannedList F :=
  (p.1.2.1, (List.range p.1.2.2.length).map fun j =>
    planAt V tape cross ((p.1.1, p.1.2.2, p.2), j))

theorem planHeaders_poly {F : Type} [Fintype F] [Inhabited (Label F)] (V : FiniteMultiTapeMachine) (tape : V.K → ℕ)
    {cross : CrossIn → Bool} (hc : Poly cross) :
    Poly (planHeaders (F := F) V tape cross) := by
  have hn := (show Poly (fun p : ((PublicClocks × Offered F) × List (List Bool)) => p.1.2.2) from by fun_prop).compose range_length_poly
  have hp := (show Poly (fun z : ((PublicClocks × Offered F) × List (List Bool)) × ℕ => ((z.1.1.1, z.1.1.2.2, z.1.2), z.2)) from
    by fun_prop).compose (planAt_poly V tape hc)
  exact (show Poly (fun p : ((PublicClocks × Offered F) × List (List Bool)) => p.1.2.1) from by fun_prop).pair (poly_mapWith hn hp)

def reqPins (p : Tally × Planned) : List P1Batch.Req :=
  (List.range p.1.length).map fun j => pinReq (readAt (.inl 0) p.2.1.2 j)

theorem reqPins_length (p : Tally × Planned) : (reqPins p).length = p.1.length := by
  simp only [reqPins, List.length_map, List.length_range]

theorem reqPins_poly : Poly reqPins := by
  have hr := (show Poly (fun p : Tally × Planned => p.1) from by fun_prop).compose range_length_poly
  have hq : Poly (fun p : (Tally × Planned) × ℕ => readAt (.inl 0) p.1.2.1.2 p.2) := by fun_prop
  exact poly_mapWith hr (hq.compose pinReq_poly)

def pinRequests {F : Type} (p : PublicClocks × PlannedList F) : List P1Batch.Req :=
  p.2.2.flatMap fun q => reqPins (p.1.2.2.1, q)

theorem pinRequests_poly {F : Type} [Fintype F] [Inhabited (Label F)] : Poly (pinRequests (F := F)) := by
  have hp := (show Poly (fun z : (PublicClocks × PlannedList F) × Planned => (z.1.1.2.2.1, z.2)) from by fun_prop).compose reqPins_poly
  exact poly_flatMapWith (by fun_prop) hp

def pinReply (V : FiniteMultiTapeMachine)
    (z : (List PinQuery × List (List Bool) × ℕ) × ℕ) : Tally :=
  let q := readAt (.inl 0) z.1.1 z.2
  let bits := readAt [] z.1.2.1 (z.1.2.2 + z.2)
  tally (min (resolvePin V q bits) (Fintype.card V.Γ))

private theorem pinReply_poly (V : FiniteMultiTapeMachine) : Poly (pinReply V) := by
  have h : Poly (fun z : ((List PinQuery × List (List Bool) × ℕ) × ℕ) =>
      (readAt (.inl 0) z.1.1 z.2, readAt [] z.1.2.1 (z.1.2.2 + z.2))) := by fun_prop
  exact P1ProgEng.SolKWR.poly_tallyMin (h.compose (resolvePin_poly V)) (Code.Poly.const _) (Dom.const _ _)

def entryAt (V : FiniteMultiTapeMachine)
    (p : (Tally × List Planned × List (List Bool)) × ℕ) : EntryCode :=
  let plan := readAt (([], []), [], []) p.1.2.1 p.2
  let offset := p.1.1.length * p.2
  (plan.1.1 ++ (List.range plan.1.2.length).map (fun j => pinReply V ((plan.1.2, p.1.2.2, offset), j)),
    plan.2)

theorem entryAt_poly (V : FiniteMultiTapeMachine) : Poly (entryAt V) := by
  let f (p : ((Tally × List Planned × List (List Bool)) × ℕ)) : Planned := readAt (([], []), [], []) p.1.2.1 p.2
  have hf : Poly f := by unfold f; fun_prop
  have hs := hf.fstCompose.sndCompose
  have hn := hs.compose range_length_poly
  have hq : Poly (fun p : ((Tally × List Planned × List (List Bool)) × ℕ) × ℕ => (f p.1).1.2) := Easy.fst.poly.compose hs
  have hr : Poly (fun p : ((Tally × List Planned × List (List Bool)) × ℕ) × ℕ => (p.1.1.2.2, p.1.1.1.length * p.1.2, p.2)) := by fun_prop
  have hv : Poly (fun p : ((Tally × List Planned × List (List Bool)) × ℕ) × ℕ => (p.1.1.2.2, p.1.1.1.length * p.1.2)) := hr.fstCompose.pair hr.sndCompose.fstCompose
  have ht : Poly (fun p : ((Tally × List Planned × List (List Bool)) × ℕ) × ℕ => (((f p.1).1.2, p.1.1.2.2, p.1.1.1.length * p.1.2), p.2)) :=
    (hq.pair hv).pair Easy.snd.poly
  exact (Code.Poly.app hf.fstCompose.fstCompose (poly_mapWith hn (ht.compose (pinReply_poly V)))).pair
    hf.sndCompose

def resolveEntries {F : Type} (V : FiniteMultiTapeMachine)
    (p : (PublicClocks × PlannedList F) × List (List Bool)) : Label F × List EntryCode :=
  (p.1.2.1, (List.range p.1.2.2.length).map fun j =>
    entryAt V ((p.1.1.2.2.1, p.1.2.2, p.2), j))

theorem resolveEntries_poly {F : Type} [Fintype F] [Inhabited (Label F)] (V : FiniteMultiTapeMachine) :
    Poly (resolveEntries (F := F) V) := by
  have hn := (show Poly (fun p : ((PublicClocks × PlannedList F) × List (List Bool)) => p.1.2.2) from by fun_prop).compose range_length_poly
  have hp := (show Poly (fun z : ((PublicClocks × PlannedList F) × List (List Bool)) × ℕ => ((z.1.1.1.2.2.1, z.1.1.2.2, z.1.2), z.2)) from
    by fun_prop).compose (entryAt_poly V)
  exact (show Poly (fun p : ((PublicClocks × PlannedList F) × List (List Bool)) => p.1.2.1) from by fun_prop).pair (poly_mapWith hn hp)

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.planHeaders_poly
#print axioms P1SolF0R.SolReader.resolveEntries_poly
