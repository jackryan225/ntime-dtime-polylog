import P1SolCone.TerminalGuard
import P1SolCone.TerminalPayload

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly
attribute [local fun_prop] cachedTerminalArcs_poly cachedArcSpan_poly

def terminalArcWidths (h : TerminalHeader) (incidence : FieldCache) : List FieldKey :=
  let arcs := cachedTerminalArcs h incidence
  (arcs.1 ++ arcs.2).flatMap (fun a => terminalWidthKeys h a.1)

theorem terminalArcWidths_poly : Poly (fun p : TerminalHeader × FieldCache => terminalArcWidths p.1 p.2) := by
  unfold terminalArcWidths
  have arcs := cachedTerminalArcs_poly.compose Easy.append.poly
  have key : Poly (fun p : (TerminalHeader × FieldCache) × ArcCode => (p.1.1,p.2.1)) := by fun_prop
  exact (poly_mapParameter arcs (key.compose terminalWidthKeys_poly)).compose Easy.flatten.poly

def terminalFieldRequests (h : TerminalHeader) (ks : List FieldKey) : List P1Batch.Req :=
  ks.map (terminalFieldReq h)

theorem terminalFieldRequests_poly :
    Poly (fun p : TerminalHeader × List FieldKey => terminalFieldRequests p.1 p.2) := by
  have f : Poly (fun q : (TerminalHeader × List FieldKey) × FieldKey => (q.1.1,q.2)) := by fun_prop
  exact poly_mapParameter Easy.snd.poly (f.compose terminalFieldReq_poly)

theorem terminalFieldRequests_offsets (h : TerminalHeader) (ks : List FieldKey) :
    ∀ q ∈ terminalFieldRequests h ks, P1Batch.bval q.1 ≤ h.2.1 := by
  intro q hq
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
  exact terminalFieldReq_addr h k

/-- The polynomial calculation after the two metadata batches and before reading the actual half words. -/
def cachedTerminalSpans (h : TerminalHeader) (incidence widths : FieldCache) :
    Bool × (List Span × List Span) :=
  let arcs := cachedTerminalArcs h incidence
  let spans := (arcs.1.map (cachedArcSpan h widths), arcs.2.map (cachedArcSpan h widths))
  bif ((terminalHeaderOK h && cachedDispOK h incidence) &&
      (arcs.1 ++ arcs.2).all (terminalArcOK h)) &&
      (spans.1 ++ spans.2).all (terminalSpanOK h)
  then (true, spans) else (false, [], [])

theorem cachedTerminalSpans_poly :
    Poly (fun p : TerminalHeader × FieldCache × FieldCache => cachedTerminalSpans p.1 p.2.1 p.2.2) := by
  let U := TerminalHeader × FieldCache × FieldCache
  have head : Poly (fun p : U => p.1) := Easy.fst.poly
  have inc : Poly (fun p : U => (p.1,p.2.1)) := by dsimp [U]; fun_prop
  have arcs := inc.compose cachedTerminalArcs_poly
  have bothArcs := arcs.compose Easy.append.poly
  have key : Poly (fun p : U × ArcCode => (p.1.1,p.2)) := by dsimp [U]; fun_prop
  have testArcs := poly_allParameter bothArcs (key.compose terminalArcOK_poly)
  have getSpan : Poly (fun p : U × ArcCode => (p.1.1,p.1.2.2,p.2)) := by dsimp [U]; fun_prop
  have spans := (poly_mapParameter arcs.fstCompose (getSpan.compose cachedArcSpan_poly)).pair
    (poly_mapParameter arcs.sndCompose (getSpan.compose cachedArcSpan_poly))
  have spanKey : Poly (fun p : U × Span => (p.1.1,p.2)) := by dsimp [U]; fun_prop
  have testSpans := poly_allParameter (spans.compose Easy.append.poly) (spanKey.compose terminalSpanOK_poly)
  let conj := (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly
  have hd := ((head.compose terminalHeaderOK_poly).pair (inc.compose cachedDispOK_poly)).compose conj
  have test := (((hd.pair testArcs).compose conj).pair testSpans).compose conj
  exact Poly.choose test ((Code.Poly.const true).pair spans)
    (Code.Poly.const ((false, [], []) : Bool × List Span × List Span))

/-- Drop the non-coding failure flag only after the three batch stages have run. -/
def terminalSpanOption (s : Bool × List Span × List Span) : Option (List Span × List Span) :=
  bif s.1 then some s.2 else none

theorem cachedTerminalSpans_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally)
    (inc widths : FieldCache) (hc : (D.lv D.top).slots ≤ clock.length)
    (hc' : finArcs D ≤ clock.length)
    (hi : ∀ k ∈ terminalIncidenceKeys (actualTerminalHeader D u.length w v clock),
      inc.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2)
    (hw : ∀ k ∈ terminalArcWidths (actualTerminalHeader D u.length w v clock) inc,
      widths.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2)
    (hfix : D.fixedLen ≤ u.length) :
    terminalSpanOption (cachedTerminalSpans (actualTerminalHeader D u.length w v clock) inc widths) =
      terminalSpans D u w v := by
  let h := actualTerminalHeader D u.length w v clock
  let arcs := terminalArcCodes D u v
  let valid := (arcs.1 ++ arcs.2).all (arcValid (D.lv D.top))
  have ha : cachedTerminalArcs h inc = arcs := cachedTerminalArcs_eq D u w v clock hc inc hi
  have hd : cachedDispOK h inc = terminalDispValid D u v := cachedDispOK_eq D u w v clock inc hc hi
  have hh : terminalHeaderOK h = decide (v < (D.lv D.top).bases * (D.lv D.top).lanes) := by
    rw [terminalHeaderOK_eq]
    simp only [hfix, true_and]
  have hvalid : (arcs.1 ++ arcs.2).all (terminalArcOK h) = valid := by
    unfold valid
    apply List.all_congr
    · rfl
    · intro a
      exact terminalArcOK_eq D u.length w v clock a
  unfold cachedTerminalSpans terminalSpans
  dsimp only
  rw [ha, hd, hh, hvalid]
  by_cases hv : valid = true
  · have he (a : ArcCode) (hm : a ∈ arcs.1 ++ arcs.2) :
        cachedArcSpan h widths a = arcSpan D u a := by
      apply cachedArcSpan_eq D u w v clock widths a hc'
      · exact List.all_eq_true.mp hv a hm
      · intro k hk
        apply hw
        unfold terminalArcWidths
        rw [ha]
        exact List.mem_flatMap.mpr ⟨a,hm,hk⟩
    have ho : arcs.1.map (cachedArcSpan h widths) = arcs.1.map (arcSpan D u) :=
      List.map_congr_left (fun a hm => he a (List.mem_append_left _ hm))
    have hn : arcs.2.map (cachedArcSpan h widths) = arcs.2.map (arcSpan D u) :=
      List.map_congr_left (fun a hm => he a (List.mem_append_right _ hm))
    rw [ho, hn]
    let good := v < (D.lv D.top).bases * (D.lv D.top).lanes ∧
        terminalDispValid D u v = true ∧ valid = true ∧
        ((arcs.1.map (arcSpan D u)) ++ (arcs.2.map (arcSpan D u))).all (terminalSpanOK h) = true
    have hb : (((decide (v < (D.lv D.top).bases * (D.lv D.top).lanes) &&
        terminalDispValid D u v) && valid) &&
        ((arcs.1.map (arcSpan D u)) ++ (arcs.2.map (arcSpan D u))).all (terminalSpanOK h)) = true ↔ good := by
      simp only [good, Bool.and_eq_true, decide_eq_true_eq]
      tauto
    change terminalSpanOption _ =
      if good then some (arcs.1.map (arcSpan D u), arcs.2.map (arcSpan D u)) else none
    by_cases hgood : good
    · rw [hb.mpr hgood, ite_eq_left hgood]
      rfl
    · rw [Bool.eq_false_iff.mpr (mt hb.mp hgood), ite_eq_right hgood]
      rfl
  · have hfalse : valid = false := Bool.eq_false_iff.mpr hv
    rw [hfalse]
    simp [terminalSpanOption, arcs, valid, hv]

end P1SolCone.SolCone
