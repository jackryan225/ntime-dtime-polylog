import P1SolCone.TerminalSpanProgram

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly
attribute [local fun_prop] terminalIncidenceKeys_poly cachedTerminalArcs_poly cachedArcSpan_poly

@[fun_prop] theorem poly_le {X : Type} [Codec X] {f g : X → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x ≤ g x)) := by
  have h := (poly_lt hg hf).compose (Easy.finite Bool.not).poly
  convert h using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [Nat.not_lt]

def terminalHeaderOK (h : TerminalHeader) : Bool :=
  decide (packetNat h.2.2.2.2.1 2 ≤ h.2.1) &&
    decide (h.2.2.2.1 < terminalBases h * terminalLanes h)

theorem terminalHeaderOK_poly : Poly terminalHeaderOK := by
  unfold terminalHeaderOK
  have a : Poly (fun h : TerminalHeader => decide (packetNat h.2.2.2.2.1 2 ≤ h.2.1)) := by fun_prop
  have b : Poly (fun h : TerminalHeader => decide (h.2.2.2.1 < terminalBases h * terminalLanes h)) := by fun_prop
  exact (a.pair b).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

theorem terminalHeaderOK_eq (D : Dims) (m w v : ℕ) (clock : Tally) :
    terminalHeaderOK (actualTerminalHeader D m w v clock) =
      decide (D.fixedLen ≤ m ∧ v < (D.lv D.top).bases * (D.lv D.top).lanes) := by
  have hfixed : packetNat (phaseFormat D D.top) 2 = D.fixedLen := by rw [packetNat_phaseFormat]; rfl
  unfold terminalHeaderOK
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, terminalBases_actual, terminalLanes_actual]
  change (packetNat (phaseFormat D D.top) 2 ≤ m ∧ _) ↔ _
  rw [hfixed]
  rfl

def terminalArcOK (h : TerminalHeader) (a : ArcCode) : Bool :=
  decide (a.1 < terminalBases h) &&
    (decide (a.2.1 < terminalLanes h) && decide (a.2.2 < terminalSlots h))

theorem terminalArcOK_poly : Poly (fun p : TerminalHeader × ArcCode => terminalArcOK p.1 p.2) := by
  unfold terminalArcOK
  let conj := (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly
  have a : Poly (fun p : TerminalHeader × ArcCode => decide (p.2.1 < terminalBases p.1)) := by fun_prop
  have b : Poly (fun p : TerminalHeader × ArcCode => decide (p.2.2.1 < terminalLanes p.1)) := by fun_prop
  have c : Poly (fun p : TerminalHeader × ArcCode => decide (p.2.2.2 < terminalSlots p.1)) := by fun_prop
  exact (a.pair ((b.pair c).compose conj)).compose conj

theorem terminalArcOK_eq (D : Dims) (m w v : ℕ) (clock : Tally) (a : ArcCode) :
    terminalArcOK (actualTerminalHeader D m w v clock) a = arcValid (D.lv D.top) a := by
  apply Bool.eq_iff_iff.mpr
  simp only [terminalArcOK, arcValid, terminalBases_actual, terminalLanes_actual, terminalSlots_actual,
    Bool.and_eq_true, decide_eq_true_eq]

def terminalSpanOK (h : TerminalHeader) (s : Span) : Bool :=
  spanValid h.2.1 s && decide (s.2 ≤ h.2.2.1)

theorem terminalSpanOK_poly : Poly (fun p : TerminalHeader × Span => terminalSpanOK p.1 p.2) := by
  unfold terminalSpanOK spanValid
  have a : Poly (fun p : TerminalHeader × Span => decide (p.2.1 + p.2.2 ≤ p.1.2.1)) := by fun_prop
  have b : Poly (fun p : TerminalHeader × Span => decide (p.2.2 ≤ p.1.2.2.1)) := by fun_prop
  exact (a.pair b).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

/-- Check all fields of a partially assembled terminal read without expanding payload words. -/
theorem poly_allParameter {X A : Type} [Codec X] [Inhabited X] [Codec A] [Inhabited A] {ls : X → List A}
    {p : X × A → Bool} (hls : Poly ls) (hp : Poly p) :
    Poly (fun x => (ls x).all fun a => p (x,a)) := by
  simpa only [List.all_map, Function.comp_def] using
    (poly_mapParameter hls hp).compose (poly_allList (Code.Poly.identity (X := Bool)))

/-- Check the displacement separately, since a malformed displacement is a decoding failure. -/
def cachedDispOK (h : TerminalHeader) (c : FieldCache) : Bool :=
  (capRange (h.1, terminalSlots h)).all fun k =>
    decide (c.read (Mem.inDisp.toNat, (terminalPos h).1 * terminalSlots h + k) < terminalLanes h)

theorem cachedDispOK_poly : Poly (fun p : TerminalHeader × FieldCache => cachedDispOK p.1 p.2) := by
  unfold cachedDispOK
  have rng : Poly (fun p : TerminalHeader × FieldCache => capRange (p.1.1, terminalSlots p.1)) :=
    (show Poly (fun p : TerminalHeader × FieldCache => (p.1.1,terminalSlots p.1)) from by fun_prop).compose capRange_poly
  have field : Poly (fun q : (TerminalHeader × FieldCache) × ℕ =>
      (q.1.2, Mem.inDisp.toNat, (terminalPos q.1.1).1 * terminalSlots q.1.1 + q.2)) := by fun_prop
  have lanes : Poly (fun q : (TerminalHeader × FieldCache) × ℕ => terminalLanes q.1.1) := by fun_prop
  exact poly_allParameter rng (poly_lt (field.compose fieldCache_read_poly) lanes)

theorem cachedDispOK_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally) (cache : FieldCache)
    (hc : (D.lv D.top).slots ≤ clock.length)
    (he : ∀ k ∈ terminalIncidenceKeys (actualTerminalHeader D u.length w v clock),
      cache.read k = readField D u (terminalPhysicalKey D k).1 (terminalPhysicalKey D k).2) :
    cachedDispOK (actualTerminalHeader D u.length w v clock) cache = terminalDispValid D u v := by
  let h := actualTerminalHeader D u.length w v clock
  let L := D.lv D.top
  have hs : terminalSlots h = L.slots := terminalSlots_actual ..
  have hl : terminalLanes h = L.lanes := terminalLanes_actual ..
  have hr : capRange (h.1,terminalSlots h) = List.range L.slots := by
    change List.range (min (terminalSlots h) clock.length) = _
    rw [hs, min_eq_left hc]
  have hp : (terminalPos h).1 = v / L.lanes := by
    unfold terminalPos
    rw [hl]
    rfl
  change cachedDispOK h cache = _
  unfold cachedDispOK terminalDispValid
  rw [hr, hs, hl, hp]
  have same (k : ℕ) (hk : k ∈ List.range L.slots) :
      cache.read (Mem.inDisp.toNat, v / L.lanes * L.slots + k) =
        rdInDisp D u D.top (v / L.lanes) k := by
    let i := v / L.lanes * L.slots + k
    have mem : (Mem.inDisp.toNat,i) ∈ terminalIncidenceKeys h := by
      unfold terminalIncidenceKeys
      rw [hr]
      refine List.mem_flatMap.mpr ⟨k,hk,?_⟩
      rw [hs, hp]
      simp [i]
    rw [he _ mem]
    rfl
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro r k hk
    simpa only [same k hk] using r k hk
  · intro r k hk
    simpa only [same k hk] using r k hk

end P1SolCone.SolCone
