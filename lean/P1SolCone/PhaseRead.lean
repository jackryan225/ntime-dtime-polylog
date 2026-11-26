import P1SolCone.ConeFormat
import P1SolCone.FieldPrograms
import P1SolCone.BatchKeep

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

/-- Clock, binary witness length, phase index, queried child base and the two formatted rows. -/
abbrev PhaseHeader := Tally × ℕ × ℕ × ℕ × List Bits.Word

def actualPhaseHeader (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) : PhaseHeader :=
  (clock, u.length, l, y, phaseFormat D l)

/-- Physical keys agree with the C10 reader's offset/length pairs. The old row's raw readers
also use these keys at indices outside the declared arrays. -/
def phaseFieldKey (next : Bool) (m : Mem) (h : PhaseHeader) (i : ℕ) : FieldKey :=
  let p := (if next then 38 else 14) + 2 * m.toNat
  let w := packetNat h.2.2.2.2 (p + 1)
  (min h.2.1 (packetNat h.2.2.2.2 p + i * w), min h.1.length w)

@[fun_prop] theorem phaseFieldKey_poly (next : Bool) (m : Mem) :
    Poly (fun p : PhaseHeader × ℕ => phaseFieldKey next m p.1 p.2) := by
  unfold phaseFieldKey
  dsimp only
  fun_prop

def phaseRequest (q : FieldKey) : P1Batch.Req := (bin q.1, bin q.2)

@[fun_prop] theorem phaseRequest_poly : Poly phaseRequest := by unfold phaseRequest; fun_prop

def phaseFieldAt (u : List Bool) (q : FieldKey) : ℕ := bitsVal ((u.drop q.1).take q.2)

theorem read_phaseFieldKey (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) (next : Bool) (m : Mem)
    (i : ℕ) (hw : D.width (secLev (if next then l+1 else l) m) ≤ clock.length) :
    phaseFieldAt u (phaseFieldKey next m (actualPhaseHeader D u l y clock) i) =
      readField D u (secLev (if next then l+1 else l) m) i := by
  let k := secLev (if next then l+1 else l) m
  have parts : (packetNat (phaseFormat D l) ((if next then 38 else 14) + 2*m.toNat),
      packetNat (phaseFormat D l) ((if next then 38 else 14) + 2*m.toNat + 1)) = (D.off k, D.width k) := by
    rw [packetNat_phaseFormat, packetNat_phaseFormat]
    cases next <;> cases m <;> rfl
  have ho := congrArg Prod.fst parts
  have hw' := congrArg Prod.snd parts
  dsimp only at ho hw'
  unfold phaseFieldAt phaseFieldKey readField readNat
  dsimp only [actualPhaseHeader]
  rw [ho, hw', min_eq_right hw]
  generalize D.off k + i * D.width k = j
  by_cases hj : j ≤ u.length
  · rw [min_eq_right hj]
  · rw [min_eq_left (Nat.le_of_not_le hj), List.drop_length,
      List.drop_eq_nil_of_le (Nat.le_of_not_le hj)]

theorem phaseFieldKey_bounds (next : Bool) (m : Mem) (h : PhaseHeader) (i : ℕ) :
    (phaseFieldKey next m h i).1 ≤ h.2.1 ∧ (phaseFieldKey next m h i).2 ≤ h.1.length :=
  ⟨min_le_left _ _, min_le_left _ _⟩

def fetchPhaseFields (u : List Bool) (keys : List FieldKey) : FieldCache :=
  fieldCache keys ((keys.map phaseRequest).map (P1Batch.fetch u))

theorem fetchPhaseFields_read (u : List Bool) (keys : List FieldKey) (q : FieldKey) (hq : q ∈ keys) :
    (fetchPhaseFields u keys).read q = phaseFieldAt u q := by
  unfold fetchPhaseFields
  rw [List.map_map, fieldCache_read_on _ _ _ hq]
  simp only [Function.comp_def, phaseRequest, phaseFieldAt, P1Batch.fetch, bval_bin]

theorem fetchPhaseFields_eq_map (u : List Bool) (keys : List FieldKey) :
    fetchPhaseFields u keys = keys.map (fun k => (k,phaseFieldAt u k)) := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [fetchPhaseFields, fieldCache, List.map_cons, List.zip_cons_cons, phaseRequest,
      phaseFieldAt, P1Batch.fetch, bval_bin] at ih ⊢
    rw [ih]

/-- For one phase, retain the complete ordered raw incidence at every queried base. -/
def rawSlotFields (h : PhaseHeader) (y k : ℕ) : List FieldKey :=
  let i := y * packetNat h.2.2.2.2 4 + k
  [phaseFieldKey false .outAddr h i, phaseFieldKey false .outDisp h i, phaseFieldKey false .outFar h i,
    phaseFieldKey false .inAddr h i, phaseFieldKey false .inDisp h i, phaseFieldKey false .inFar h i]

theorem rawSlotFields_poly : Poly (fun p : PhaseHeader × ℕ × ℕ => rawSlotFields p.1 p.2.1 p.2.2) := by
  unfold rawSlotFields
  let inf (p : PhaseHeader × ℕ × ℕ) := p.2.1 * packetNat p.1.2.2.2.2 4 + p.2.2
  have p : Poly (fun q : PhaseHeader × ℕ × ℕ => (q.1, inf q)) := by unfold inf; fun_prop
  have one (m : Mem) : Poly (fun q : PhaseHeader × ℕ × ℕ => phaseFieldKey false m q.1 (inf q)) :=
    p.compose (phaseFieldKey_poly false m)
  have cons {f : PhaseHeader × ℕ × ℕ → FieldKey} {g : PhaseHeader × ℕ × ℕ → List FieldKey}
      (hf : Poly f) (hg : Poly g) : Poly (fun p => f p :: g p) := (hf.pair hg).compose Poly.cons
  exact cons (one .outAddr) (cons (one .outDisp) (cons (one .outFar)
    (cons (one .inAddr) (cons (one .inDisp) (cons (one .inFar) (Code.Poly.const []))))))

def rawSlots (h : PhaseHeader) : List ℕ := capRange (h.1, packetNat h.2.2.2.2 4)

@[fun_prop] theorem rawSlots_poly : Poly rawSlots := by
  unfold rawSlots
  exact (show Poly (fun h : PhaseHeader => (h.1,packetNat h.2.2.2.2 4)) from by fun_prop).compose capRange_poly

theorem rawSlots_eq (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally)
    (hc : (D.lv l).slots ≤ clock.length) :
    rawSlots (actualPhaseHeader D u l y clock) = List.range (D.lv l).slots := by
  have hs : packetNat (phaseFormat D l) 4 = (D.lv l).slots := by rw [packetNat_phaseFormat]; rfl
  change List.range (min (packetNat (phaseFormat D l) 4) clock.length) = _
  rw [hs, min_eq_left hc]

def rawBaseFields (h : PhaseHeader) (y : ℕ) : List FieldKey :=
  phaseFieldKey false .colour h y :: phaseFieldKey false .offset h y ::
    (rawSlots h).flatMap (rawSlotFields h y)

theorem rawBaseFields_poly : Poly (fun p : PhaseHeader × ℕ => rawBaseFields p.1 p.2) := by
  unfold rawBaseFields
  have slots := (Easy.fst.poly : Poly (Prod.fst : PhaseHeader × ℕ → PhaseHeader)).compose rawSlots_poly
  have lookup : Poly (fun p : (PhaseHeader × ℕ) × ℕ => (p.1.1,p.1.2,p.2)) := by fun_prop
  have rest := (poly_mapParameter slots (lookup.compose rawSlotFields_poly)).compose Easy.flatten.poly
  exact ((phaseFieldKey_poly false .colour).pair
    (((phaseFieldKey_poly false .offset).pair rest).compose Poly.cons)).compose Poly.cons

def rawRead (h : PhaseHeader) (cache : FieldCache) (m : Mem) (i : ℕ) : ℕ :=
  cache.read (phaseFieldKey false m h i)

theorem rawRead_poly (m : Mem) :
    Poly (fun p : PhaseHeader × FieldCache × ℕ => rawRead p.1 p.2.1 m p.2.2) := by
  unfold rawRead
  have key : Poly (fun p : PhaseHeader × FieldCache × ℕ => (p.1,p.2.2)) := by fun_prop
  exact ((show Poly (fun p : PhaseHeader × FieldCache × ℕ => p.2.1) from by fun_prop).pair
    (key.compose (phaseFieldKey_poly false m))).compose fieldCache_read_poly

def rawIncidence (h : PhaseHeader) (cache : FieldCache) (m : Mem) (y k : ℕ) : ℕ :=
  rawRead h cache m (y * packetNat h.2.2.2.2 4 + k)

theorem rawIncidence_poly (m : Mem) :
    Poly (fun p : (PhaseHeader × FieldCache) × ℕ × ℕ => rawIncidence p.1.1 p.1.2 m p.2.1 p.2.2) := by
  unfold rawIncidence
  exact (show Poly (fun p : (PhaseHeader × FieldCache) × ℕ × ℕ =>
    (p.1.1,p.1.2,p.2.1 * packetNat p.1.1.2.2.2.2 4 + p.2.2)) from by fun_prop).compose (rawRead_poly m)

def rawNeighbors (h : PhaseHeader) (cache : FieldCache) (y : ℕ) : List ℕ :=
  (rawSlots h).map (rawIncidence h cache .outAddr y) ++
    (rawSlots h).map (rawIncidence h cache .inAddr y)

theorem rawNeighbors_poly : Poly (fun p : PhaseHeader × FieldCache × ℕ => rawNeighbors p.1 p.2.1 p.2.2) := by
  unfold rawNeighbors
  have l := (Easy.fst.poly : Poly (Prod.fst : PhaseHeader × FieldCache × ℕ → PhaseHeader)).compose rawSlots_poly
  have h : Poly (fun p : (PhaseHeader × FieldCache × ℕ) × ℕ => ((p.1.1,p.1.2.1),p.1.2.2,p.2)) := by fun_prop
  exact (poly_mapParameter l (h.compose (rawIncidence_poly .outAddr))).app
    (poly_mapParameter l (h.compose (rawIncidence_poly .inAddr)))

end P1SolCone.SolCone
