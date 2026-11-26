import P1ProgDir.C4ProgPanel
import P1ChkDir.C4Wired

namespace P1ProgDir.SolC4

open P1Net P1ChkDir P1Wit
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}

def startReq (D : Dims) (m j tape : ℕ) : P1Batch.Req :=
  fieldReq m D secStart (j * D.r + tape)

def ownerReq (D : Dims) (m j tape δ : ℕ) (forward : Bool) : P1Batch.Req :=
  fieldReq m D (if forward then secNext else secPrev) ((j * D.r + tape) * 3 + δ)

def nullReq : P1Batch.Req := ([], [])

theorem nullReq_value (u : List Bool) : P1Batch.bval (P1Batch.fetch u nullReq) = 0 := rfl

/-- A nonzero owner code outside the range of big intervals is decoded as absent. -/
def decodedOwner (I raw : ℕ) : Option (Fin I) := (ownOfN I raw).getD none

theorem decodedOwner_eq_some {I raw : ℕ} {j : Fin I} :
    decodedOwner I raw = some j ↔ raw = (j : ℕ) + 1 := by
  unfold decodedOwner ownOfN
  split
  · rename_i hz
    change none = some j ↔ raw = (j : ℕ) + 1
    constructor
    · intro h
      cases h
    · intro h
      omega
  · rename_i hz
    split
    · simp only [Option.getD_some, Option.some.injEq, Fin.ext_iff]
      omega
    · rename_i hj
      change none = some j ↔ raw = (j : ℕ) + 1
      have hi := j.isLt
      constructor
      · intro h
        cases h
      · intro h
        omega

/-- The first scan reads a start block and owner code at the queried port. -/
def firstReqs (D : Dims) (τ : K → ℕ) (m : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) : List P1Batch.Req :=
  match portQuery y.1.2 with
  | none => []
  | some (forward, k, δ) =>
    [startReq D m y.1.1 (τ k), ownerReq D m y.1.1 (τ k) δ forward]

theorem firstReqs_address (D : Dims) (τ : K → ℕ) (m : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) :
    ∀ q ∈ firstReqs D τ m y, P1Batch.bval q.1 ≤ m := by
  intro q hq
  unfold firstReqs at hq
  split at hq
  · cases hq
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact fieldReq_address _ _ _ _
    · rcases List.mem_singleton.mp hq with rfl
      exact fieldReq_address _ _ _ _

/-- A start block at the named owner, with the owner range checked first. -/
def secondReq (D : Dims) (τ : K → ℕ) (m : ℕ)
    (l : Loc K h) (owner : ℕ) : P1Batch.Req :=
  match portQuery l, decodedOwner D.I owner with
  | some (_, k, _), some j => startReq D m j (τ k)
  | _, _ => nullReq

theorem secondReq_address (D : Dims) (τ : K → ℕ) (m : ℕ) (l : Loc K h) (owner : ℕ) :
    P1Batch.bval (secondReq D τ m l owner).1 ≤ m := by
  unfold secondReq
  split
  · exact fieldReq_address _ _ _ _
  · exact Nat.zero_le m

structure PortReads where
  start : ℕ
  owner : ℕ
  farStart : ℕ

def readPort (D : Dims) (τ : K → ℕ) (u : List Bool)
    (y : (Fin D.I × Loc K h) × Bool) : PortReads :=
  let rs := (firstReqs D τ u.length y).map (P1Batch.fetch u)
  let owner := P1Batch.bval (rs.getD 1 [])
  ⟨P1Batch.bval (rs.getD 0 []), owner,
    P1Batch.bval (P1Batch.fetch u (secondReq D τ u.length y.1.2 owner))⟩

theorem readPort_eq (D : Dims) (τ : K → ℕ) (u : List Bool)
    (y : (Fin D.I × Loc K h) × Bool)
    {nxt : Bool} {k : K} {δ : Fin 3} (hp : portQuery y.1.2 = some (nxt, k, δ)) :
    let p := readPort D τ u y
    p.start = rdStart D u y.1.1 (τ k) ∧
    p.owner = (if nxt then rdNext D u y.1.1 (τ k) δ else rdPrev D u y.1.1 (τ k) δ) ∧
    ∀ j, decodedOwner D.I p.owner = some j → p.farStart = rdStart D u j (τ k) := by
  unfold readPort firstReqs
  simp only [hp, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  constructor
  · exact fieldReq_value _ _ _ _
  constructor
  · cases nxt <;> exact fieldReq_value _ _ _ _
  · intro j hj
    simp only [secondReq, hp, hj]
    exact fieldReq_value _ _ _ _

def reconstructedSlot (h : ℕ) (p : PortReads) (δ : Fin 3) : Fin 3 :=
  finOfInt 3 (bigOf (2 ^ h) (unzigzag p.start) + (δ : ℤ) -
    bigOf (2 ^ h) (unzigzag p.farStart))

def interFrom (I h : ℕ) (p : PortReads) (ι : Fin I) (l : Loc K h) (s : Fin 4) :
    Option (Fin I × Loc K h × Fin 4) :=
  match l with
  | .portOut k δ =>
    if s = 1 then (decodedOwner I p.owner).map fun j => (j, .portIn k (reconstructedSlot h p δ), 1) else none
  | .portIn k δ =>
    if s = 1 then (decodedOwner I p.owner).map fun j => (j, .portOut k (reconstructedSlot h p δ), 1) else none
  | .eOut => if s = 1 then (colSucc ι).map fun j => (j, .eIn, 1) else none
  | .eIn => if s = 1 then (colPred ι).map fun j => (j, .eOut, 1) else none
  | _ => none

theorem interFrom_readPort (D : Dims) (τ : K → ℕ)
    (u : List Bool) (ι : Fin D.I) (l : Loc K h) (t : Bool) (s : Fin 4) :
    interFrom D.I h (readPort D τ u ((ι, l), t)) ι l s =
      interMateD (dirAt D τ D.I (2 ^ h)) u ι l s := by
  let L : DirLayout K D.I (2 ^ h) := dirAt D τ D.I (2 ^ h)
  let p := readPort D τ u ((ι, l), t)
  change interFrom D.I h p ι l s = interMateD L u ι l s
  have b (i : Fin D.I) (k : K) : bD L u i k = unzigzag (rdStart D u i (τ k)) := by
    simp only [bD, DirLayout.betaS, L, dirAt, zigCode, numCode_read, rdStart, readField,
      width_start, Option.getD_some]
  have hs (k : K) (δ : Fin 3) (nxt : Bool) (hq : portQuery l = some (nxt, k, δ)) :
      (if nxt then nD L u ι k δ else pD L u ι k δ) = decodedOwner D.I p.owner ∧
      ∀ j, decodedOwner D.I p.owner = some j →
        reconstructedSlot h p δ = slotD L u j k (portQD L u ι k δ) := by
    obtain ⟨hb, ho, hf⟩ := readPort_eq D τ u ((ι, l), t) hq
    change p.start = _ at hb
    change p.owner = _ at ho
    refine ⟨?_, fun j hj => ?_⟩
    · symm
      rw [ho]
      cases nxt
      · simp only [decodedOwner, pD, L, Bool.false_eq_true, ↓reduceIte]
        simp only [DirLayout.prevS, dirAt, ownCode, numCode_read, rdPrev, readField, width_prev]
      · simp only [decodedOwner, nD, L, ↓reduceIte]
        simp only [DirLayout.nextS, dirAt, ownCode, numCode_read, rdNext, readField, width_next]
    · have hfar := hf j hj
      change p.farStart = _ at hfar
      simp only [reconstructedSlot, slotD, portQD, b, hb, hfar]
      congr 1
      ring
  cases l with
  | portIn k δ =>
    have he := hs k δ false rfl
    change pD L u ι k δ = _ ∧ _ at he
    rw [interFrom, interMateD, he.1]
    split
    · cases hh : decodedOwner D.I p.owner with
      | none => rfl
      | some j => simp only [Option.map_some, he.2 j hh]
    · rfl
  | portOut k δ =>
    have he := hs k δ true rfl
    change nD L u ι k δ = _ ∧ _ at he
    rw [interFrom, interMateD, he.1]
    split
    · cases hh : decodedOwner D.I p.owner with
      | none => rfl
      | some j => simp only [Option.map_some, he.2 j hh]
    · rfl
  | _ => rfl

/-- The reconstructed partner function is needed only on the four half-edges
at the queried base. -/
noncomputable def mateFrom (p : PortReads) (q : (Fin I × Loc K h) × Fin 4) :
    Option ((Fin I × Loc K h) × Fin 4) :=
  match locMate q.1.2 q.2 with
  | some (l, s) => some ((q.1.1, l), s)
  | none => (interFrom I h p q.1.1 q.1.2 q.2).map fun r => ((r.1, r.2.1), r.2.2)

theorem mateFrom_readPort (D : Dims) (τ : K → ℕ)
    (u : List Bool) (y : (Fin D.I × Loc K h) × Bool) (s : Fin 4) :
    mateFrom (readPort D τ u y) (y.1, s) =
      netMateD (dirAt D τ D.I (2 ^ h)) u (y.1, s) := by
  rcases y with ⟨⟨ι, l⟩, t⟩
  unfold mateFrom netMateD
  dsimp only
  rw [interFrom_readPort D τ]
  cases locMate l s <;> rfl

theorem fieldsAt_readPort_iff {a : ℕ} (ha : 4 ≤ 2 ^ a) (D : Dims)
    (τ : K → ℕ) (u : List Bool) (Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) :
    (∀ p ∈ fieldsAt ha D (mateFrom (readPort D τ u y)) Wc Ws Wt y,
      readField D u p.1 p.2.1 = p.2.2) ↔
      C4 ha D (dirAt D τ D.I (2 ^ h)) u Wc Ws Wt y := by
  rw [fieldsAt_iff, C4]
  apply c4_congr_mate
  exact mateFrom_readPort D τ u y

def panelReqs (D : Dims) (m : ℕ) (fs : List (ℕ × ℕ × ℕ)) : List P1Batch.Req :=
  fs.map fun p => fieldReq m D p.1 p.2.1

theorem panelReqs_address (D : Dims) (m : ℕ) (fs : List (ℕ × ℕ × ℕ)) :
    ∀ q ∈ panelReqs D m fs, P1Batch.bval q.1 ≤ m := by
  intro q hq
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hq
  exact fieldReq_address _ _ _ _

def checkPanel (D : Dims) (u : List Bool) (fs : List (ℕ × ℕ × ℕ)) : Bool :=
  decide (((panelReqs D u.length fs).map (P1Batch.fetch u)).map P1Batch.bval = fs.map fun p => p.2.2)

theorem checkPanel_true (D : Dims) (u : List Bool) (fs : List (ℕ × ℕ × ℕ)) :
    checkPanel D u fs = true ↔ ∀ p ∈ fs, readField D u p.1 p.2.1 = p.2.2 := by
  simp only [checkPanel, decide_eq_true_eq, panelReqs, List.map_map, Function.comp_def, fieldReq_value]
  induction fs with
  | nil => simp
  | cons p fs ih => simp only [List.map_cons, List.cons.injEq, List.forall_mem_cons, ih]

/-- Readback specification for three scans. It uses the supplied layout and
never inspects the correctness of the witness trits or directory. -/
noncomputable def checkC4Readback {a : ℕ} (ha : 4 ≤ 2 ^ a) (D : Dims)
    (τ : K → ℕ) (u : List Bool) (Wc Ws Wt h i : ℕ) : Bool :=
  match baseAt K D.I h i with
  | none => true
  | some y =>
    let p := readPort D τ u y
    let fs := fieldsAt ha D (mateFrom p) Wc Ws Wt y
    checkPanel D u fs

theorem checkC4Readback_true {a : ℕ} (ha : 4 ≤ 2 ^ a) (D : Dims) (τ : K → ℕ)
    (u : List Bool) (Wc Ws Wt i : ℕ) :
    checkC4Readback ha D τ u Wc Ws Wt h i = true ↔
      C4F ha D (dirAt D τ D.I (2 ^ h)) u Wc Ws Wt i := by
  rw [c4f_at]
  unfold checkC4Readback
  cases hb : baseAt K D.I h i with
  | none => simp only [iff_true]
  | some y => rw [checkPanel_true, fieldsAt_readPort_iff ha D τ]

end P1ProgDir.SolC4
