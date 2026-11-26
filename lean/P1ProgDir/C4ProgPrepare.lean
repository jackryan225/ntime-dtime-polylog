import P1ProgDir.C4ProgGeometry
import P1ProgDir.C4ProgPipeline

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Net P1Wit P1ChkDir
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {h a : ℕ}

def packNumber (n : ℕ) : Word := Length.born n

theorem value_packNumber (n : ℕ) : value (packNumber n) = n :=
  (bval_eq_value _).symm.trans (bval_canonical n)

def packSection (D : Dims) (s : ℕ) : SectionWord := (packNumber (D.off s), packNumber (D.width s))

def sectionTest (D : Dims) (m s i ordinary : ℕ) (changeAddr : Bool) (linked : ℕ) :
    P1Batch.Req × Expectation :=
  (fieldReq m D s i, packNumber ordinary, changeAddr, packNumber linked)

def unchangedTest (D : Dims) (m s i v : ℕ) : P1Batch.Req × Expectation :=
  sectionTest D m s i v false v

def portActive (l : Loc K h) (slot : ℕ) : Bool := (portQuery l).isSome && decide (slot = 1)

noncomputable def slotPlan (D : Dims) (m : ℕ) (Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) (k : Fin (2 ^ a)) : List (P1Batch.Req × Expectation) :=
  let fallback := slotView Wc Ws Wt ⟨0, 0, 0⟩ y k
  let active := portActive y.1.2 k
  let address := addrL y
  let j := address * (D.lv 0).slots + k
  let payload := if y.2 then 0 else baseWidth Wc Ws Wt y.1.2 1
  let ownedWidth := if active then payload else fallback.2.2.2
  [sectionTest D m (secLev 0 .outAddr) j fallback.1 active fallback.1,
   unchangedTest D m (secLev 0 .outDisp) j fallback.2.1,
   unchangedTest D m (secLev 0 .outFar) j fallback.2.2.1,
   sectionTest D m (secLev 0 .inAddr) j fallback.1 active fallback.1,
   unchangedTest D m (secLev 0 .inDisp) j fallback.2.1,
   unchangedTest D m (secLev 0 .inFar) j fallback.2.2.1] ++
  (List.range (2 ^ h)).map fun l =>
    sectionTest D m (secLev 0 .width) ((address * (D.lv 0).lanes + l) * (D.lv 0).slots + k)
      fallback.2.2.2 false ownedWidth

noncomputable def packPort (D : Dims) (τ : K → ℕ) (l : Loc K h) (t : Bool) :
    OwnerGeometry × StartGeometry :=
  let idx := (packNumber (D.I), tally h)
  let count := packNumber (locCount K h)
  let twin := packNumber t.toNat
  let start := packSection D secStart
  match portQuery l with
  | none => ((idx, count, [], [], twin), packNumber D.r, [], start)
  | some (nxt, k, δ) =>
    let remote := if nxt then locNum K h (.portIn k 0) else locNum K h (.portOut k 0)
    ((idx, count, packNumber remote, packNumber δ, twin), packNumber D.r, packNumber (τ k), start)

noncomputable def prepareAt (D : Dims) (τ : K → ℕ) (a m Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) : ReadPlan :=
  let info := packPort D τ y.1.2 y.2
  (packNumber m, info.1, info.2, firstReqs D τ m y,
    (List.finRange (2 ^ a)).flatMap (slotPlan D m Wc Ws Wt y))

noncomputable def prepareC4 (D : Dims) (τ : K → ℕ) (a h m Wc Ws Wt i : ℕ) : ReadPlan :=
  match baseAt K D.I h i with
  | none => (packNumber m, (([], []), [], [], [], []), ([], [], ([], [])), [], [])
  | some y => prepareAt D τ a m Wc Ws Wt y

theorem prepareC4_length (D : Dims) (τ : K → ℕ) (a h m Wc Ws Wt i : ℕ) :
    value (prepareC4 D τ a h m Wc Ws Wt i).1 = m := by
  unfold prepareC4
  split <;> simp only [prepareAt, value_packNumber]

theorem ownerOK_decoded (I : ℕ) (w : Word) :
    ownerOK (packNumber I, w) = (decodedOwner I (value w)).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [ownerOK_true, value_packNumber]
  constructor
  · intro h
    let j : Fin I := ⟨value w - 1, by omega⟩
    have hj : decodedOwner I (value w) = some j := decodedOwner_eq_some.mpr (by
      dsimp only [j]
      omega)
    rw [hj]
    rfl
  · intro h
    cases hj : decodedOwner I (value w) with
    | none => simp only [hj, Option.isSome_none, reduceCtorEq] at h
    | some j =>
      have e := decodedOwner_eq_some.mp hj
      have hj' := j.isLt
      omega

theorem ownerIndex_value (w : Word) : value (ownerIndex w) = value w - 1 := by
  rw [ownerIndex, value_wordSub]
  rfl

theorem ownerAddress_value (I localCount h opposite : ℕ) (δ : Fin 3) (t : Bool) (near raw far : Word) :
    value (ownerAddress (((packNumber I, tally h), packNumber localCount, packNumber opposite,
      packNumber δ, packNumber t.toNat), near, raw, far)) =
      t.toNat + 2 * (opposite + (reconstructedSlot h ⟨value near, value raw, value far⟩ δ : ℕ) +
        localCount * (value raw - 1)) := by
  unfold ownerAddress
  simp only [add_val, value_cons, d0, Nat.zero_add, Binary.school_exact, value_packNumber,
    ownerIndex_value, value_wordPortSlot, reconstructedSlot, finOfInt, Fin.val_mk]
  omega

theorem clampReq_fetch (u : Word) (m : Word) (q : P1Batch.Req) (hv : value m = u.length)
    (ha : P1Batch.bval q.1 ≤ u.length) :
    P1Batch.fetch u (clampReq (m, q)) = P1Batch.fetch u q := by
  unfold P1Batch.fetch clampReq
  simp only [bval_eq_value, value_wordMin, hv]
  rw [bval_eq_value] at ha
  rw [Nat.min_eq_right ha]

theorem firstScan_prepareAt (D : Dims) (τ : K → ℕ) (a Wc Ws Wt : ℕ) (u : Word)
    (y : (Fin D.I × Loc K h) × Bool) :
    (firstScan (prepareAt D τ a u.length Wc Ws Wt y)).2.map (P1Batch.fetch u) =
      (firstReqs D τ u.length y).map (P1Batch.fetch u) := by
  simp only [firstScan, prepareAt, polyPush, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro q hq
  exact clampReq_fetch _ _ _ (value_packNumber _) (firstReqs_address D τ u.length y q hq)

theorem secondWord_getD (l : List Word) : secondWord l = l.getD 1 [] := by
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl

theorem farRequest_prepareAt (D : Dims) (τ : K → ℕ) (a Wc Ws Wt : ℕ) (u : Word)
    (y : (Fin D.I × Loc K h) × Bool) :
    let p := prepareAt D τ a u.length Wc Ws Wt y
    let rs := (firstScan p).2.map (P1Batch.fetch u)
    P1Batch.bval (P1Batch.fetch u (farRequest (p, rs))) = (readPort D τ u y).farStart := by
  dsimp only
  rw [firstScan_prepareAt]
  unfold readPort
  cases hp : portQuery y.1.2 with
  | none =>
    have hz : ownerOK (packNumber D.I, []) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact (Nat.lt_irrefl 0) ((ownerOK_true _ _).mp h).1
    simp only [firstReqs, hp, List.map_nil, prepareAt, packPort, farRequest, secondWord, List.tail_nil,
      List.headD_nil, hz, Bool.cond_false, secondReq]
    rfl
  | some q =>
    rcases q with ⟨nxt, k, δ⟩
    let rs := (firstReqs D τ u.length y).map (P1Batch.fetch u)
    let owner := secondWord rs
    have hword : value owner = P1Batch.bval (rs.getD 1 []) := by
      simp only [owner, secondWord_getD, bval_eq_value]
    change P1Batch.bval (P1Batch.fetch u (farRequest (prepareAt D τ a u.length Wc Ws Wt y, rs))) =
      P1Batch.bval (P1Batch.fetch u (secondReq D τ u.length y.1.2 (P1Batch.bval (rs.getD 1 []))))
    rw [← hword]
    simp only [farRequest, prepareAt, packPort, hp, ← show owner = secondWord rs from rfl,
      ownerOK_decoded]
    cases ho : decodedOwner D.I (value owner) with
    | none => simp only [ho, Option.isSome_none, Bool.cond_false, secondReq, hp]; rfl
    | some j =>
      simp only [ho, Option.isSome_some, Bool.cond_true, secondReq, hp, startReq]
      rw [wordFieldReq_fetch _ _ secStart _ _ _ (value_packNumber _) (value_packNumber _) (value_packNumber _),
        fieldReq_value, add_val, Binary.school_exact, ownerIndex_value, value_packNumber, value_packNumber]
      have hj := decodedOwner_eq_some.mp ho
      rw [hj, Nat.add_sub_cancel]

theorem decodedOwner_zero (I : ℕ) : decodedOwner I 0 = none := by simp [decodedOwner, ownOfN]

private theorem slotView_fallback {I : ℕ} (Wc Ws Wt : ℕ) (p : PortReads)
    (y : (Fin I × Loc K h) × Bool) (slot : ℕ)
    (hf : portActive y.1.2 slot = true → decodedOwner I p.owner = none) :
    slotView Wc Ws Wt p y slot = slotView Wc Ws Wt ⟨0, 0, 0⟩ y slot := by
  rcases y with ⟨⟨i, l⟩, t⟩
  unfold slotView
  dsimp only
  split
  · rename_i hs
    congr 1
    simp only [ruleData_eq]
    have he : mateFrom p ((i, l), (⟨slot, hs⟩ : Fin 4)) =
        mateFrom ⟨0, 0, 0⟩ ((i, l), (⟨slot, hs⟩ : Fin 4)) := by
      unfold mateFrom
      dsimp only
      split
      · rfl
      · by_cases hk : slot = 1
        · subst slot
          cases l with
          | portIn k δ =>
            have ho := hf rfl
            simp only [interFrom, if_pos (show (⟨1, hs⟩ : Fin 4) = 1 from rfl), ho, decodedOwner_zero,
              Option.map_none]
          | portOut k δ =>
            have ho := hf rfl
            simp only [interFrom, if_pos (show (⟨1, hs⟩ : Fin 4) = 1 from rfl), ho, decodedOwner_zero,
              Option.map_none]
          | _ => rfl
        · have hk' : (⟨slot, hs⟩ : Fin 4) ≠ 1 := fun h => hk (congrArg Fin.val h)
          cases l <;> simp only [interFrom, if_neg hk']
    rw [he]
  · rfl

private theorem portSlotView {I : ℕ} (Wc Ws Wt : ℕ) (p : PortReads)
    (i j : Fin I) (l : Loc K h) (t nxt : Bool) (k : K) (δ : Fin 3)
    (hp : portQuery l = some (nxt, k, δ)) (ho : decodedOwner I p.owner = some j) :
    slotView Wc Ws Wt p ((i, l), t) 1 =
      (ruleAddress K h j ((if nxt then locNum K h (.portIn k 0) else locNum K h (.portOut k 0)) +
        reconstructedSlot h p δ) t, 0, 1, if t then 0 else baseWidth Wc Ws Wt l 1) := by
  cases l with
  | portIn tape d =>
    simp only [portQuery, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    simp only [slotView, show 1 < 4 by decide, ↓reduceDIte, ruleData, mateRule,
      show (⟨1, by decide⟩ : Fin 4) = 1 from rfl, locMate, show (1 : Fin 4) ≠ 0 by decide,
      if_neg, if_pos rfl, followRule, portQuery, Option.bind_some, Option.map_some, Option.getD_some, ho,
      Bool.false_eq_true, ↓reduceIte]
  | portOut tape d =>
    simp only [portQuery, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    simp only [slotView, show 1 < 4 by decide, ↓reduceDIte, ruleData, mateRule,
      show (⟨1, by decide⟩ : Fin 4) = 1 from rfl, locMate, show (1 : Fin 4) ≠ 0 by decide,
      if_neg, if_pos rfl, followRule, portQuery, Option.bind_some, Option.map_some, Option.getD_some, ho,
      ↓reduceIte]
  | _ => simp only [portQuery, reduceCtorEq] at hp

private theorem portSlotFallback {I : ℕ} (Wc Ws Wt : ℕ)
    (i : Fin I) (l : Loc K h) (t nxt : Bool) (k : K) (δ : Fin 3)
    (hp : portQuery l = some (nxt, k, δ)) :
    slotView Wc Ws Wt ⟨0, 0, 0⟩ ((i, l), t) 1 = (addrL ((i, l), !t), 0, 1, 0) := by
  cases l <;> simp only [portQuery, reduceCtorEq] at hp
  all_goals simp only [slotView, show 1 < 4 by decide, ↓reduceDIte, ruleData, mateRule,
      show (⟨1, by decide⟩ : Fin 4) = 1 from rfl, locMate, show (1 : Fin 4) ≠ 0 by decide,
      if_neg, if_pos rfl, ite_true, ite_false, followRule, portQuery, Option.bind_some, Option.map_some, Option.getD_some,
      decodedOwner_zero, Option.map_none]

theorem total_le_of_width {qs : List P1Batch.Req} {W : ℕ}
    (h : ∀ q ∈ qs, P1Batch.bval q.2 ≤ W) : P1Batch.total qs ≤ qs.length * W := by
  induction qs with
  | nil => simp only [P1Batch.total, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons q qs ih =>
    simp only [P1Batch.total, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hb := Nat.add_le_add (h q List.mem_cons_self) (ih fun v hv => h v (List.mem_cons_of_mem _ hv))
    simpa only [P1Batch.total, Nat.add_comm (qs.length * W) W] using hb

theorem slotPlan_length (D : Dims) (m Wc Ws Wt : ℕ) (y : (Fin D.I × Loc K h) × Bool)
    (k : Fin (2 ^ a)) : (slotPlan D m Wc Ws Wt y k).length = 6 + 2 ^ h := by
  simp only [slotPlan, List.length_append, List.length_map, List.length_range]
  rfl

theorem slotPlan_width (D : Dims) (m Wc Ws Wt : ℕ) (y : (Fin D.I × Loc K h) × Bool)
    (k : Fin (2 ^ a)) (W : ℕ) (hW : ∀ s < 13, D.width s ≤ W) :
    ∀ rec ∈ slotPlan D m Wc Ws Wt y k, P1Batch.bval rec.1.2 ≤ W := by
  simp only [slotPlan, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true, List.forall_mem_map, sectionTest, unchangedTest, fieldReq, bval_canonical, and_assoc]
  exact ⟨hW _ (by decide), hW _ (by decide), hW _ (by decide), hW _ (by decide), hW _ (by decide),
    hW _ (by decide), fun _ _ => hW _ (by decide)⟩

theorem widths_prepareAt (D : Dims) (τ : K → ℕ) (a m Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) (W : ℕ) (hW : ∀ s < 13, D.width s ≤ W) :
    allFieldWidths (prepareAt D τ a m Wc Ws Wt y) ≤ (3 + 2 ^ a * (6 + 2 ^ h)) * W := by
  have h₁ : P1Batch.total (firstReqs D τ m y) ≤ 2 * W := by
    unfold firstReqs
    split
    · exact Nat.zero_le _
    · simp only [P1Batch.total, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero, startReq, ownerReq, fieldReq, bval_canonical, two_mul]
      apply Nat.add_le_add (hW _ (by decide))
      split <;> exact hW _ (by decide)
  have h₂ : value (packPort D τ y.1.2 y.2).2.2.2.2 ≤ W := by
    unfold packPort
    split <;> simp only [packSection, value_packNumber] <;> exact hW _ (by decide)
  have h₃ : P1Batch.total (((List.finRange (2 ^ a)).flatMap (slotPlan D m Wc Ws Wt y)).map Prod.fst) ≤
      (2 ^ a * (6 + 2 ^ h)) * W := by
    have e : (((List.finRange (2 ^ a)).flatMap (slotPlan D m Wc Ws Wt y)).map Prod.fst).length =
        2 ^ a * (6 + 2 ^ h) := by
      simp only [List.length_map, List.length_flatMap, Function.comp_def, slotPlan_length,
        List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
    rw [← e]
    apply total_le_of_width
    simp only [List.forall_mem_map, List.forall_mem_flatMap, List.mem_finRange, true_implies]
    exact fun k => slotPlan_width D m Wc Ws Wt y k W hW
  change P1Batch.total (firstReqs D τ m y) + value (packPort D τ y.1.2 y.2).2.2.2.2 +
    P1Batch.total (((List.finRange (2 ^ a)).flatMap (slotPlan D m Wc Ws Wt y)).map Prod.fst) ≤ _
  rw [Nat.add_mul, show 3 * W = 2 * W + W by omega]
  exact Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

theorem widths_prepareC4 (D : Dims) (τ : K → ℕ) (a h m Wc Ws Wt i W : ℕ)
    (hW : ∀ s < 13, D.width s ≤ W) :
    allFieldWidths (prepareC4 D τ a h m Wc Ws Wt i) ≤ (3 + 2 ^ a * (6 + 2 ^ h)) * W := by
  unfold prepareC4
  split
  · exact Nat.zero_le _
  · exact widths_prepareAt D τ a m Wc Ws Wt _ W hW

theorem slotPlan_requests (D : Dims) (m Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) (k : Fin (2 ^ a)) (v : SlotView) :
    (slotPlan D m Wc Ws Wt y k).map Prod.fst =
      panelReqs D m (slotFields D (addrL y) k v.1 v.2.1 v.2.2.1 v.2.2.2 (2 ^ h)) := by
  simp only [slotPlan, sectionTest, unchangedTest, panelReqs, slotFields,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def]

theorem slotPlan_values (D : Dims) (m Wc Ws Wt : ℕ)
    (y : (Fin D.I × Loc K h) × Bool) (k : Fin (2 ^ a)) (p : PortReads) (addr : Word)
    (hd : ∀ nxt tape δ j, portQuery y.1.2 = some (nxt, tape, δ) → decodedOwner D.I p.owner = some j →
      value addr = ruleAddress K h j ((if nxt then locNum K h (.portIn tape 0) else
        locNum K h (.portOut tape 0)) + reconstructedSlot h p δ) y.2) :
    let linked := (decodedOwner D.I p.owner).isSome
    let v := slotView Wc Ws Wt p y k
    (slotPlan D m Wc Ws Wt y k).map (fun r => value (expectedValue ((linked, addr), r))) =
      (slotFields D (addrL y) k v.1 v.2.1 v.2.2.1 v.2.2.2 (2 ^ h)).map (fun p => p.2.2) := by
  dsimp only
  by_cases ha : portActive y.1.2 k = true
  · cases ho : decodedOwner D.I p.owner with
    | none =>
      rw [slotView_fallback Wc Ws Wt p y k (fun _ => ho)]
      simp only [slotPlan, slotFields, sectionTest, unchangedTest, expectedValue, ho, Option.isSome_none,
        Bool.cond_false, List.map_append, List.map_cons, List.map_nil, List.map_map, value_packNumber,
        Function.comp_def]
    | some j =>
      have hop := ha
      simp only [portActive, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨hq, hk⟩ := hop
      cases hport : portQuery y.1.2 with
      | none => simp only [hport, Option.isSome_none, Bool.false_eq_true] at hq
      | some rec =>
        rcases rec with ⟨nxt, tape, δ⟩
        rcases y with ⟨⟨i, l⟩, t⟩
        have hp := portSlotView Wc Ws Wt p i j l t nxt tape δ hport ho
        have hf := portSlotFallback Wc Ws Wt i l t nxt tape δ hport
        have ha' := hd nxt tape δ j hport ho
        have hs : portActive l 1 = true := by simpa only [hk] using ha
        simp only [slotPlan, slotFields, sectionTest, unchangedTest, expectedValue, ho, Option.isSome_some,
          Bool.cond_false, Bool.cond_true, hs, ↓reduceIte, List.map_append, List.map_cons, List.map_nil,
          List.map_map, value_packNumber, Function.comp_def, hk, hp, hf, ha']
  · have hb : portActive y.1.2 k = false := Bool.eq_false_iff.mpr ha
    rw [slotView_fallback Wc Ws Wt p y k (fun hc => False.elim (ha hc))]
    cases ho : decodedOwner D.I p.owner <;>
      simp only [slotPlan, slotFields, sectionTest, unchangedTest, expectedValue, ho, Option.isSome_none,
        Option.isSome_some, Bool.cond_false, Bool.cond_true, hb, Bool.false_eq_true, ↓reduceIte,
        List.map_append, List.map_cons, List.map_nil, List.map_map, value_packNumber, Function.comp_def]

theorem headD_eq_getD_zero (l : List Word) : l.headD [] = l.getD 0 [] := by cases l <;> rfl

private theorem portReads_ext {p q : PortReads} (h₁ : p.start = q.start)
    (h₂ : p.owner = q.owner) (h₃ : p.farStart = q.farStart) : p = q := by
  cases p
  cases q
  rw [PortReads.mk.injEq]
  exact ⟨h₁, h₂, h₃⟩

theorem checkPlan_prepareAt {D : Dims} (τ : K → ℕ) (ha : 4 ≤ 2 ^ a)
    (u : Word) (Wc Ws Wt : ℕ) (y : (Fin D.I × Loc K h) × Bool) :
    checkPlan u (prepareAt D τ a u.length Wc Ws Wt y) = true ↔
      C4 ha D (dirAt D τ D.I (2 ^ h)) u Wc Ws Wt y := by
  let p := prepareAt D τ a u.length Wc Ws Wt y
  let reads := readPort D τ u y
  let near := (firstScan p).2.map (P1Batch.fetch u)
  let far := P1Batch.fetch u (farRequest (p, near))
  let addr := ownerAddress (p.2.1, near.headD [], secondWord near, far)
  let linked := ownerOK (p.2.1.1.1, secondWord near)
  let fields := (List.finRange (2 ^ a)).flatMap (slotPlan D u.length Wc Ws Wt y)
  let expected := fields.map (fun r => expectedValue ((linked, addr), r))
  let qs := fields.map Prod.fst
  let actual := (polyPush clampReq (p.1, qs)).map (P1Batch.fetch u)
  have hStart : value (near.headD []) = reads.start := by
    dsimp only [near, p, reads, readPort]
    rw [firstScan_prepareAt, headD_eq_getD_zero, bval_eq_value]
  have hOwn : value (secondWord near) = reads.owner := by
    dsimp only [near, p, reads, readPort]
    rw [firstScan_prepareAt, secondWord_getD, bval_eq_value]
  have hFar : value far = reads.farStart := by
    dsimp only [far, near, p, reads]
    rw [← bval_eq_value]
    exact farRequest_prepareAt D τ a Wc Ws Wt u y
  have hLink : linked = (decodedOwner D.I reads.owner).isSome := by
    have hpI : p.2.1.1.1 = packNumber D.I := by
      dsimp only [p, prepareAt]
      unfold packPort
      split <;> rfl
    rw [show linked = ownerOK (p.2.1.1.1, secondWord near) from rfl,
      hpI, ownerOK_decoded, hOwn]
  have hAddr (nxt : Bool) (tape : K) (δ : Fin 3) (j : Fin D.I)
      (hp : portQuery y.1.2 = some (nxt, tape, δ)) (ho : decodedOwner D.I reads.owner = some j) :
      value addr = ruleAddress K h j ((if nxt then locNum K h (.portIn tape 0) else
        locNum K h (.portOut tape 0)) + reconstructedSlot h reads δ) y.2 := by
    have hj := decodedOwner_eq_some.mp ho
    have eqRead : (⟨value (near.headD []), value (secondWord near), value far⟩ : PortReads) = reads :=
      portReads_ext hStart hOwn hFar
    unfold addr
    simp only [p, prepareAt, packPort, hp]
    rw [ownerAddress_value, eqRead, hOwn, hj, Nat.add_sub_cancel]
    rfl
  let fs := fieldsAt ha D (mateFrom reads) Wc Ws Wt y
  have hViews : fs = (List.finRange (2 ^ a)).flatMap (fun k : Fin (2 ^ a) =>
      let v := slotView Wc Ws Wt reads y k
      slotFields D (addrL y) k v.1 v.2.1 v.2.2.1 v.2.2.2 (2 ^ h)) := by
    unfold fs fieldsAt
    apply congrArg (List.flatMap · (List.finRange (2 ^ a)))
    funext k
    rw [slotView_eq ha Wc Ws Wt reads y k]
  have hReq : qs = panelReqs D u.length fs := by
    rw [hViews]
    simp only [qs, fields, panelReqs, List.map_flatMap]
    apply congrArg (List.flatMap · (List.finRange (2 ^ a)))
    funext k
    exact slotPlan_requests D u.length Wc Ws Wt y k (slotView Wc Ws Wt reads y k)
  have hActual : actual = (panelReqs D u.length fs).map (P1Batch.fetch u) := by
    dsimp only [actual]
    rw [hReq]
    simp only [polyPush, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro q hq
    exact clampReq_fetch u p.1 q (value_packNumber _) (panelReqs_address D u.length fs q hq)
  have hExpected : expected.map value = fs.map (fun f => f.2.2) := by
    rw [hViews]
    simp only [expected, fields, List.map_map, List.map_flatMap, Function.comp_def, hLink]
    apply congrArg (List.flatMap · (List.finRange (2 ^ a)))
    funext k
    exact slotPlan_values D u.length Wc Ws Wt y k reads addr hAddr
  have hLen : expected.length = actual.length := by
    simp only [expected, actual, qs, polyPush, List.length_map]
  change wordsAgree (expected, actual) = true ↔ _
  rw [wordsAgree_true expected actual hLen, hExpected, hActual]
  have h : fs.map (fun f => f.2.2) = (List.map (P1Batch.fetch u) (panelReqs D u.length fs)).map value ↔
      checkPanel D u fs = true := by
    have hv : P1Batch.bval = value := funext bval_eq_value
    simp only [checkPanel, decide_eq_true_eq, hv]
    exact ⟨Eq.symm, Eq.symm⟩
  rw [h, checkPanel_true]
  exact fieldsAt_readPort_iff ha D τ u Wc Ws Wt y

theorem checkPlan_prepareC4 {D : Dims} (τ : K → ℕ) (ha : 4 ≤ 2 ^ a)
    (u : Word) (Wc Ws Wt i : ℕ) :
    checkPlan u (prepareC4 D τ a h u.length Wc Ws Wt i) = true ↔
      C4F ha D (dirAt D τ D.I (2 ^ h)) u Wc Ws Wt i := by
  rw [c4f_at, prepareC4]
  cases hb : baseAt K D.I h i with
  | none => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | some y => exact checkPlan_prepareAt τ ha u Wc Ws Wt y

end P1ProgDir.SolC4
