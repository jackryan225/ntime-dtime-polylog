import P1ProgDir.C4ProgReadback

namespace P1ProgDir.SolC4

open P1Net P1ChkDir
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}

inductive RuleDirection where
  | same | previous | next | owner
  deriving DecidableEq

/-- A descriptor for a potential mate. For an owner link, the location is the
first of the opposite port's three types, before the directory adjustment. -/
structure MateRule where
  direction : RuleDirection
  location : ℕ
  far : ℕ
  displacement : ℕ
  width : ℕ

def ruleAddress (K : Type) [Fintype K] (h j l : ℕ) (t : Bool) : ℕ :=
  t.toNat + 2 * (l + locCount K h * j)

theorem ruleAddress_eq (ι : Fin I) (l : Loc K h) (t : Bool) :
    ruleAddress K h ι (locNum K h l) t = addrL ((ι, l), t) := by cases t <;> rfl

theorem locNum_portIn_add (k : K) (δ : Fin 3) :
    locNum K h (.portIn k δ) = locNum K h (.portIn k 0) + (δ : ℕ) := by
  simp only [locNum, Fin.val_zero, Nat.add_zero, Nat.add_assoc]

theorem locNum_portOut_add (k : K) (δ : Fin 3) :
    locNum K h (.portOut k δ) = locNum K h (.portOut k 0) + (δ : ℕ) := by
  simp only [locNum, Fin.val_zero, Nat.add_zero, Nat.add_assoc]

/-- Local displacements depend on columns and slots alone. -/
theorem disp1_interval_independent (i : Fin I) (l : Loc K h) (s : Fin 4) :
    disp1 I ((i, l), s) = disp1 1 ((0, l), s) := by cases l <;> rfl

/-- The local part of the geometry table: one rule for each half-edge, before
testing the interval bounds or consulting the directory. -/
noncomputable def mateRule (Wc Ws Wt : ℕ) (l : Loc K h) (s : Fin 4) : Option MateRule :=
  let w := baseWidth Wc Ws Wt l s
  match locMate l s with
  | some (l', s') =>
    some ⟨.same, locNum K h l', s', bwNum (disp1 1 ((0, l), s) + disp1 1 ((0, l'), s')), w⟩
  | none =>
    if s = 1 then
      match l with
      | .portIn k _ => some ⟨.owner, locNum K h (.portOut k 0), 1, 0, w⟩
      | .portOut k _ => some ⟨.owner, locNum K h (.portIn k 0), 1, 0, w⟩
      | .eIn => some ⟨.previous, locNum K h .eOut, 1, 0, w⟩
      | .eOut => some ⟨.next, locNum K h .eIn, 1, 0, w⟩
      | _ => none
    else none

def followRule (I h : ℕ) (j : Fin I) (δ : Fin 3) (p : PortReads) (r : MateRule) :
    Option (Fin I × ℕ) :=
  match r.direction with
  | .same => some (j, r.location)
  | .previous => (colPred j).map fun i => (i, r.location)
  | .next => (colSucc j).map fun i => (i, r.location)
  | .owner => (decodedOwner I p.owner).map fun i => (i, r.location + reconstructedSlot h p δ)

/-- The address, far slot, displacement and unpadded width of the mate, in
numbers. An absent mate is handled by the regularization step. -/
noncomputable def ruleData (Wc Ws Wt : ℕ) (p : PortReads) (i : Fin I) (l : Loc K h) (s : Fin 4) :
    Option ((Fin I × ℕ) × ℕ × ℕ × ℕ) :=
  let δ := ((portQuery l).map fun p => p.2.2).getD 0
  (mateRule Wc Ws Wt l s).bind fun r =>
    (followRule I h i δ p r).map fun peer => (peer, r.far, r.displacement, r.width)

theorem bwNum_zero (h : ℕ) : bwNum (0 : BitWord h) = 0 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    unfold bwNum at ih ⊢
    rw [bitWordFinEquiv_val]
    have ht : Fin.tail (0 : BitWord (h + 1)) = (0 : BitWord h) := rfl
    simp only [ht, ih, Pi.zero_apply, ZMod.val_zero, Nat.mul_zero, Nat.add_zero]

theorem ruleData_eq (Wc Ws Wt : ℕ) (p : PortReads) (i : Fin I) (l : Loc K h) (s : Fin 4) :
    ruleData Wc Ws Wt p i l s = (mateFrom p ((i, l), s)).map fun q =>
      ((q.1.1, locNum K h q.1.2), (q.2 : ℕ),
        bwNum (disp1 I ((i, l), s) + disp1 I q), baseWidth Wc Ws Wt l s) := by
  cases e : locMate l s with
  | some q =>
    rcases q with ⟨l', s'⟩
    simp only [ruleData, mateRule, mateFrom, e, Option.bind_some, followRule, Option.map_some,
      disp1_interval_independent]
  | none =>
    by_cases hs : s = 1
    · subst s
      cases l with
      | portIn k δ =>
        cases hp : decodedOwner I p.owner <;>
          simp only [ruleData, mateRule, mateFrom, e, if_pos rfl, ite_true, interFrom, followRule, portQuery, hp,
            Option.getD_some, Option.bind_some, Option.map_none, Option.map_some, disp1, zero_add,
            bwNum_zero, locNum_portOut_add k (reconstructedSlot h p δ)] <;> rfl
      | portOut k δ =>
        cases hp : decodedOwner I p.owner <;>
          simp only [ruleData, mateRule, mateFrom, e, if_pos rfl, ite_true, interFrom, followRule, portQuery, hp,
            Option.getD_some, Option.bind_some, Option.map_none, Option.map_some, disp1, zero_add,
            bwNum_zero, locNum_portIn_add k (reconstructedSlot h p δ)] <;> rfl
      | eIn =>
        cases hp : colPred i <;>
          simp only [ruleData, mateRule, mateFrom, e, if_pos rfl, ite_true, interFrom, followRule, hp,
            Option.bind_some, Option.map_none, Option.map_some, disp1, zero_add, bwNum_zero] <;> rfl
      | eOut =>
        cases hp : colSucc i <;>
          simp only [ruleData, mateRule, mateFrom, e, if_pos rfl, ite_true, interFrom, followRule, hp,
            Option.bind_some, Option.map_none, Option.map_some, disp1, zero_add, bwNum_zero] <;> rfl
      | _ => simp only [ruleData, mateRule, mateFrom, e, if_pos rfl, ite_true, interFrom, Option.bind_none, Option.map_none]
    · cases l <;>
        simp only [ruleData, mateRule, mateFrom, e, if_neg hs, interFrom, Option.bind_none, Option.map_none]

/-- Numbers used by all stored fields of a slot. Width is the same at every lane. -/
abbrev SlotView := ℕ × ℕ × ℕ × ℕ

noncomputable def slotView (Wc Ws Wt : ℕ) (p : PortReads) (y : (Fin I × Loc K h) × Bool)
    (slot : ℕ) : SlotView :=
  let defaultView := (addrL (y.1, !y.2), 0, slot, 0)
  if hs : slot < 4 then
    match ruleData Wc Ws Wt p y.1.1 y.1.2 ⟨slot, hs⟩ with
    | none => defaultView
    | some (peer, far, disp, width) =>
      (ruleAddress K h peer.1 peer.2 y.2, disp, far, if y.2 then 0 else width)
  else defaultView

theorem slotView_eq {a : ℕ} (ha : 4 ≤ 2 ^ a) (Wc Ws Wt : ℕ) (p : PortReads)
    (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    slotView Wc Ws Wt p y k =
      (addrL (tgtOf ha (mateFrom p) y k).1, bwNum (dispOf (mateFrom p) y k),
        ((tgtOf ha (mateFrom p) y k).2 : ℕ), widthOf (mateFrom p) Wc Ws Wt y k 0) := by
  unfold slotView tgtOf dispOf widthOf PreGraph.slot4
  dsimp only
  split
  · rename_i hk
    simp only [dif_pos hk, ruleData_eq]
    cases hm : mateFrom p (y.1, (⟨k.val, hk⟩ : Fin 4)) with
    | none => simp only [hm, Option.map_none, bwNum_zero, ↓reduceIte, ite_self]
    | some q =>
      rcases q with ⟨⟨j, l⟩, s⟩
      simp only [hm, Option.map_some, ruleAddress_eq, Fin.val_castLE, reduceCtorEq, ↓reduceIte]
  · rename_i hk
    simp only [dif_neg hk, bwNum_zero]

end P1ProgDir.SolC4
