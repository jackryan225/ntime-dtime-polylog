import P1ChkFinal.C10RcCodes
import P1ProgEng.KWShrinkC10PayloadSpec

/-! The accepted C10 shrink chart and its readers, specialized to the radius-three ball.
The numbered slot readback here only needs a centre within one step of the root. -/

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open P1P7 P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

namespace P1ProgEng.SolKWS.C10

section Bridge

variable {a g : ℕ} {factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)

noncomputable def codedBall (x : X.Base) : BallRows :=
  ballList (nbrAt X) (fun y => (shrinkOld B X s y).map codeShrinkDatum) (addr X x) 3

theorem codedBall_addresses (x : X.Base) :
    (codedBall B X s x).map Prod.fst = bfs (nbrAt X) (addr X x) 3 := by
  simp only [codedBall, ballList, List.map_map, Function.comp_def, List.map_id']

theorem lookup_codedBall (x y : X.Base) :
    lookup none (codedBall B X s x) (addr X y) =
      if (baseGraph X).edist x y ≤ 3 then some (codeShrinkDatum (shrinkData B X s y)) else none := by
  have hb : addr X y ∈ bfs (nbrAt X) (addr X x) 3 ↔ (baseGraph X).edist x y ≤ 3 := by
    rw [mem_bfs_iff]
    constructor
    · rintro ⟨v, hv, hd⟩
      rw [← P1ChkFinal.addr_injective X hv]
      exact hd
    · intro hd
      exact ⟨y, rfl, hd⟩
  by_cases hd : (baseGraph X).edist x y ≤ 3
  · rw [ite_eq_left hd]
    apply lookup_eq_of_mem
    · exact List.mem_map.mpr ⟨addr X y, hb.mpr hd, by simp only [shrinkOld_addr, Option.map_some]⟩
    · intro v hv
      obtain ⟨i, -, hi⟩ := List.mem_map.mp hv
      have e : i = addr X y := congrArg Prod.fst hi
      cases e
      simpa only [shrinkOld_addr, Option.map_some] using (congrArg Prod.snd hi).symm
  · rw [ite_eq_right hd]
    exact lookup_default_of_absent none _ _ (by rw [codedBall_addresses, hb]; exact hd)

theorem rowAt_codedBall (x y : X.Base) (hy : hasRow (codedBall B X s x) (addr X y) = true) :
    rowAt (codedBall B X s x) (addr X y) = codeShrinkDatum (shrinkData B X s y) := by
  have hd : (baseGraph X).edist x y ≤ 3 := by
    by_contra hn
    rw [hasRow, lookup_codedBall B X s x y, ite_eq_right hn] at hy
    cases hy
  rw [rowAt, lookup_codedBall B X s x y, ite_eq_left hd, Option.getD_some]

def oldLaneWord (e : OldArc X) : BitWord (packingLaneBits a g) :=
  (packingFields a g).symm (e.2.1, e.2.2, e.1.1.2.1, e.1.1.2.2)

theorem oldLaneWord_fields (e : OldArc X) :
    packingFields a g (oldLaneWord X e) = (e.2.1, e.2.2, e.1.1.2.1, e.1.1.2.2) :=
  (packingFields a g).apply_symm_apply _

theorem oldLane_code (e : OldArc X) :
    oldLane a (2 ^ g) (arcCode X e) = wordNum (oldLaneWord X e) := by
  have he := joinLane_packing (oldLaneWord X e)
  rw [oldLaneWord_fields] at he
  exact he

theorem selected_field (v : Bool × Fin 4 → ℕ) (layout : Bool) (t : Fin 4) :
    read 0 (shrinkTermCode (some v)) (termField layout t.val) = v (layout,t) := by
  let xs := List.ofFn (fun i : Fin 4 => v (false,i))
  let ys := List.ofFn (fun i : Fin 4 => v (true,i))
  have hx : xs.length = 4 := List.length_ofFn
  cases layout
  · have ht : t.val < xs.length := by rw [hx]; exact t.isLt
    change read 0 (1 :: (xs ++ ys)) (1 + t.val) = _
    unfold read
    rw [Nat.one_add, List.getElem?_cons_succ, List.getElem?_append_left ht]
    exact read_ofFn_num 0 _ t
  · have ht : xs.length ≤ 4 + t.val := by rw [hx]; omega
    change read 0 (1 :: (xs ++ ys)) (5 + t.val) = _
    unfold read
    rw [show 5 + t.val = (4 + t.val) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right ht, hx, Nat.add_sub_cancel_left]
    exact read_ofFn_num 0 _ t

theorem codedBall_payload (x : X.Base) : PayloadRows B X s x (codedBall B X s x) := by
  constructor
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro y i hy
      rw [slotAt, rowAt_codedBall B X s x y hy]
      change (read default (codePanel (panel X y)) i.val).1 = _
      exact congrArg Prod.fst (readAt_panel (panel X y) i)
    · intro y hy
      rw [rowAt_codedBall B X s x y hy]
      rfl
    · intro y hy
      rw [rowAt_codedBall B X s x y hy]
      rfl
    · intro i hi
      rw [codedBall_addresses, mem_bfs_iff] at hi
      exact hi.elim fun y hy => ⟨y, hy.1⟩
    · intro y hy
      rw [hasRow, lookup_codedBall B X s x y, ite_eq_left hy]
      rfl
  · intro e he
    let y := e.1.1.1
    let u := oldLaneWord X e
    change read 0 (slotAt (codedBall B X s x) (addr X y) e.1.2.val).2.2
      (oldLane a (2 ^ g) (arcCode X e)) = _
    rw [oldLane_code X e, slotAt, rowAt_codedBall B X s x y he]
    change read 0 (read default (codePanel (panel X y)) e.1.2.val).2.2 (bwNum u) = _
    rw [show read default (codePanel (panel X y)) e.1.2.val = codeSlot (panel X y) e.1.2
      from readAt_panel _ _]
    exact readAt_laneList 0 (outWidths X y e.1.2) u
  · intro m layout t hm
    let e := m.val
    let y := e.1.1.1
    let i := e.1.2
    let u := oldLaneWord X e
    change read 0 (read [] (read [] (rowAt (codedBall B X s x) (addr X y)).2.2.2
      (oldLane a (2 ^ g) (arcCode X e))) i.val) (termField layout t.val) = _
    rw [oldLane_code X e, rowAt_codedBall B X s x y hm]
    let terms (w : BitWord (packingLaneBits a g)) : List (List ℕ) :=
      let z := packingFields a g w
      List.ofFn fun i => shrinkTermCode (choiceAt B X s y i z.2.2.1 z.2.2.2 z.1 z.2.1)
    change read 0 (read [] (read [] (laneList terms) (bwNum u)) i.val) (termField layout t.val) = _
    rw [show read [] (laneList terms) (bwNum u) = terms u from readAt_laneList [] terms u]
    unfold terms
    dsimp only
    rw [read_ofFn_num [] _ i, oldLaneWord_fields X e]
    have hchoice : choiceAt B X s y i e.1.1.2.1 e.1.1.2.2 e.2.1 e.2.2 = some (s m).val := by
      unfold choiceAt
      dsimp only
      rw [dite_eq_left m.property]
    rw [hchoice, selected_field]

theorem codedBall_terms_length (x : X.Base) :
    (rootTerms (codedBall B X s x) (addr X x)).length = 2 ^ packingLaneBits a g := by
  have hx : hasRow (codedBall B X s x) (addr X x) = true :=
    (codedBall_payload B X s x).cover x (by simp)
  rw [rootTerms, rowAt_codedBall B X s x x hx]
  simp only [codeShrinkDatum, length_laneList]

end Bridge

end P1ProgEng.SolKWS.C10
