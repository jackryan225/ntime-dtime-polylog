import P1Batch.Sort
import P1Batch.Moves

/-!
# P1Batch.Plan: tags, gaps between sorted addresses, and the scan as a Lean fold

* `tagged qs = zip (tallies 0..r-1) qs` (`tagged_eq`), polynomial time (`poly_tagged`).
* `gapsOf S`: each sorted entry `(t, (a, ℓ))` becomes `(t, (a - a_prev, ℓ))` in binary (`Bits.sub`); linear time
  (`easy_gapsOf`); `gapsOf S = gapsAux [] S` (`gapsOf_eq`).
* `scanStep`: one step of the scan of the data (cut off the gap, cut off the field, put the field back, record it).
  `scan_gaps`: on a sorted list the scan returns the fetched fields (reversed) and the suffix after the last address.
* `walk_bound`: the step budgets along the scan sum to
  `r (size outs + size records) + size plan + (m - a_0) + Σ ℓ + r`.
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Tags -/

/-- The tags `tally 0, …, tally (r-1)`. -/
def tags (qs : List Req) : List Tally := Iter.lineup (ruler qs)

theorem tags_length (qs : List Req) : (tags qs).length = qs.length := by
  simp [tags]

theorem take_zipSafe {A B : Type} (c : A) (d : B) (l1 : List A) (l2 : List B)
    (h : l1.length = l2.length) : (zipSafe c d (l1, l2)).take l2.length = l1.zip l2 := by
  unfold zipSafe
  dsimp only
  rw [List.zip_append h]
  exact List.take_left' (by simp [h])

/-- Tagged requests `(tally i, q_i)`. -/
def tagged (qs : List Req) : List TReq :=
  (cutLists (ruler qs, zipSafe ([] : Tally) (([] : List Bool), ([] : List Bool)) (tags qs, qs))).1

theorem tagged_eq (qs : List Req) : tagged qs = (tags qs).zip qs := by
  unfold tagged cutLists
  dsimp only
  rw [ruler_length]
  exact take_zipSafe _ _ _ _ (tags_length qs)

theorem poly_tagged : Poly tagged := by
  have hr : Easy (fun qs : List Req => ruler qs) := Easy.ruler easy_id
  have ht : Poly tags := hr.poly.compose Iter.poly_line
  have hz : Poly (fun qs : List Req =>
      zipSafe ([] : Tally) (([] : List Bool), ([] : List Bool)) (tags qs, qs)) :=
    (ht.pair Code.Poly.identity).compose (Easy.zipSafe _ _).poly
  have hc : Poly (fun qs : List Req =>
      cutLists (ruler qs, zipSafe ([] : Tally) (([] : List Bool), ([] : List Bool)) (tags qs, qs))) :=
    (hr.poly.pair hz).compose (easy_cut easy_id).poly
  exact hc.fstCompose

/-! ## Gaps -/

/-- Address of a tagged request. -/
def addr (e : TReq) : List Bool := e.2.1

/-- Previous addresses `[], a_1, …, a_{r-1}`. -/
def prevs (S : List TReq) : List (List Bool) :=
  (cutLists (ruler S, ([] : List Bool) :: S.map addr)).1

/-- Plan item from an entry and the previous address: `(tag, (gap word, length word))`. -/
def gstep (p : TReq × List Bool) : TReq := (p.1.1, ((Bits.sub (p.1.2.1, p.2)).1, p.1.2.2))

theorem gstep_fst (e : TReq) (p : List Bool) : (gstep (e, p)).2.1 = (Bits.sub (e.2.1, p)).1 := rfl
theorem gstep_snd (e : TReq) (p : List Bool) : (gstep (e, p)).2.2 = e.2.2 := rfl
theorem gstep_tag (e : TReq) (p : List Bool) : (gstep (e, p)).1 = e.1 := rfl

/-- The plan: gaps between consecutive addresses of a (sorted) list. -/
def gapsOf (S : List TReq) : List TReq :=
  ((cutLists (ruler S, zipSafe (([] : Tally), (([] : List Bool), ([] : List Bool))) ([] : List Bool)
    (S, prevs S))).1).map gstep

theorem easy_gapsOf : Easy gapsOf := by
  have ha : Easy addr := by unfold addr; fun_prop
  have hmap : Easy (fun S : List TReq => S.map addr) := easy_map easy_id ha
  have hcons : Easy (fun S : List TReq => ([] : List Bool) :: S.map addr) :=
    (Easy.pair (Easy.const []) hmap).compose Easy.cons
  have hprev : Easy prevs := (easy_cut (Easy.pair (Easy.ruler easy_id) hcons)).fstCompose
  have hz : Easy (fun S : List TReq => zipSafe (([] : Tally), (([] : List Bool), ([] : List Bool)))
      ([] : List Bool) (S, prevs S)) := easy_zipSafe _ _ (Easy.pair easy_id hprev)
  have hc := (easy_cut (Easy.pair (Easy.ruler easy_id) hz)).fstCompose
  have hg : Easy gstep := by unfold gstep; fun_prop
  exact easy_map hc hg

/-- Recursive form of the plan, from a previous address `p`. -/
def gapsAux : List Bool → List TReq → List TReq
  | _, [] => []
  | p, e :: S => gstep (e, p) :: gapsAux e.2.1 S

theorem zip_prev_eq (S : List TReq) (p : List Bool) :
    (S.zip ((p :: S.map addr).take S.length)).map gstep = gapsAux p S := by
  induction S generalizing p with
  | nil => rfl
  | cons e S ih =>
    simp only [List.length_cons, List.map_cons, List.take_succ_cons, List.zip_cons_cons, gapsAux]
    rw [← ih e.2.1]
    rfl

theorem gapsOf_eq (S : List TReq) : gapsOf S = gapsAux [] S := by
  have hp : prevs S = (([] : List Bool) :: S.map addr).take S.length := by
    unfold prevs cutLists
    simp only [ruler_length]
  have hl : S.length = (prevs S).length := by
    rw [hp, List.length_take, List.length_cons, List.length_map]
    omega
  have e1 : (zipSafe (([] : Tally), (([] : List Bool), ([] : List Bool))) ([] : List Bool)
      (S, prevs S)).take S.length = S.zip (prevs S) := by
    have := take_zipSafe (([] : Tally), (([] : List Bool), ([] : List Bool))) ([] : List Bool) S (prevs S) hl
    rwa [← hl] at this
  unfold gapsOf cutLists
  dsimp only
  rw [ruler_length, e1, hp, zip_prev_eq]

/-! ## The scan as a Lean fold -/

/-- State of the scan: (records so far, newest first; the data from the current address on). -/
abbrev St := List Rec × List Bool

/-- One step: cut off the gap, cut off the field, put the field back, record `(tag, field)`. -/
def scanStep (st : St) (it : TReq) : St :=
  ((it.1, (cutLists (tally (bval it.2.2), (cutLists (tally (bval it.2.1), st.2)).2)).1) :: st.1,
   (cutLists (tally (bval it.2.2), (cutLists (tally (bval it.2.1), st.2)).2)).1 ++
   (cutLists (tally (bval it.2.2), (cutLists (tally (bval it.2.1), st.2)).2)).2)

/-- The record of a tagged request. -/
def recOf (w : List Bool) (e : TReq) : Rec := (e.1, fetch w e.2)

theorem bval_sub (a p : List Bool) (h : bval p ≤ bval a) :
    bval (Bits.sub (a, p)).1 = bval a - bval p := by
  rw [bval_eq_value, bval_eq_value] at h
  rw [bval_eq_value, bval_eq_value, bval_eq_value]
  exact Bits.sub_val_le _ _ h

theorem scanStep_gstep (w : List Bool) (outs : List Rec) (e : TReq) (p : List Bool)
    (hp : bval p ≤ bval e.2.1) :
    scanStep (outs, w.drop (bval p)) (gstep (e, p)) = (recOf w e :: outs, w.drop (bval e.2.1)) := by
  have hg := bval_sub e.2.1 p hp
  have h2 : bval p + (bval e.2.1 - bval p) = bval e.2.1 := by omega
  have hd : (w.drop (bval p)).drop (bval e.2.1 - bval p) = w.drop (bval e.2.1) := by
    rw [List.drop_drop, h2]
  simp only [scanStep, gstep_fst, gstep_snd, gstep_tag, cutLists, tally_length, hg, hd,
    List.take_append_drop, recOf, fetch]

/-- Final address of a scan that starts at `p`. -/
def lastA (p : List Bool) (S : List TReq) : List Bool := S.foldl (fun _ e => e.2.1) p

theorem scan_gaps (w : List Bool) : ∀ (S : List TReq) (p : List Bool) (outs : List Rec),
    (∀ e ∈ S, bval p ≤ bval e.2.1) → S.Pairwise (fun a b => bval a.2.1 ≤ bval b.2.1) →
    (gapsAux p S).foldl scanStep (outs, w.drop (bval p))
      = ((S.map (recOf w)).reverse ++ outs, w.drop (bval (lastA p S))) := by
  intro S
  induction S with
  | nil => intro p outs _ _; rfl
  | cons e S ih =>
    intro p outs hp hs
    rw [List.pairwise_cons] at hs
    simp only [gapsAux, List.foldl_cons, scanStep_gstep w outs e p (hp e List.mem_cons_self)]
    rw [ih e.2.1 (recOf w e :: outs) hs.1 hs.2]
    simp [lastA]

/-! ## Budget along the scan -/

/-- Step budget: records so far, the item, the gap, the length (never the data suffix). -/
def stepCost (st : St) (it : TReq) : ℕ := size st.1 + size it + bval it.2.1 + bval it.2.2 + 1

/-- Total requested length of tagged requests. -/
def tot (S : List TReq) : ℕ := (S.map fun e => bval e.2.2).sum

theorem walk_bound (w : List Bool) : ∀ (S : List TReq) (p : List Bool) (outs : List Rec),
    (∀ e ∈ S, bval p ≤ bval e.2.1 ∧ bval e.2.1 ≤ w.length) →
    S.Pairwise (fun a b => bval a.2.1 ≤ bval b.2.1) →
    walkCost stepCost scanStep (outs, w.drop (bval p)) (gapsAux p S)
      ≤ S.length * (size outs + size (S.map (recOf w))) + size (gapsAux p S) + (w.length - bval p)
        + tot S + S.length := by
  intro S
  induction S with
  | nil => intro p outs _ _; simp [walkCost, gapsAux]
  | cons e S ih =>
    intro p outs hp hs
    rw [List.pairwise_cons] at hs
    have he := hp e List.mem_cons_self
    have hrest : ∀ e' ∈ S, bval e.2.1 ≤ bval e'.2.1 ∧ bval e'.2.1 ≤ w.length :=
      fun e' h' => ⟨hs.1 e' h', (hp e' (List.mem_cons_of_mem _ h')).2⟩
    have hih := ih e.2.1 (recOf w e :: outs) hrest hs.2
    have hK : size (recOf w e :: outs) + size (S.map (recOf w))
        = size outs + size ((e :: S).map (recOf w)) := by
      simp only [List.map_cons, size_cons]; omega
    rw [hK] at hih
    have hg := bval_sub e.2.1 p he.1
    have hmul : (S.length + 1) * (size outs + size ((e :: S).map (recOf w)))
        = S.length * (size outs + size ((e :: S).map (recOf w)))
          + (size outs + size ((e :: S).map (recOf w))) := by ring
    have hsz3 := size_cons (gstep (e, p)) (gapsAux e.2.1 S)
    have htot : tot (e :: S) = bval e.2.2 + tot S := by simp [tot]
    simp only [gapsAux, walkCost, scanStep_gstep w outs e p he.1, stepCost, gstep_fst, gstep_snd, hg,
      List.length_cons]
    omega

end P1Batch
