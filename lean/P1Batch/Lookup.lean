import P1Batch.Step

/-!
# P1Batch.Lookup: the batched look-up (paper lem:batch) as one stack program

Pipeline on `send (w, qs)`:
A. (right of `w`) plan = gaps of the requests tagged with their index and sorted by address (polynomial in `qs`);
B. exchange: `fork plan w`;  C. (right of plan) put the empty record list in front of `w`;
D. one left fold of `stepTask` over the plan (`foldLeftS`), the data `w` consumed from left to right;
E. drop the remaining data;  F. restore the request order (sort by tag, polynomial) and keep the fields.
Budget: `O(m)` for the crossings of `w` and the scan (gaps telescope to at most `m`), plus a polynomial in
`size qs + Σ ℓ_i` (`Dom` calculus of OpenAI's CodePolyBasic).
-/

namespace P1Batch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open scoped List

/-- Tagged requests sorted by address. -/
def Sx (qs : List Req) : List TReq := arrange ltA (tagged qs)
/-- The plan of the scan. -/
def planF (qs : List Req) : List TReq := gapsOf (Sx qs)
/-- State after the scan. -/
def finF (w : List Bool) (qs : List Req) : St := (planF qs).foldl scanStep (([] : List Rec), w)
/-- Back to request order: sort the records by tag and keep the fields. -/
def restore (outs : List Rec) : List (List Bool) := (arrange ltT outs).map Prod.snd

theorem poly_Sx : Poly Sx := poly_tagged.compose (arrange_poly ltA easy_ltA.poly)
theorem poly_planF : Poly planF := poly_Sx.compose easy_gapsOf.poly
theorem poly_restore : Poly restore :=
  (arrange_poly ltT easy_ltT.poly).compose (Easy.mapping (Easy.snd (X := Tally) (Y := List Bool))).poly

theorem sorted_Sx (qs : List Req) : (Sx qs).Pairwise (fun a b => bval a.2.1 ≤ bval b.2.1) :=
  arrange_sorted (κ := fun e : TReq => bval e.2.1) ltA_eq _

theorem finF_eq (w : List Bool) (qs : List Req) :
    finF w qs = (((Sx qs).map (recOf w)).reverse ++ [], w.drop (bval (lastA [] (Sx qs)))) := by
  have h := scan_gaps w (Sx qs) [] [] (fun e _ => Nat.zero_le _) (sorted_Sx qs)
  unfold finF planF
  rw [gapsOf_eq]
  exact h

/-! ## Correctness -/

theorem lookup_correct (w : List Bool) (qs : List Req) : restore (finF w qs).1 = qs.map (fetch w) := by
  rw [finF_eq]
  dsimp only
  unfold restore
  rw [List.append_nil]
  have hperm : ((Sx qs).map (recOf w)).reverse ~ (tagged qs).map (recOf w) :=
    (List.reverse_perm _).trans ((arrange_perm ltA _).map _)
  have hkeys : ((tagged qs).map (recOf w)).map (fun r : Rec => r.1.length) = (tags qs).map List.length := by
    rw [List.map_map, tagged_eq]
    rw [show ((fun r : Rec => r.1.length) ∘ recOf w) = List.length ∘ (Prod.fst : TReq → Tally) from rfl,
      ← List.map_map, List.map_fst_zip (by simp [tags_length])]
  have hLk : (((tagged qs).map (recOf w)).map (fun r : Rec => r.1.length)).Pairwise (· < ·) := by
    rw [hkeys]
    unfold tags Iter.lineup
    rw [List.map_ofFn, List.pairwise_ofFn]
    intro i j hij
    simp only [Function.comp, tally_length]
    exact hij
  have hL : ((tagged qs).map (recOf w)).Pairwise (fun a b : Rec => a.1.length < b.1.length) :=
    List.pairwise_map.mp hLk
  have hA := arrange_perm ltT (((Sx qs).map (recOf w)).reverse)
  have hsA := arrange_sorted (κ := fun r : Rec => r.1.length) ltT_eq (((Sx qs).map (recOf w)).reverse)
  have hnd : ((arrange ltT (((Sx qs).map (recOf w)).reverse)).map (fun r : Rec => r.1.length)).Nodup :=
    ((hA.trans hperm).map _).nodup_iff.mpr (hLk.imp (fun h => Nat.ne_of_lt h))
  have hne : (arrange ltT (((Sx qs).map (recOf w)).reverse)).Pairwise
      (fun a b : Rec => a.1.length ≠ b.1.length) := List.pairwise_map.mp hnd
  have hsA' : (arrange ltT (((Sx qs).map (recOf w)).reverse)).Pairwise
      (fun a b : Rec => a.1.length < b.1.length) :=
    (hsA.and hne).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  have heq := List.Perm.eq_of_pairwise
    (fun a b _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)) hsA' hL (hA.trans hperm)
  rw [heq, List.map_map, show (Prod.snd ∘ recOf w) = fetch w ∘ (Prod.snd : TReq → Req) from rfl,
    ← List.map_map, tagged_eq, List.map_snd_zip (by simp [tags_length])]

/-! ## Size facts -/

theorem size_perm {X : Type} [Codec X] {a b : List X} (pm : a ~ b) : size a = size b := by
  induction pm with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp; omega
  | trans _ _ ih ij => exact ih.trans ij

theorem size_recs (w : List Bool) (S : List TReq) : size (S.map (recOf w)) ≤ size S + 2 * tot S := by
  induction S with
  | nil => simp [tot]
  | cons e S ih =>
    simp only [List.map_cons, size_cons]
    have h1 : size (recOf w e) = size e.1 + size (fetch w e.2) + 1 := rfl
    have h2 : size (fetch w e.2) ≤ 2 * bval e.2.2 + 1 := count_send_take _ _
    have h3 : size e = size e.1 + (size e.2.1 + size e.2.2 + 1) + 1 := rfl
    have h4 := size_pos e.2.1
    have h5 := size_pos e.2.2
    have h6 : tot (e :: S) = bval e.2.2 + tot S := by simp [tot]
    omega

theorem tot_perm {S T : List TReq} (h : S ~ T) : tot S = tot T := (h.map _).sum_eq

theorem tot_tagged (qs : List Req) : tot (tagged qs) = total qs := by
  unfold tot total
  rw [tagged_eq, show (fun e : TReq => bval e.2.2) = (fun q : Req => bval q.2) ∘ Prod.snd from rfl,
    ← List.map_map, List.map_snd_zip (by simp [tags_length])]

theorem tot_Sx (qs : List Req) : tot (Sx qs) = total qs :=
  (tot_perm (arrange_perm ltA _)).trans (tot_tagged qs)

theorem size_outs (w : List Bool) (qs : List Req) :
    size (finF w qs).1 ≤ size (Sx qs) + 2 * total qs := by
  rw [finF_eq]
  dsimp only
  rw [List.append_nil, size_perm (List.reverse_perm _)]
  have := size_recs w (Sx qs)
  rw [tot_Sx] at this
  exact this

theorem count_suf (w : List Bool) (qs : List Req) : (send (finF w qs).2).count ≤ 2 * w.length + 1 := by
  rw [finF_eq]
  dsimp only
  rw [count_send_bits, List.length_drop]
  omega

theorem walk_le (x : BatchIn) :
    walkCost stepCost scanStep (([] : List Rec), x.val.1) (planF x.val.2)
      ≤ (Sx x.val.2).length * (1 + (size (Sx x.val.2) + 2 * total x.val.2)) + size (planF x.val.2)
        + x.val.1.length + total x.val.2 + (Sx x.val.2).length := by
  have hmem : ∀ e ∈ Sx x.val.2, bval ([] : List Bool) ≤ bval e.2.1 ∧ bval e.2.1 ≤ x.val.1.length := by
    intro e he
    refine ⟨Nat.zero_le _, ?_⟩
    have he' : e ∈ tagged x.val.2 := (arrange_perm ltA _).subset he
    rw [tagged_eq] at he'
    have hq := (List.of_mem_zip (a := e.1) (b := e.2) he').2
    exact x.property e.2 hq
  have h := walk_bound x.val.1 (Sx x.val.2) [] [] hmem (sorted_Sx _)
  have e1 : planF x.val.2 = gapsAux [] (Sx x.val.2) := gapsOf_eq _
  rw [e1]
  have h' : walkCost stepCost scanStep (([] : List Rec), x.val.1) (gapsAux [] (Sx x.val.2)) ≤ _ := h
  have hsr := size_recs x.val.1 (Sx x.val.2)
  have ht := tot_Sx x.val.2
  have hb0 : bval ([] : List Bool) = 0 := rfl
  have hmono : (Sx x.val.2).length * (size ([] : List Rec) + size ((Sx x.val.2).map (recOf x.val.1)))
      ≤ (Sx x.val.2).length * (1 + (size (Sx x.val.2) + 2 * total x.val.2)) :=
    Nat.mul_le_mul_left _ (by rw [size_nil]; omega)
  omega

/-! ## The program -/

theorem batch_lookup_proof : ∃ c : ℕ,
    Task (fun i : BatchIn => i.val.1.length + (size i.val.2 + total i.val.2 + 1) ^ c)
      (fun i => send i.val) (fun i => send (i.val.2.map (fetch i.val.1))) := by
  obtain ⟨t1, ht1, hT1⟩ := poly_planF
  obtain ⟨t2, ht2, hT2⟩ := poly_restore
  -- A. the plan, right of the data
  have hA := (hT1.on (fun x : BatchIn => x.val.2)).right (fun x => send x.val.1)
  -- B. exchange
  have hB := Task.exchange (fun x : BatchIn => send x.val.1) (fun x => send (planF x.val.2))
  -- C. empty records in front of the data
  have hC := (Task.supply (send ([] : List Rec)) (fun x : BatchIn => send x.val.1)).right
    (fun x => send (planF x.val.2))
  -- D. the scan
  have hD0 := foldLeftS (p := fun (_ : Unit) => (send : TReq → Tree))
    (u := fun (_ : Unit) => (send : St → Tree)) (next := fun _ => scanStep) (a := fun _ => stepCost) stepTask
  have hD := (hD0.on (fun x : BatchIn => (planF x.val.2, ((([] : List Rec), x.val.1) : St), ()))).conform
    (b' := fun x : BatchIn =>
      walkCost stepCost scanStep (([] : List Rec), x.val.1) (planF x.val.2) + size (planF x.val.2))
    (p' := fun x : BatchIn => .fork (send (planF x.val.2)) (.fork (send ([] : List Rec)) (send x.val.1)))
    (q' := fun x : BatchIn => send (finF x.val.1 x.val.2))
    (fun x => by simp only [Task.forest_send, size]) (fun x => by simp only [Task.forest_send]; rfl)
    (fun x => rfl)
  -- E. drop the rest of the data
  have hE := Task.dropRight (fun x : BatchIn => send (finF x.val.1 x.val.2).1)
    (fun x => send (finF x.val.1 x.val.2).2)
  -- F. request order
  have hF := hT2.on (fun x : BatchIn => (finF x.val.1 x.val.2).1)
  have hall := (((((hA.compose hB).compose hC).compose hD).compose hE).compose hF).conform
    (q' := fun x : BatchIn => send (x.val.2.map (fetch x.val.1)))
    (fun _ => rfl) (fun _ => rfl) (fun x => by rw [lookup_correct])
  -- the polynomial part of the budget
  let p : BatchIn → ℕ := fun x => size x.val.2 + total x.val.2
  have hq : Dom p (fun x => size x.val.2) := (Dom.base p).mono (fun x => Nat.le_add_right _ _)
  have hto : Dom p (fun x => total x.val.2) := (Dom.base p).mono (fun x => Nat.le_add_left _ _)
  have dT1 : Dom p (fun x => t1 x.val.2) := (ht1.map (fun x : BatchIn => x.val.2)).sub hq
  have dP : Dom p (fun x => size (planF x.val.2)) :=
    (poly_planF.length.map (fun x : BatchIn => x.val.2)).sub hq
  have dS : Dom p (fun x => size (Sx x.val.2)) := (poly_Sx.length.map (fun x : BatchIn => x.val.2)).sub hq
  have dR : Dom p (fun x => (Sx x.val.2).length) := dS.mono (fun x => (duration _).le)
  have dRec : Dom p (fun x => size (Sx x.val.2) + 2 * total x.val.2) := dS.add ((Dom.const p 2).mul hto)
  have dO : Dom p (fun x => size (finF x.val.1 x.val.2).1) := dRec.mono (fun x => size_outs _ _)
  have dT2 : Dom p (fun x => t2 (finF x.val.1 x.val.2).1) :=
    (ht2.map (fun x : BatchIn => (finF x.val.1 x.val.2).1)).sub dO
  have dW : Dom p (fun x => (Sx x.val.2).length * (1 + (size (Sx x.val.2) + 2 * total x.val.2))) :=
    dR.mul ((Dom.const p 1).add dRec)
  have dT : Dom p (fun x => t1 x.val.2 + size (planF x.val.2)
      + (Sx x.val.2).length * (1 + (size (Sx x.val.2) + 2 * total x.val.2)) + total x.val.2
      + (Sx x.val.2).length + size (Sx x.val.2) + t2 (finF x.val.1 x.val.2).1) :=
    ((((((dT1.add dP).add dW).add hto).add dR).add dS).add dT2)
  obtain ⟨k, C, hk⟩ := dT
  refine ⟨k, hall.bound (4 * C + 20) (fun x => ?_)⟩
  have g1 : (send x.val.1).count = 2 * x.val.1.length + 1 := count_send_bits _
  have g2 : (send (planF x.val.2)).count = size (planF x.val.2) := rfl
  have g3 := walk_le x
  have g4 : (send (finF x.val.1 x.val.2).1).count ≤ size (Sx x.val.2) + 2 * total x.val.2 :=
    size_outs _ _
  have g5 := count_suf x.val.1 x.val.2
  have g6 : _ ≤ C * (size x.val.2 + total x.val.2 + 1) ^ k := hk x
  have g7 : (send ([] : List Rec)).count = 1 := rfl
  have hexp : (4 * C + 20) * (x.val.1.length + (size x.val.2 + total x.val.2 + 1) ^ k + 1)
      = 4 * (C * x.val.1.length) + 4 * (C * (size x.val.2 + total x.val.2 + 1) ^ k) + 4 * C
        + 20 * x.val.1.length + 20 * (size x.val.2 + total x.val.2 + 1) ^ k + 20 := by ring
  beta_reduce at g6 ⊢
  omega

/-- `batch_lookup` unfolded to OpenAI's `Prog.Run`. -/
theorem batch_lookup_prog_proof : ∃ (P : Prog Ltr) (c : ℕ), ∀ (w : List Bool) (qs : List Req),
    (∀ q ∈ qs, bval q.1 ≤ w.length) → ∀ (env : Scope Ltr) (r : Reg Tree),
      ∃ t ≤ c * (w.length + (size qs + total qs + 1) ^ c),
        Prog.Run env P (letters (pile 0 (send (w, qs)) r)) t
          (letters (pile 0 (send (qs.map (fetch w))) r)) := by
  obtain ⟨c0, P, C0, h⟩ := batch_lookup_proof
  refine ⟨P, c0 + 2 * C0 + 1, fun w qs hq env r => ?_⟩
  obtain ⟨t, ht, hrun⟩ := h ⟨(w, qs), hq⟩ env r
  refine ⟨t, ht.trans ?_, hrun⟩
  have h1 : (size qs + total qs + 1) ^ c0 ≤ (size qs + total qs + 1) ^ (c0 + 2 * C0 + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 1 ≤ (size qs + total qs + 1) ^ (c0 + 2 * C0 + 1) := Nat.one_le_pow _ _ (by omega)
  calc C0 * (w.length + (size qs + total qs + 1) ^ c0 + 1)
      ≤ C0 * (2 * (w.length + (size qs + total qs + 1) ^ (c0 + 2 * C0 + 1))) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = (2 * C0) * (w.length + (size qs + total qs + 1) ^ (c0 + 2 * C0 + 1)) := by ring
    _ ≤ (c0 + 2 * C0 + 1) * (w.length + (size qs + total qs + 1) ^ (c0 + 2 * C0 + 1)) :=
        Nat.mul_le_mul_right _ (by omega)

end P1Batch
