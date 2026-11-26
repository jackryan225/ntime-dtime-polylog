import P1C1U.CheckRows
import P1C1U.OuterChecker
import P1Hier.Hierarchy

namespace P1C1U.AstraC1U.Outer

open C1Challenge P1Int P1Wrap.W3
noncomputable section

open Classical in
/-- Each accepted fixed-length guess encodes one prefix and one accepting computation on its padded input. -/
theorem count (M : NMachine) (j a b : ℕ) (x : List Bool) (g T : ℕ)
    (bound : ∀ u : Fin (lpM2 (sOf j) a b x.length) → Bool, ∀ d,
      ¬ M.Reach (M.init (padIn j a b x (List.ofFn u))) (T + 1) d)
    (room : lpM2 (sOf j) a b x.length + ((Rows.ncode M).table.length + 1) * (T + 1) ≤ g) :
    (Finset.univ.filter fun w : Fin g → Bool => verdict (Rows.ncode M) j a b (List.ofFn w) x = true).card =
      ∑ u : Fin (lpM2 (sOf j) a b x.length) → Bool, M.acc (padIn j a b x (List.ofFn u)) := by
  classical
  let m := lpM2 (sOf j) a b x.length
  let U := Fin m → Bool
  let y (u : U) := padIn j a b x (List.ofFn u)
  let S := (u : U) × M.AccComp (y u)
  letI (u : U) : Fintype (M.AccComp (y u)) := by
    haveI : Finite (M.AccComp (y u)) := finite_accComp (bound u)
    exact Fintype.ofFinite _
  let tbl := (Rows.ncode M).table
  let τ (v : S) := Rows.rows M (M.init (y v.1)) v.2.val
  let body (v : S) := List.ofFn v.1 ++ encT tbl (τ v)
  let pack (v : S) (i : Fin g) := (body v).getD i false
  change m + (tbl.length + 1) * (T + 1) ≤ g at room
  have hmg : m ≤ g := by omega
  have hTg : T ≤ g := by
    have h : T + 1 ≤ (tbl.length + 1) * (T + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  have memτ (v : S) : ∀ e ∈ τ v, e ∈ tbl :=
    Rows.rows_mem M v.2.val _ v.2.property.1 v.2.property.2.1
  have lenτ (v : S) : (τ v).length ≤ T + 1 := by
    calc
      (τ v).length = v.2.val.length + 1 := Rows.length_rows M v.2.val (M.init (y v.1))
      _ ≤ T + 1 := Nat.succ_le_succ (acc_length_le (bound v.1) v.2)
  have fit (v : S) : (body v).length ≤ g := by
    have hl := (length_encT_le tbl (τ v) (memτ v)).trans (Nat.mul_le_mul_right _ (lenτ v))
    rw [Nat.mul_comm (T + 1)] at hl
    simp only [body, List.length_append, List.length_ofFn]
    omega
  have form (v : S) : List.ofFn (pack v) =
      List.ofFn v.1 ++ (encT tbl (τ v) ++ List.replicate (g - (body v).length) false) := by
    have h := P1Hier.ofFn_getD (body v) g (fit v)
    simpa only [pack, body, List.append_assoc] using h
  have pref (v : S) : (List.ofFn (pack v)).take m = List.ofFn v.1 := by
    rw [form v, List.take_left' (List.length_ofFn : (List.ofFn v.1).length = m)]
  have suff (v : S) : (List.ofFn (pack v)).drop m =
      encT tbl (τ v) ++ List.replicate (g - (body v).length) false := by
    rw [form v, List.drop_left' (List.length_ofFn : (List.ofFn v.1).length = m)]
  have accepted (v : S) : verdict (Rows.ncode M) j a b (List.ofFn (pack v)) x = true := by
    unfold verdict
    rw [decide_eq_true_iff, List.length_ofFn]
    refine ⟨hmg, τ v, g - (body v).length, memτ v, suff v, ?_⟩
    change P1Hier.Check (Rows.ncode M) (padIn j a b x ((List.ofFn (pack v)).take m)) g (τ v)
    rw [pref v]
    exact (Rows.check_iff M (y v.1) g (τ v)).mpr
      ⟨v.2, rfl, (acc_length_le (bound v.1) v.2).trans hTg⟩
  let Gs := Finset.univ.filter fun w : Fin g → Bool => verdict (Rows.ncode M) j a b (List.ofFn w) x = true
  have bij : (Finset.univ : Finset S).card = Gs.card := by
    apply Finset.card_bij (fun v _ => pack v)
    · intro v _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, accepted v⟩
    · rintro ⟨u, s⟩ _ ⟨u', s'⟩ _ he
      have hp := congrArg (fun w : Fin g → Bool => (List.ofFn w).take m) he
      have hu : u = u' := List.ofFn_injective
        ((pref ⟨u,s⟩).symm.trans (hp.trans (pref ⟨u',s'⟩)))
      subst u'
      have hd := congrArg (fun w : Fin g → Bool => (List.ofFn w).drop m) he
      have hs := (suff ⟨u,s⟩).symm.trans (hd.trans (suff ⟨u,s'⟩))
      have ht := encT_pad_inj (τ ⟨u,s⟩) (τ ⟨u,s'⟩) _ _ (memτ ⟨u,s⟩) (memτ ⟨u,s'⟩) hs
      have heq : s = s' := Subtype.ext (Rows.eq_of_rows_eq M s.val s'.val (M.init (y u)) ht)
      subst s'
      rfl
    · intro w hw
      have hacc := (Finset.mem_filter.mp hw).2
      unfold verdict at hacc
      rw [decide_eq_true_iff] at hacc
      obtain ⟨_, t, r, _, hd, hcheck⟩ := hacc
      let u : U := cut m g w
      have hp : (List.ofFn w).take m = List.ofFn u := take_ofFn_cut hmg w
      change P1Hier.Check (Rows.ncode M) (padIn j a b x ((List.ofFn w).take m)) (List.ofFn w).length t at hcheck
      rw [hp, List.length_ofFn] at hcheck
      obtain ⟨s, ht, _⟩ := (Rows.check_iff M (y u) g t).mp hcheck
      let v : S := ⟨u, s⟩
      have hd' : (List.ofFn w).drop m = encT tbl (τ v) ++ List.replicate r false := by
        change (List.ofFn w).drop m = encT tbl t ++ List.replicate r false at hd
        change t = τ v at ht
        rwa [ht] at hd
      have hr : g - (body v).length = r := by
        have hl := congrArg List.length hd'
        simp only [List.length_drop, List.length_ofFn, List.length_append, List.length_replicate] at hl
        simp only [body, List.length_append, List.length_ofFn]
        omega
      refine ⟨v, Finset.mem_univ _, List.ofFn_injective ?_⟩
      have hp' : (List.ofFn (pack v)).take m = (List.ofFn w).take m := (pref v).trans hp.symm
      have hs' : (List.ofFn (pack v)).drop m = (List.ofFn w).drop m := by
        rw [suff v, hd', hr]
      exact (List.take_append_drop m (List.ofFn (pack v))).symm.trans
        ((congrArg₂ List.append hp' hs').trans (List.take_append_drop m (List.ofFn w)))
  have total : (Finset.univ : Finset S).card = ∑ u : U, M.acc (y u) := by
    change Fintype.card ((u : U) × M.AccComp (y u)) = _
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro u _
    exact Nat.card_eq_fintype_card.symm
  exact bij.symm.trans total

end
end P1C1U.AstraC1U.Outer

#print axioms P1C1U.AstraC1U.Outer.count
