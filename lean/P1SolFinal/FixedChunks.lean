import P1ChkFinal.Skeleton
import OAI.Computability.IntegerMultiplication.Code.Slice

namespace P1ChkFinal.SolFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-- Partition the available bits into fields of the given width, including a truncated last field. -/
def fixedChunks (width : ℕ) (w : List Bool) : List (List Bool) :=
  if h : width = 0 ∨ w = [] then [] else
    w.take width :: fixedChunks width (w.drop width)
termination_by w.length
decreasing_by
  rw [List.length_drop]
  have hw : 0 < w.length := List.length_pos_iff.mpr (fun e => h (.inr e))
  have hk : 0 < width := Nat.pos_of_ne_zero (fun e => h (.inl e))
  omega

theorem fixedChunks_nil (width : ℕ) : fixedChunks width [] = [] := by
  rw [fixedChunks, dif_pos (Or.inr rfl)]

theorem fixedChunks_step (width : ℕ) (w : List Bool) (h : width ≠ 0) (hw : w ≠ []) :
    fixedChunks width w = w.take width :: fixedChunks width (w.drop width) := by
  rw [fixedChunks, dif_neg (not_or_intro h hw)]

private def chunksBody (cut : Cmd) : Cmd :=
  splitRoot 0 (fun _ => give 0 false)
    ((pack 0).join ((clone 1 0 2).join ((pack 0).join
      (cut.join (splitRoot 0 (fun _ => .pass)
        ((move 0 3 2).join ((.again 0 : Cmd).join ((move 3 0 2).join (pack 0)))))))))

private def scanWeight (k n : ℕ) : ℕ := n + (if n = 0 then 0 else k) + 1

private theorem weight_drop (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    scanWeight k (n - k) + k ≤ scanWeight k n := by
  by_cases h : k < n
  · simp only [scanWeight, show n - k ≠ 0 by omega, Nat.ne_of_gt hn, ite_false]
    omega
  · simp only [scanWeight, show n - k = 0 by omega, Nat.ne_of_gt hn, ite_true, ite_false]
    omega

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 3000 in
private theorem chunksRun {c : Cmd} {C : ℕ}
    (hc : ∀ (i : Tally × List Bool) env r,
      Fits env c (pile 0 (send i) r) (pile 0 (send (cutLists i)) r)
        (C * (size i.1 + size (cutLists i).1 + 1)))
    (u : Tally) (hu : 0 < u.length) (env : Env) :
    ∀ (w : List Bool) (r : Deck),
      Fits (chunksBody c :: env) (chunksBody c)
        (pile 1 (send u) (pile 0 (send w) r))
        (pile 1 (send u) (pile 0 (send (fixedChunks u.length w)) r))
        ((7 * C + 500) * scanWeight u.length w.length) := by
  suffices h : ∀ n : ℕ, ∀ (w : List Bool), w.length = n → ∀ (r : Deck),
      Fits (chunksBody c :: env) (chunksBody c)
        (pile 1 (send u) (pile 0 (send w) r))
        (pile 1 (send u) (pile 0 (send (fixedChunks u.length w)) r))
        ((7 * C + 500) * scanWeight u.length w.length) from fun w r => h w.length w rfl r
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn r
    subst n
    cases w with
    | nil =>
      rw [fixedChunks_nil]
      rw [pile_comm 1 _ r 0 _ (by decide), pile_comm 1 _ r 0 _ (by decide)]
      exact (fits_bit (b := false) (c := fun _ => give 0 false) (fits_give false ..)).mono
        (by simp only [scanWeight, List.length_nil, ite_true, Nat.add_zero, Nat.zero_add, Nat.mul_one]; omega)
    | cons a w =>
      let W := a :: w
      let G := chunksBody c :: env
      let R := pile 1 (send u) r
      let p := W.take u.length
      let t := W.drop u.length
      have hp := fits_pack (send a) (send w) R 0 G
      have hd := fits_clone (i := 1) (j := 0) (u := 2) (by decide) (by decide) (by decide)
        (send u) G (pile 0 (send W) r)
      rw [pile_comm 1 _ r 0 (send W) (by decide),
        pile_comm 1 _ (pile 0 (send W) r) 0 (send u) (by decide),
        pile_comm 1 _ r 0 (send W) (by decide)] at hd
      have hpack := fits_pack (send u) (send W) R 0 G
      have hcut := hc (u, W) G R
      change Fits G c (pile 0 (.fork (send u) (send W)) R)
        (pile 0 (.fork (send p) (send t)) R) (C * (size u + size p + 1)) at hcut
      have hmv := fits_move (i := 0) (j := 3) (u := 2) (by decide) (by decide)
        (send p) G (pile 0 (send t) R)
      have hlt : t.length < W.length := by
        simp only [t, W, List.length_drop, List.length_cons]
        omega
      have hrec := ih t.length hlt t rfl (pile 3 (send p) r)
      rw [pile_comm 1 _ (pile 3 (send p) r) 0 (send t) (by decide),
        pile_comm 1 _ (pile 3 (send p) r) 0 (send (fixedChunks u.length t)) (by decide),
        pile_comm 1 _ r 3 _ (by decide)] at hrec
      rw [pile_comm 3 _ R 0 (send t) (by decide)] at hmv
      have hb := fits_move (i := 3) (j := 0) (u := 2) (by decide) (by decide)
        (send p) G (pile 0 (send (fixedChunks u.length t)) R)
      rw [pile_comm 3 _ R 0 (send (fixedChunks u.length t)) (by decide)] at hb
      have hf := fits_pack (send p) (send (fixedChunks u.length t)) R 0 G
      have H := hp.join (hd.join (hpack.join (hcut.join
        (fits_pair (c := fun _ => Prog.pass) (hmv.join (hrec.again0.join (hb.join hf)))))))
      rw [fixedChunks_step u.length W (Nat.ne_of_gt hu) (fun h => nomatch h)]
      rw [pile_comm 1 _ r 0 (send W) (by decide),
        pile_comm 1 _ r 0 (send (p :: fixedChunks u.length t)) (by decide)]
      refine (fits_pair (c := fun _ => give 0 false) H).mono ?_
      have hpl : p.length ≤ u.length := List.length_take_le _ _
      have hsp : C * (size u + size p + 1) ≤ C * (7 * u.length) := by
        apply Nat.mul_le_mul_left
        simp only [size_tally, size_listBool]
        omega
      have hd := weight_drop u.length W.length hu (by simp only [W, List.length_cons, Nat.zero_lt_succ])
      have hw : t.length = W.length - u.length := List.length_drop
      rw [← hw] at hd
      have hD := Nat.mul_le_mul_left (7 * C + 500) hd
      simp only [W] at hD
      rw [show C * (7 * u.length) = 7 * (C * u.length) by ring] at hsp
      have hU : (send u).count = size u := rfl
      have hP : (send p).count = size p := rfl
      simp only [hU, hP, size_tally, size_listBool, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hsp hD ⊢
      omega

/-- Read fixed-width fields with one ruler. Each recursive call consumes a field of the witness. -/
theorem fixedChunks_task :
    Task (fun i : {i : Tally × List Bool // 0 < i.1.length} => size i.val)
      (fun i => send i.val) (fun i => send (fixedChunks i.val.1.length i.val.2)) := by
  obtain ⟨c, C, hc⟩ := Computes.cut (X := Bool)
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join ((Prog.tie (chunksBody c)).join (discard 1))),
    7 * C + 600, ?_⟩
  rintro ⟨⟨u, w⟩, hu⟩ env r
  have H := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) (send u) env (pile 0 (send w) r)
  have J := (chunksRun hc u hu env w r).tie
  have D := fits_discard 1 (send u) env (pile 0 (send (fixedChunks u.length w)) r)
  refine (fits_pair (H.join (J.join D))).mono ?_
  have hW : scanWeight u.length w.length ≤ size u + size w := by
    unfold scanWeight
    simp only [size_tally, size_listBool]
    split_ifs <;> omega
  have hC := Nat.mul_le_mul_left (7 * C + 500) hW
  simp only [show (send u).count = size u from rfl, size_prod, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_one] at hC ⊢
  omega

end P1ChkFinal.SolFinal
