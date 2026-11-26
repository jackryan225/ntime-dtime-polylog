import P1Net.ContractProofAgreement

/-! Uniqueness of the intermediate words of both physical routings from agreement of their sources. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

section ContentRows

noncomputable def ctInRow (z : Labels V B I σ ha) (ι : Fin I) (k : V.K) (s : Fin 4) : WordAt (3 + h) (strWidth V B) :=
  fun c x => if hc : c < 2 * (h + 3) then
    slotIn V B I σ ha z (ι, .rt k ⟨c, hc⟩ (addrSplit (t := 3) x).1) (addrSplit (t := 3) x).2 s (strWidth V B)
    else fun _ => false

noncomputable def ctOutRow (z : Labels V B I σ ha) (ι : Fin I) (k : V.K) (s : Fin 4) : WordAt (3 + h) (strWidth V B) :=
  fun c x => if hc : c < 2 * (h + 3) then
    slotOut V B I σ ha z (ι, .rt k ⟨c, hc⟩ (addrSplit (t := 3) x).1) (addrSplit (t := 3) x).2 s (strWidth V B)
    else fun _ => false

variable (z : RoutedGood V B L I σ ha bset) (ι : Fin I) (k : V.K)

local notation "ins" => ctInRow V B I σ ha z.val ι k
local notation "outs" => ctOutRow V B I σ ha z.val ι k

theorem ct_rows_ok (c : ℕ) (hc : c < 2 * (3 + h)) (x : Routing.Addr (3 + h)) :
    routeOK (bset (3 + h) (accAddr I σ ι k)) c x (ins 2 c x) (ins 3 c x) (outs 0 c x) (outs 1 c x) := by
  have hc' : c < 2 * (h + 3) := by omega
  let p := addrSplit (t := 3) (h := h) x
  let v : Fin I × Loc V.K h := (ι, .rt k ⟨c, hc'⟩ p.1)
  have H := z.property ((v, false), p.2)
  change routeOK (bset (3 + h) (accAddr I σ ι k)) c (addrOf p.1 p.2) _ _ _ _ at H
  have he : addrOf p.1 p.2 = x := packed_split (t := 3) (h := h) x
  rw [he] at H
  simp only [ctInRow, ctOutRow, dif_pos hc']
  exact H

theorem ct_straight (c : ℕ) (hc : c + 1 < 2 * (3 + h)) (x : Routing.Addr (3 + h)) :
    ins 2 (c + 1) x = outs 0 c x := by
  have h0 : c < 2 * (h + 3) := by omega
  have h1 : c + 1 < 2 * (h + 3) := by omega
  let π := (addrSplit (t := 3) (h := h) x).1
  have hp : colPred (⟨c + 1, h1⟩ : Fin (2 * (h + 3))) = some ⟨c, h0⟩ := by simp [colPred]
  have hm : locMate (.rt k ⟨c + 1, h1⟩ π : Loc V.K h) 2 = some (.rt k ⟨c, h0⟩ π, 0) := by
    simp [locMate, hp]
  simp only [ctInRow, ctOutRow, dif_pos h1, dif_pos h0]
  exact slotIn_local V B I σ ha z.val ι hm rfl rfl _ _

theorem ct_cross (c : ℕ) (hc : c + 1 < 2 * (3 + h)) (x : Routing.Addr (3 + h)) :
    ins 3 (c + 1) x = outs 1 c (x + Routing.flip (3 + h) c) := by
  have h0 : c < 2 * (h + 3) := by omega
  have h1 : c + 1 < 2 * (h + 3) := by omega
  let π := (addrSplit (t := 3) (h := h) x).1
  have hp : colPred (⟨c + 1, h1⟩ : Fin (2 * (h + 3))) = some ⟨c, h0⟩ := by simp [colPred]
  have hm : locMate (.rt k ⟨c + 1, h1⟩ π : Loc V.K h) 3 =
      some (.rt k ⟨c, h0⟩ (π + tyFlip 3 h c), 1) := by simp [locMate, hp]
  have hn := local_mate V I σ ι hm
  have hd : netDisp I σ ((ι, Loc.rt k ⟨c + 1, h1⟩ π), 3) = lnFlip 3 h c := by
    simp [netDisp, hn, disp1]
  simp only [ctInRow, ctOutRow, dif_pos h1, dif_pos h0, split_flip]
  simpa only [hd] using slotIn_mate V B I σ ha z.val hn (addrSplit (t := 3) (h := h) x).2 (strWidth V B)

end ContentRows

theorem sends_unique {m W : ℕ} [NeZero m] (s : Routing.Settings m) (c : ℕ) (x : Routing.Addr m)
    {w u v u' v' : Fin W → Bool} (hu : sends s c x w u v) (hu' : sends s c x w u' v') :
    u = u' ∧ (c + 1 ≠ 2 * m → v = v') := by
  by_cases hl : c + 1 = 2 * m
  · simp only [sends, if_pos hl] at hu hu'
    exact ⟨hu.trans hu'.symm, fun hf => (hf hl).elim⟩
  · cases hs : s c (Routing.rep m c x) <;>
      simp only [sends, if_neg hl, hs, Bool.false_eq_true, ↓reduceIte] at hu hu'
    · exact ⟨hu.1.trans hu'.1.symm, fun _ => hu.2.trans hu'.2.symm⟩
    · exact ⟨hu.2.trans hu'.2.symm, fun _ => hu.1.trans hu'.1.symm⟩

variable (z z' : RoutedGood V B L I σ ha bset) (A : SourceAgreement V B L I σ ha bset z z')

include A in
theorem same_content_input (ι : Fin I) (k : V.K) (x : Fin 8 × Fin (2 ^ h)) :
    contentInput V B I σ ha z.val ι k x = contentInput V B I σ ha z'.val ι k x := by
  obtain ⟨d,j⟩ := x
  by_cases h3 : (d : ℕ) < 3
  · let δ : Fin 3 := ⟨d,h3⟩
    have he : typ δ = d := Fin.ext (typ_val d.isLt)
    rw [← he, input_from_port V B L I σ ha bset z, input_from_port V B L I σ ha bset z']
    exact A.port ι k δ _
  · by_cases h6 : (d : ℕ) < 6
    · let δ : Fin 3 := ⟨(d : ℕ) - 3, by omega⟩
      have he : typ (3 + δ) = d := typ_window_eq d h3 h6
      rw [← he, input_from_table V B L I σ ha bset z, input_from_table V B L I σ ha bset z', A.center]
    · rw [input_dummy V B L I σ ha bset z ι k d (by omega) j,
        input_dummy V B L I σ ha bset z' ι k d (by omega) j]

include A in
theorem same_ct_source (ι : Fin I) (k : V.K) :
    ctInRow V B I σ ha z.val ι k 2 0 = ctInRow V B I σ ha z'.val ι k 2 0 := by
  funext x
  obtain ⟨⟨d,j⟩,rfl⟩ := (itemEquiv h).surjective x
  have h0 : 0 < 2 * (h + 3) := by omega
  simp only [ctInRow, dif_pos h0, item_addr, split_packed]
  exact same_content_input V B L I σ ha bset z z' A ι k (d,j)

include A in
theorem same_st_source (ι : Fin I) :
    stInRow V B I σ ha z.val ι 2 0 = stInRow V B I σ ha z'.val ι 2 0 := by
  funext x
  obtain ⟨⟨d,j⟩,rfl⟩ := (stItemEquiv h).surjective x
  have hd : d = 0 ∨ d = 1 := by revert d; decide
  rcases hd with rfl | rfl
  · exact (state_input_zero V B L I σ ha bset z ι j).trans
      ((A.start ι j).trans (state_input_zero V B L I σ ha bset z' ι j).symm)
  · have he := congrArg (fun d : LocalIn V B => encS V B (evolve d).q (evolve d).off)
      (A.center ι ((laneEquiv h).symm j))
    exact (state_input_one V B L I σ ha bset z ι j).trans
      (he.trans (state_input_one V B L I σ ha bset z' ι j).symm)

include A in
theorem same_ct_arcs (ι : Fin I) (k : V.K) (c : ℕ) (hc : c < 2 * (3+h)) (x : Routing.Addr (3+h)) :
    ctOutRow V B I σ ha z.val ι k 0 c x = ctOutRow V B I σ ha z'.val ι k 0 c x ∧
    (c + 1 ≠ 2 * (3+h) → ctOutRow V B I σ ha z.val ι k 1 c x = ctOutRow V B I σ ha z'.val ι k 1 c x) := by
  let s := bset (3+h) (accAddr I σ ι k)
  have H (q : RoutedGood V B L I σ ha bset) := (switch_normal_form s
    (ctInRow V B I σ ha q.val ι k 2) (ctInRow V B I σ ha q.val ι k 3)
    (ctOutRow V B I σ ha q.val ι k 0) (ctOutRow V B I σ ha q.val ι k 1)
    (ct_rows_ok V B L I σ ha bset q ι k) (ct_straight V B L I σ ha bset q ι k)
    (ct_cross V B L I σ ha bset q ι k) c hc x).2
  have h1 := H z
  rw [same_ct_source V B L I σ ha bset z z' A ι k] at h1
  exact sends_unique s c x h1 (H z')

include A in
theorem same_st_arcs (ι : Fin I) (c : ℕ) (hc : c < 2 * (1+h)) (x : Routing.Addr (1+h)) :
    stOutRow V B I σ ha z.val ι 0 c x = stOutRow V B I σ ha z'.val ι 0 c x ∧
    (c + 1 ≠ 2 * (1+h) → stOutRow V B I σ ha z.val ι 1 c x = stOutRow V B I σ ha z'.val ι 1 c x) := by
  let s := bset (1+h) (stAddr h)
  have H (q : RoutedGood V B L I σ ha bset) := (switch_normal_form s
    (stInRow V B I σ ha q.val ι 2) (stInRow V B I σ ha q.val ι 3)
    (stOutRow V B I σ ha q.val ι 0) (stOutRow V B I σ ha q.val ι 1)
    (st_rows_ok V B L I σ ha bset q ι) (st_straight V B L I σ ha bset q ι)
    (st_cross V B L I σ ha bset q ι) c hc x).2
  have h1 := H z
  rw [same_st_source V B L I σ ha bset z z' A ι] at h1
  exact sends_unique s c x h1 (H z')

end P1Net.AstraContract
