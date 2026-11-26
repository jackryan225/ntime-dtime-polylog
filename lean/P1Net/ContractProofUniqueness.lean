import P1Net.ContractProofArcAgreement

/-! Equality of all directed physical edges, from tables and the source rows of the routings. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z z' : RoutedGood V B L I σ ha bset) (A : SourceAgreement V B L I σ ha bset z z')

local notation "outW" => slotOut V B I σ ha
local notation "inW" => slotIn V B I σ ha
local notation "Wx" => strWidth V B
local notation "Wt" => tupWidth V B

section Uniqueness
include A

theorem same_center_word (ι : Fin I) (l : BitWord h) :
    outW z.val (ι,.tabC) l 0 Wt = outW z'.val (ι,.tabC) l 0 Wt := by
  rw [(center_spec V B L I σ ha bset z ι l).1, (center_spec V B L I σ ha bset z' ι l).1, A.center]

theorem same_path_word (ι : Fin I) (c : Ext V.K) (l : BitWord h)
    (hm : netMate I σ ((ι,Loc.tabP c),1) ≠ none) :
    outW z.val (ι,.tabP c) l 1 Wt = outW z'.val (ι,.tabP c) l 1 Wt := by
  rw [(path_factor V B L I σ ha bset z ι l c).1 hm, (path_factor V B L I σ ha bset z' ι l c).1 hm,
    path_eq_center V B L I σ ha bset z, path_eq_center V B L I σ ha bset z']
  exact same_center_word V B L I σ ha bset z z' A ι l

theorem same_ext_out (ι : Fin I) (c : Ext V.K) (l : BitWord h) (ho : Ext.isIn V c = false) :
    outW z.val (ι,.tabP c) l 2 Wx = outW z'.val (ι,.tabP c) l 2 Wx := by
  have h1 := external_eq V B L I σ ha bset z ι l c
  have h2 := external_eq V B L I σ ha bset z' ι l c
  simp only [ho, Bool.false_eq_true, ↓reduceIte] at h1 h2
  rw [A.center] at h1
  exact h1.trans h2.symm

theorem same_rt_words (ι : Fin I) (k : V.K) (c : Fin (2 * (h+3))) (π : BitWord 3) (l : BitWord h) :
    outW z.val (ι,.rt k c π) l 0 Wx = outW z'.val (ι,.rt k c π) l 0 Wx ∧
      (netMate I σ ((ι,Loc.rt k c π),1) ≠ none →
      outW z.val (ι,.rt k c π) l 1 Wx = outW z'.val (ι,.rt k c π) l 1 Wx) := by
  have hc := c.isLt
  have H := same_ct_arcs V B L I σ ha bset z z' A ι k c (by omega) (addrOf π l)
  simp only [ctOutRow, dif_pos hc, split_packed] at H
  refine ⟨H.1, fun hm => H.2 ?_⟩
  intro he
  have hn : ¬ (c : ℕ) + 1 < 2 * (h+3) := by omega
  apply hm
  simp [netMate, locMate, colSucc, hn, interMate]

theorem same_st_words (ι : Fin I) (c : Fin (2 * (h+1))) (π : BitWord 1) (l : BitWord h) :
    outW z.val (ι,.st c π) l 0 Wx = outW z'.val (ι,.st c π) l 0 Wx ∧
      (netMate I σ ((ι,Loc.st c π),1) ≠ none →
      outW z.val (ι,.st c π) l 1 Wx = outW z'.val (ι,.st c π) l 1 Wx) := by
  have hc := c.isLt
  have H := same_st_arcs V B L I σ ha bset z z' A ι c (by omega) (addrOf π l)
  simp only [stOutRow, dif_pos hc, split_packed] at H
  refine ⟨H.1, fun hm => H.2 ?_⟩
  intro he
  have hn : ¬ (c : ℕ) + 1 < 2 * (h+1) := by omega
  apply hm
  simp [netMate, locMate, colSucc, hn, interMate]

theorem same_port_out (ι : Fin I) (k : V.K) (δ : Fin 3) (l : BitWord h)
    (hm : netMate I σ ((ι,Loc.portOut k δ),1) ≠ none) :
    outW z.val (ι,.portOut k δ) l 1 Wx = outW z'.val (ι,.portOut k δ) l 1 Wx := by
  have attach : locMate (.portOut k δ : Loc V.K h) 0 = some (.rt k (rcolLast h) (code3 δ), 0) := rfl
  have H (q : RoutedGood V B L I σ ha bset) :
      outW q.val (ι,.portOut k δ) l 1 Wx = outW q.val (ι,.rt k (rcolLast h) (code3 δ)) l 0 Wx := by
    have copy : netMate I σ ((ι,Loc.portOut k δ),1) ≠ none →
      outW q.val (ι,.portOut k δ) l 1 Wx = inW q.val (ι,.portOut k δ) l 0 Wx :=
      q.property (((ι, Loc.portOut k δ), false), l)
    exact (copy hm).trans (slotIn_local V B I σ ha q.val ι attach rfl rfl l Wx)
  have eqLast := (same_rt_words V B L I σ ha bset z z' A ι k (rcolLast h) (code3 δ) l).1
  exact (H z).trans (eqLast.trans (H z').symm)

theorem same_state_out (ι : Fin I) (l : BitWord h) (hm : netMate I σ ((ι,Loc.eOut),1) ≠ none) :
    outW z.val (ι,.eOut) l 1 Wx = outW z'.val (ι,.eOut) l 1 Wx := by
  have attach : locMate (.eOut : Loc V.K h) 0 = some (.st (scolLast h) (code1 false), 0) := rfl
  have H (q : RoutedGood V B L I σ ha bset) :
      outW q.val (ι,.eOut) l 1 Wx = outW q.val (ι,.st (scolLast h) (code1 false)) l 0 Wx := by
    have copy : netMate I σ ((ι,Loc.eOut),1) ≠ none →
      outW q.val (ι,.eOut) l 1 Wx = inW q.val (ι,.eOut) l 0 Wx :=
      q.property (((ι, Loc.eOut), false), l)
    exact (copy hm).trans (slotIn_local V B I σ ha q.val ι attach rfl rfl l Wx)
  have eqLast := (same_st_words V B L I σ ha bset z z' A ι (scolLast h) (code1 false) l).1
  exact (H z).trans (eqLast.trans (H z').symm)

/-- For any fixed settings the source data determine every physical label. -/
theorem same_labels : z = z' := by
  have cases4 (s : Fin 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  apply Subtype.ext
  apply labels_ext V B I σ ha
  rintro ⟨ι,v⟩ l s
  by_cases hm : netMate I σ ((ι,v),s) = none
  · rw [slotOut_unmated V B I σ ha z.val hm, slotOut_unmated V B I σ ha z'.val hm]
  · cases v with
    | tabC =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact same_center_word V B L I σ ha bset z z' A ι l
      all_goals exact word_eq_of_width_zero rfl _ _
    | tabP c =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact word_eq_of_width_zero rfl _ _
      · exact same_path_word V B L I σ ha bset z z' A ι c l hm
      · cases c with
        | stIn => exact word_eq_of_width_zero rfl _ _
        | stOut => exact same_ext_out V B L I σ ha bset z z' A ι .stOut l rfl
        | cIn k δ => exact word_eq_of_width_zero rfl _ _
        | cOut k δ => exact same_ext_out V B L I σ ha bset z z' A ι (.cOut k δ) l rfl
      · exact word_eq_of_width_zero rfl _ _
    | portIn k δ =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact A.port ι k δ l
      all_goals exact word_eq_of_width_zero rfl _ _
    | portOut k δ =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact word_eq_of_width_zero rfl _ _
      · exact same_port_out V B L I σ ha bset z z' A ι k δ l hm
      all_goals exact word_eq_of_width_zero rfl _ _
    | rt k c π =>
      have H := same_rt_words V B L I σ ha bset z z' A ι k c π l
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact H.1
      · exact H.2 hm
      all_goals exact word_eq_of_width_zero rfl _ _
    | st c π =>
      have H := same_st_words V B L I σ ha bset z z' A ι c π l
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact H.1
      · exact H.2 hm
      all_goals exact word_eq_of_width_zero rfl _ _
    | eIn =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · have H := A.start ι (laneEquiv h l)
        simp only [startWord, Equiv.symm_apply_apply] at H
        exact H
      all_goals exact word_eq_of_width_zero rfl _ _
    | eOut =>
      rcases cases4 s with rfl | rfl | rfl | rfl
      · exact word_eq_of_width_zero rfl _ _
      · exact same_state_out V B L I σ ha bset z z' A ι l hm
      all_goals exact word_eq_of_width_zero rfl _ _

end Uniqueness

theorem same_labels_of_completion (route : Routes bset) (b b' : UnownedBits V B L I σ)
    (hw : completedGuess V B L I σ ha bset z b = completedGuess V B L I σ ha bset z' b') : z = z' :=
  same_labels V B L I σ ha bset z z' (agree_of_completion V B L I σ ha bset z z' route b b' hw)

end P1Net.AstraContract
