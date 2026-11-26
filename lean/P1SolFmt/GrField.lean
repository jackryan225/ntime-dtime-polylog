import P1ChkFinal.GreedyFieldTarget

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkGreedy P1SolGreedy P1Int.P11
open P1ChkFinal.C7R P1ChkFinal.GreedyBridge

namespace P1SolGrField.Sol

private theorem allIndices_iff {ni count modulus lv : ℕ} {check family : ℕ → Prop}
    (hfit : count ≤ ni) (hcheck : ∀ i, check i ↔ family i)
    (hout : ∀ i, count ≤ i → family i) :
    (∀ i < ni, i < count → i % modulus = lv → check i) ↔
      (∀ i, i % modulus = lv → family i) := by
  constructor
  · intro h i hi
    by_cases hcnt : i < count
    · exact (hcheck i).mp (h i (lt_of_lt_of_le hcnt hfit) hcnt hi)
    · exact hout i (Nat.le_of_not_gt hcnt)
  · intro h i _ _ hi
    exact (hcheck i).mpr (h i hi)

private theorem levelIndex_iff {ni count modulus lv : ℕ} {check family : ℕ → Prop}
    (hfit : count ≤ ni) (hcount : count ≤ modulus) (hlv : lv < count)
    (hcheck : ∀ i, check i ↔ family i) :
    (∀ i < ni, i < count → i % modulus = lv → check i) ↔ family lv := by
  constructor
  · intro h
    exact (hcheck lv).mp (h lv (lt_of_lt_of_le hlv hfit) hlv
      (Nat.mod_eq_of_lt (lt_of_lt_of_le hlv hcount)))
  · intro h i _ hi hmod
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hi hcount)] at hmod
    exact (hcheck i).mpr (hmod ▸ h)

private theorem allCodes_iff {Q : ℕ → Prop} :
    (∀ c, 4 ≤ c → c ≤ 8 → Q c) ↔ Q 4 ∧ Q 5 ∧ Q 6 ∧ Q 7 ∧ Q 8 := by
  constructor
  · intro h
    exact ⟨h 4 (by omega) (by omega), h 5 (by omega) (by omega),
      h 6 (by omega) (by omega), h 7 (by omega) (by omega), h 8 (by omega) (by omega)⟩
  · rintro ⟨h4, h5, h6, h7, h8⟩ c hlo hhi
    have hc : c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl
    exacts [h4, h5, h6, h7, h8]

private theorem tuple_of_stages {k : Type} [Field k] {S : BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (H : FixedRecords Bt κ hκ V a b x d bigBias termBias)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (lmap : F →ₗ[ZMod 2] ZMod 2)
    (Wof : List Bool → List Bool → ℕ → F) {lv : ℕ}
    (hlv : lv < (fixedDims Bt V a b x d bigBias termBias).top)
    (u : Fin (fixedM Bt a b x) → Bool)
    (hpre : ∀ j < 4 + 2 * lv, (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs lmap Wof).P
      (fixedDims Bt V a b x d bigBias termBias).top j u) :
    ∃ t : (fixedCD Bt κ hκ V a b x).Tup d, SecEq Bt κ hκ V a b x d bigBias termBias H u t secTrit ∧
      LevUpTo Bt κ hκ V a b x d bigBias termBias H u t lv ∧
      ∀ kk : Mem, panelKind kk = true →
        SecEq Bt κ hκ V a b x d bigBias termBias H u t (secLev lv kk) := by
  let G := fixedGroups Bt κ hκ V a b x d bigBias termBias H bs lmap Wof
  let top := (fixedDims Bt V a b x d bigBias termBias).top
  change lv < top at hlv
  change ∀ j < 4 + 2 * lv, G.P top j u at hpre
  cases lv with
  | zero =>
    have h := hpre 3 (by omega)
    rw [G.P_three] at h
    change c4G Bt κ hκ V a b x d bigBias termBias H u at h
    obtain ⟨t, ht, hpanel⟩ := h
    exact ⟨t, ht, fun j hj => False.elim (Nat.not_lt_zero j hj), hpanel⟩
  | succ j =>
    have hj : j < top := by omega
    have h := hpre (5 + 2 * j) (by omega)
    rw [G.P_c10 hj] at h
    exact h

end P1SolGrField.Sol

open P1SolGrField.Sol

set_option maxHeartbeats 800000 in
theorem P1SolGrField.greedyField {k : Type} [Field k] {S : OAI.Computability.VPVNP.Compression.BlockSchedule k}
    (Bt : S.Templates) {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    (hH : P1Int.P11.TrueHFacts Bt κ hκ V a b x d bigBias termBias) :
    P1ChkFinal.GreedyField.GreedyFieldTarget Bt κ hκ V a b x d bigBias termBias hH := by
  intro hBS hBR bs lmap Wof ck ni cnt hck4 hck5 hck6 hck7 hck8 hc4 hc5 hc6 hc7 hc8 hfit lv hlv u hpre
  let Dn := gdims Bt V a b d bigBias termBias
  let D := Dn x.length
  let ag := genuineAg Dn
  let w := List.ofFn u
  let H := trueH Bt κ hκ V a b x d bigBias termBias hH
  let G := greedyG Bt κ hκ V a b x d bigBias termBias H lv u
  change lv < D.top at hlv
  change (∀ c, 4 ≤ c → c ≤ 8 → ∀ i < ni, i < cnt c → i % 2 ^ P1ChkGreedy.levBits D = lv → ck c u i = true) ↔ G
  refine allCodes_iff.trans ?_
  have h4 := allIndices_iff (modulus := 2 ^ P1ChkGreedy.levBits D) (lv := lv)
    (hfit 4 (by omega) (by omega)) (hck4 u)
    (fun i hi => C5fam_out Dn x w (hc4 ▸ hi))
  have h5 := allIndices_iff (modulus := 2 ^ P1ChkGreedy.levBits D) (lv := lv)
    (hfit 5 (by omega) (by omega)) (hck5 u)
    (fun i hi => C6fam_out Dn ag x w (hc5 ▸ hi))
  have h6 := allIndices_iff (modulus := 2 ^ P1ChkGreedy.levBits D) (lv := lv)
    (hfit 6 (by omega) (by omega)) (hck6 u)
    (fun i hi => C7all_out S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink Dn ag x w (hc6 ▸ hi))
  have h7 := allIndices_iff (modulus := 2 ^ P1ChkGreedy.levBits D) (lv := lv)
    (hfit 7 (by omega) (by omega)) (hck7 u)
    (fun i hi => C8fam_out Bt.shrink Dn ag x w (hc7 ▸ hi))
  have hcount : cnt 8 ≤ 2 ^ P1ChkGreedy.levBits D := by
    rw [hc8]
    exact lev_lt D (ℓ := D.top) (Nat.le_refl _)
  have htime : lv < cnt 8 := by
    rw [hc8]
    exact Nat.lt_succ_of_lt hlv
  have h8 := levelIndex_iff (hfit 8 (by omega) (by omega)) hcount htime (hck8 u)
  refine (and_congr h4 (and_congr h5 (and_congr h6 (and_congr h7 h8)))).trans ?_
  obtain ⟨t, ht, hlevels, hpanel⟩ :=
    tuple_of_stages Bt κ hκ V a b x d bigBias termBias H bs lmap Wof hlv u hpre
  cases hsh : (D.lv lv).shrink with
  | false =>
    obtain ⟨g, X, hN, hK, hg, hP, hbridge⟩ := hBR lv hlv hsh u t ht hlevels hpanel
    exact greedy_refresh_step S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink Dn ag x w X
      (Nat.le_of_lt hlv) hsh hN hK hg hP True G (fun _ => hbridge) True.intro
  | true =>
    obtain ⟨a', g, X, hN, hslots, hag, hP, hbridge⟩ := hBS lv hlv hsh u t ht hlevels hpanel
    have hstep := P1ChkFinal.GreedyIndex.greedy_shrink_step S.graph (Nat.two_pow_pos S.expanderExponent)
      (S.port_bound.connected_and_pos S.port_order).1 Bt.refresh Bt.shrink Dn ag x w X
      (Nat.le_of_lt hlv) hsh hN hslots hag hP True G (fun _ => hbridge) True.intro
    rw [P1ChkFinal.GreedyIndex.C9_all_iff] at hstep
    exact hstep

#print axioms P1SolGrField.greedyField
