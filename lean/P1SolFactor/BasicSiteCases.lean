import P1SolFactor.BasicSiteTest
import P1SolFactor.RoutedWidths

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net SolRows
open scoped Classical

noncomputable section

section Half

variable {V : FiniteMultiTapeMachine} {R : Type} {a h : ℕ}
  (X : State a h) (u : X.network.Site) (ha : 4 ≤ 2 ^ a) (z : X.network.Half u)

def basicHalfOK : SiteRule V → Prop
  | .free => True
  | .copy o i => paddedAgree (decodeInputBit (R := R))
    ((fieldBits X u z true (i.castLE ha)).map inputBit)
    ((fieldBits X u z false (o.castLE ha)).map inputBit)
  | .fixed word => paddedAgree (decodeInputBit (R := R))
    ((fieldBits X u z false ((0 : Fin 4).castLE ha)).map inputBit) (word.map inputBit)
  | _ => False

end Half

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : RouteSettings) {R : Type}

local notation "X" => rnState V B I σ ha
local notation "Wx" => strWidth V B

omit [NeZero B] in
private theorem copyHalfOK_iff (ι : Fin I) (loc : Loc V.K h) (lane : BitWord h)
    (z : (X).network.Half (((ι, loc), false), lane)) (o i : Fin 4)
    (hc : loc ≠ .tabC) (hp : ∀ c, loc ≠ .tabP c) :
    let u := (((ι, loc), false), lane)
    basicHalfOK (R := R) X u ha z (.copy o i : SiteRule V) ↔
      outWord X u z (o.castLE ha) Wx = inWord X u z (i.castLE ha) Wx := by
  have hin := slotWidth_in_le_string V B I σ ha (ι, loc) i lane (fun c he => (hp c he).elim)
  have hout := slotWidth_out_le_string V B I σ ha (ι, loc) o lane
    (fun he => (hc he).elim) (fun c he => (hp c he).elim)
  exact (paddedAgree_in_out (R := R) X _ z _ _ Wx hin hout).trans eq_comm

/-- The three basic rules read exactly the fields constrained by the network factor. -/
theorem rnSiteOK_iff_basic (u : (X).network.Site) (z : (X).network.Half u)
    (hb : IsBasicRule (siteRuleWith V B L I σ ha bset u)) :
    rnSiteOK V B L I σ ha bset u z ↔ basicHalfOK (R := R) X u ha z (siteRuleWith V B L I σ ha bset u) := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin
  · cases loc with
    | tabC | tabP _ | rt _ _ _ | st _ _ => exact False.elim hb
    | portIn k δ =>
      by_cases hm : netMate I σ ((ι, Loc.portIn k δ), 1) = none
      · simp [siteRuleWith, siteRule, hm, IsBasicRule] at hb
      · simpa [rnSiteOK, siteRuleWith, siteRule, hm, basicHalfOK] using
          (copyHalfOK_iff (R := R) V B I σ ha ι (.portIn k δ) lane z 0 1 (by simp) (by simp)).symm
    | portOut k δ =>
      by_cases hm : netMate I σ ((ι, Loc.portOut k δ), 1) = none
      · simp [rnSiteOK, siteRuleWith, siteRule, hm, basicHalfOK]
      · simpa [rnSiteOK, siteRuleWith, siteRule, hm, basicHalfOK] using
          (copyHalfOK_iff (R := R) V B I σ ha ι (.portOut k δ) lane z 1 0 (by simp) (by simp)).symm
    | eOut =>
      by_cases hm : netMate I σ ((ι, Loc.eOut), 1) = none
      · simp [rnSiteOK, siteRuleWith, siteRule, hm, basicHalfOK]
      · simpa [rnSiteOK, siteRuleWith, siteRule, hm, basicHalfOK] using
          (copyHalfOK_iff (R := R) V B I σ ha ι .eOut lane z 1 0 (by simp) (by simp)).symm
    | eIn =>
      by_cases hi : ι.val = 0
      · have hout := slotWidth_out_le_string V B I σ ha (ι, Loc.eIn) 0 lane (by simp) (by simp)
        by_cases hl : (laneEquiv h lane).val = 0
        · simpa [rnSiteOK, siteRuleWith, siteRule, hi, hl, basicHalfOK] using
            (paddedAgree_out_full (R := R) X _ z _ Wx hout (encS V B V.initialState (fun _ => finOfInt B 0))).symm
        · simpa [rnSiteOK, siteRuleWith, siteRule, hi, hl, basicHalfOK] using
            (paddedAgree_out_zero (R := R) X _ z _ Wx hout).symm
      · simpa [rnSiteOK, siteRuleWith, siteRule, hi, basicHalfOK] using
          (copyHalfOK_iff (R := R) V B I σ ha ι .eIn lane z 0 1 (by simp) (by simp)).symm
  · simp [rnSiteOK, siteRuleWith, basicHalfOK]

omit [NeZero B] in
theorem initial_slot_width (ι : Fin I) (lane : BitWord h) :
    slotWidth X (((ι, Loc.eIn), false), lane) false ((0 : Fin 4).castLE ha) = Wx := by
  have hm : netMate I σ ((ι, Loc.eIn), 0) = some ((ι, .st (scol0 h) (code1 false)), 2) := by
    simp [netMate, locMate]
  rw [slotWidth_out_mated V B I σ ha hm lane]
  simp [baseWidth]

/-- The only nonempty fixed header word is the full state word at the chain start. -/
theorem siteRuleWith_fixed_length (u : (X).network.Site) (word : List Bool)
    (hword : siteRuleWith V B L I σ ha bset u = .fixed word) : word.length ≤ halfWidthSum X u := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin
  · cases loc with
    | tabC | tabP _ | rt _ _ _ | st _ _ => contradiction
    | portIn k δ =>
      by_cases hm : netMate I σ ((ι, Loc.portIn k δ), 1) = none <;>
        simp [siteRuleWith, siteRule, hm] at hword
    | portOut k δ =>
      by_cases hm : netMate I σ ((ι, Loc.portOut k δ), 1) = none <;>
        simp [siteRuleWith, siteRule, hm] at hword
    | eOut =>
      by_cases hm : netMate I σ ((ι, Loc.eOut), 1) = none <;>
        simp [siteRuleWith, siteRule, hm] at hword
    | eIn =>
      by_cases hi : ι.val = 0
      · by_cases hl : (laneEquiv h lane).val = 0
        · have he : List.ofFn (encS V B V.initialState (fun _ => finOfInt B 0)) = word := by
            simpa [siteRuleWith, siteRule, hi, hl] using hword
          rw [← he, List.length_ofFn, ← initial_slot_width V B I σ ha ι lane]
          exact slotWidth_le_total X _ false _
        · have he : [] = word := by simpa [siteRuleWith, siteRule, hi, hl] using hword
          rw [← he, List.length_nil]
          exact Nat.zero_le _
      · simp [siteRuleWith, siteRule, hi] at hword
  · simp [siteRuleWith] at hword

end RoutedSite

end

end P1SolFactor.SolHalf
