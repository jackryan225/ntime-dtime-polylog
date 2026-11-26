import P1C1U.OuterCount
import P1Wrap.W3Done
import P1Hier.W2Link
import OAI.Computability.MultitapeWeakETH.Price

namespace P1C1U.AstraC1U

open Classical in
private theorem sum_mod_two {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % 2 = (s.filter fun i => Odd (f i)).card % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hn : i ∉ s.filter (fun k => Odd (f k)) := fun h => hi (Finset.mem_filter.mp h).1
    by_cases h : Odd (f i)
    · have h₁ := Nat.odd_iff.mp h
      rw [Finset.sum_insert hi, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem hn]
      omega
    · have h₀ : f i % 2 ≠ 1 := fun he => h (Nat.odd_iff.mpr he)
      rw [Finset.sum_insert hi, Finset.filter_insert, if_neg h]
      omega

open Classical in
theorem odd_sum_filter {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    Odd (∑ i, f i) ↔ Odd (Finset.univ.filter fun i => Odd (f i)).card := by
  calc
    Odd (∑ i, f i) ↔ (∑ i, f i) % 2 = 1 := Nat.odd_iff
    _ ↔ (Finset.univ.filter fun i => Odd (f i)).card % 2 = 1 := by rw [sum_mod_two]
    _ ↔ _ := Nat.odd_iff.symm

end P1C1U.AstraC1U

open C1Challenge P1Int P1Wrap.W3 P1C1U.AstraC1U

set_option maxHeartbeats 4000000 in
theorem P1C1U.caseB (p11 : P1Int.LemmaPOfPort OAI.Computability.MultitapeWeakETH.PortTwo)
    (port : OAI.Computability.MultitapeWeakETH.PortTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ C1Challenge.ParTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) := by
  classical
  obtain ⟨s, j, _, hs, hP⟩ := p11 port
  have hsj : s = sOf j := hs
  rw [hsj] at hP
  obtain ⟨D, ⟨U₀, a, b₀, hU₀⟩, hDno⟩ := P1Hier.parityHierarchy (qOf j) (one_le_qOf j)
  obtain ⟨b, hb, hU⟩ : ∃ b : ℕ, 1 ≤ b ∧
      ParDecidesFrom U₀ D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 :=
    ⟨b₀ + 1, by omega, parDecidesFrom_mono_clock hU₀ (fun n => Nat.mul_le_mul_right _ (by omega))⟩
  obtain ⟨A, hA, R, letter, hinj, ans, c, n₁, hR⟩ := hP D U₀ a b 0 hb hU
  let L := Lin j a b R letter ans c n₁
  have innerV := innerVerifier_of_prog (innerProg_of_impl (Inner.innerImpl_of easy_unG j a b))
  have hNT : NTIMELinLog L :=
    innerV A hA R letter hinj ans c n₁ (fun x hx u γ => (hR x hx).1 u γ)
  refine ⟨sigmaOf j, sigmaOf_pos j, fun y => !L y, ?_, ?_⟩
  · apply (C1UGuards.coNTIMELinLog_iff _).mpr
    simpa only [Bool.not_not] using hNT
  rintro ⟨M, C, hM⟩
  let K := (Rows.ncode M).table.length + 1
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1 (fits j a b K C)
  obtain ⟨V, B, hver⟩ := Outer.verifier (Rows.ncode M) j a b
  apply hDno V (2 * B) (max n₂ n₁)
  intro x hx
  have hx₁ := le_of_max_le_right hx
  have hx₂ := le_of_max_le_left hx
  let m := lpM2 (sOf j) a b x.length
  let U := Fin m → Bool
  let y (u : U) := padIn j a b x (List.ofFn u)
  let g := G (qOf j) x.length
  let ν := nuOf j a b x.length
  let T := ⌊C * ((ν : ℝ) * Real.logb 2 ν ^ sigmaOf j + 1)⌋₊
  have hfit : m + K * (T + 1) + ν + x.length + 1 ≤ g := hn₂ x.length hx₂
  let v (w : Fin g → Bool) := Outer.verdict (Rows.ncode M) j a b (List.ofFn w) x
  let t (w : Fin g → Bool) := 2 * B * g + (withGuess (List.ofFn w) x).length
  have ver (w : Fin g → Bool) : HaltsWithin V (withGuess (List.ofFn w) x) (v w) (t w) := by
    have hw := hver (List.ofFn w) x
    rw [List.length_ofFn] at hw
    apply P1Wrap.Bridge.haltsWithin_mono hw
    have hm : B * (g + ν + 1) ≤ B * (2 * g) := Nat.mul_le_mul_left _ (by omega)
    have he : B * (2 * g) = 2 * B * g := by ring
    change B * (g + ν + 1) ≤ 2 * B * g + (withGuess (List.ofFn w) x).length
    omega
  refine ⟨fun w => ⟨v w, ver w⟩, ?_⟩
  have spec (u : U) : (∀ d, ¬ M.Reach (M.init (y u)) (T + 1) d) ∧
      (L (y u) = false ↔ Odd (M.acc (y u))) := by
    obtain ⟨t₀, ht, hbound, hp⟩ := hM (y u)
    have hy : (y u).length = ν := length_padIn j a b x (List.ofFn u) List.length_ofFn
    rw [hy] at ht
    have hle : t₀ ≤ T := Nat.le_floor ht
    refine ⟨fun d hr => ?_, ?_⟩
    · have hbad := reach_length_le hbound hr
      omega
    · change (!L (y u)) = true ↔ Odd (M.acc (y u)) at hp
      simpa only [Bool.not_eq_true'] using hp
  have room : m + K * (T + 1) ≤ g := by omega
  have hcount := Outer.count M j a b x g T (fun u => (spec u).1) room
  have hselect : (Finset.univ.filter fun w : Fin g → Bool =>
      HaltsWithin V (withGuess (List.ofFn w) x) true (t w)) =
      (Finset.univ.filter fun w : Fin g → Bool => v w = true) := by
    apply Finset.filter_congr
    intro w _
    constructor
    · exact fun h => halts_unique V (ver w) h
    · intro h
      exact h ▸ ver w
  have hinner : D x = true ↔ Odd (Finset.univ.filter fun u : U =>
      Odd (M.acc (y u))).card := by
    refine ((hR x hx₁).2).trans (Iff.of_eq (congrArg (fun s : Finset U => Odd s.card) ?_))
    apply Finset.filter_congr
    intro u _
    change AllAccept R letter ans j a b c x (List.ofFn u) ↔ Odd (M.acc (y u))
    exact ((spec u).2.symm.trans (Lin_padIn hx₁ List.length_ofFn)).symm
  change D x = true ↔ Odd (Finset.univ.filter fun w : Fin g → Bool =>
      HaltsWithin V (withGuess (List.ofFn w) x) true (t w)).card
  change (Finset.univ.filter fun w : Fin g → Bool => v w = true).card =
    ∑ u : U, M.acc (y u) at hcount
  rw [hselect, hcount]
  exact hinner.trans (odd_sum_filter (fun u : U => M.acc (y u))).symm

#print axioms P1C1U.caseB
