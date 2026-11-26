import P1Wit.SpaceFacts
import P1P5.ConeBudget
import P1SolCone.Tables

namespace P1SolCone.SolCone

open P1Int P1Wrap P1Wit.SolSpace
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open private runPhases runPhases_length from P1Wit.SpaceFacts

/-- The number of witness rows traversed by the cone is exactly the number charged in D14. -/
theorem genuine_top {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (K : Consts) (V : FiniteMultiTapeMachine) (aM t g d bigBias termBias : ℕ) :
    (genuineDims B K V aM t g d bigBias termBias).top = (S.steps + 1) * Params.T K t :=
  runPhases_length S (Params.T K t)

/-- Logarithmic clock length in terms of logarithmic input length, uniformly at small inputs. -/
theorem clock_log_le (a b n : ℕ) :
    Params.lam (lpTime a b n) + 1 ≤ (b + 2 * a + 4) * (Nat.log 2 (n + 1) + 1) := by
  let L := Nat.log 2 (n + 1) + 1
  let C := b + 2 * a + 1
  have hn : n + 1 ≤ 2 ^ L := (Nat.lt_pow_succ_log_self (by decide) _).le
  have hc : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have hb : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hn' : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hclock : lpTime a b n ≤ C * (n + 1) ^ 2 := by
    calc
      lpTime a b n = (b + 2 * a) * (n ^ 2 + 1) + (n + 1) := by unfold lpTime; ring
      _ ≤ (b + 2 * a) * (n + 1) ^ 2 + (n + 1) ^ 2 := by gcongr
      _ = C * (n + 1) ^ 2 := by unfold C; ring
  have hf : lpTime a b n ≤ 2 ^ (C + L * 2) := hclock.trans (by
    rw [pow_add, pow_mul]
    exact Nat.mul_le_mul hc (Nat.pow_le_pow_left hn _))
  have hl : Params.lam (lpTime a b n) ≤ C + L * 2 := Nat.clog_le_of_le_pow hf
  change _ ≤ (C + 3) * L
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have hCL : C + 1 ≤ (C + 1) * L := Nat.le_mul_of_pos_right _ hL
  rw [show (C + 3) * L = (C + 1) * L + L * 2 by ring]
  omega

/-- With a fixed predecessor cap, the number of distinct sites at any one frontier
is polynomial in the binary clock length. -/
theorem predecessor_growth_le (K : Consts) (steps t c : ℕ) :
    c ^ ((steps + 1) * Params.T K t) ≤ (Params.lam t + 1) ^ (c * (steps + 1)) := by
  have hp : 2 ^ Params.p t ≤ Params.lam t + 1 := by
    unfold Params.p
    by_cases h : Params.lam t = 0
    · simp [h]
    · exact (Nat.pow_log_le_self 2 h).trans (Nat.le_succ _)
  have hT : Params.T K t ≤ Params.p t := Nat.div_le_self _ _
  calc
    _ ≤ (2 ^ c) ^ ((steps + 1) * Params.T K t) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ ≤ (2 ^ c) ^ ((steps + 1) * Params.p t) :=
      Nat.pow_le_pow_right (Nat.one_le_two_pow) (Nat.mul_le_mul_left _ hT)
    _ = (2 ^ Params.p t) ^ (c * (steps + 1)) := by rw [← pow_mul, ← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_left hp _

private theorem flat_length_le {A B : Type*} (f : A → List B) (xs : List A) (c : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ c) : (xs.flatMap f).length ≤ xs.length * c := by
  induction xs with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons a xs ih =>
    have hh := Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul, Nat.add_comm] using hh

theorem needKeys_frontier_le (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (keys : List KeyCode) (c : ℕ) (h : ∀ k ∈ keys, (pre k.1).length ≤ c) :
    ((needKeys pre halves keys).map Prod.fst).dedup.length ≤ (keys.map Prod.fst).dedup.length * c := by
  let src := (keys.map Prod.fst).dedup
  let all := src.flatMap pre
  let dst := all.dedup
  let result := ((needKeys pre halves keys).map Prod.fst).dedup
  have hsub : result ⊆ dst := by
    intro s hs
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hs)
    change key ∈ dst.flatMap (fun p => (halves p).map (p, ·)) at hk
    obtain ⟨p, hp, hkey⟩ := List.mem_flatMap.mp hk
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hkey
    exact hp
  have h1 : result.length ≤ dst.length := by
    have subj : result.toFinset ⊆ dst.toFinset := fun _ hs =>
      List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hs))
    have hle := Finset.card_le_card subj
    have hnResult : result.Nodup := List.nodup_dedup _
    have hnDst : dst.Nodup := List.nodup_dedup _
    rwa [List.toFinset_card_of_nodup hnResult, List.toFinset_card_of_nodup hnDst] at hle
  exact (h1.trans (List.dedup_sublist all).length_le).trans (flat_length_le pre src c (fun s hs => by
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hs)
    exact h key hk))


private theorem list_sum_le_length_mul (ws : List ℕ) (cap : ℕ) (h : ∀ w ∈ ws, w ≤ cap) :
    ws.sum ≤ ws.length * cap := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hhead := h w List.mem_cons_self
    have htail := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem halfCodeCount_le (widths : List ℕ × List ℕ) (slots cap : ℕ)
    (hOut : widths.1.length ≤ slots) (hIn : widths.2.length ≤ slots)
    (hwOut : ∀ w ∈ widths.1, w ≤ cap) (hwIn : ∀ w ∈ widths.2, w ≤ cap) :
    (halfCodes widths).length ≤ 2 ^ (2 * slots * cap) := by
  rw [length_halfCodes]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have h₁ := (list_sum_le_length_mul widths.1 cap hwOut).trans (Nat.mul_le_mul_right _ hOut)
  have h₂ := (list_sum_le_length_mul widths.2 cap hwIn).trans (Nat.mul_le_mul_right _ hIn)
  calc
    _ ≤ slots * cap + slots * cap := Nat.add_le_add h₁ h₂
    _ = 2 * slots * cap := by ring

/-- All half assignments at a site are added in one group. Increasing the number of half
assignments at an existing site does not increase the number of predecessor searches. -/
theorem needKeys_count_le (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (keys : List KeyCode) (parents count : ℕ)
    (hpre : ∀ k ∈ keys, (pre k.1).length ≤ parents)
    (hhalf : ∀ k ∈ keys, ∀ p ∈ pre k.1, (halves p).length ≤ count) :
    (needKeys pre halves keys).length ≤ ((keys.map Prod.fst).dedup.length * parents) * count := by
  let sites := (keys.map Prod.fst).dedup
  let points := (sites.flatMap pre).dedup
  have hs : ∀ v ∈ sites, (pre v).length ≤ parents := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    exact hpre k hk
  have hp : points.length ≤ sites.length * parents :=
    (List.dedup_sublist _).length_le.trans (flat_length_le pre sites parents hs)
  have hz : ∀ p ∈ points, ((halves p).map (p, ·)).length ≤ count := by
    intro p hp
    obtain ⟨v, hv, hp'⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hp)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_dedup.mp hv)
    rw [List.length_map]
    exact hhalf k hk p hp'
  exact (flat_length_le _ points count hz).trans (Nat.mul_le_mul_right _ hp)

theorem placedCodeCount_le (halves : PositionCode → List HalfCode) (pre : List PositionCode)
    (parents count : ℕ) (hp : pre.length ≤ parents) (hcount : 1 ≤ count)
    (hh : ∀ v ∈ pre, (halves v).length ≤ count) :
    (placedCodes halves pre).length ≤ count ^ parents := by
  rw [length_placedCodes]
  apply le_trans _ (Nat.pow_le_pow_right hcount hp)
  induction pre with
  | nil => simp
  | cons v pre ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact Nat.mul_le_mul (hh v List.mem_cons_self)
      (ih (Nat.le_of_succ_le hp) (fun w hw => hh w (List.mem_cons_of_mem _ hw)))

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.genuine_top
#print axioms P1SolCone.SolCone.needKeys_frontier_le

#print axioms P1SolCone.SolCone.halfCodeCount_le
#print axioms P1SolCone.SolCone.needKeys_count_le
#print axioms P1SolCone.SolCone.placedCodeCount_le
