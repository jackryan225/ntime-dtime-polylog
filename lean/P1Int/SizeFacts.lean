import P1Int.SizeFactsDefs
import P1Int.WitnessFit

noncomputable section

open Filter P1Wrap.Params
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.sizeFacts {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)

    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) :
    P1Int.P11.SizeFactsTarget Bt V a b d bigBias termBias := by
  intro _
  -- Once p reaches 1, the lane exponent h is positive and supplies two lanes.
  have hpTime : Tendsto (fun n => p (P1Int.lpTime a b n)) atTop atTop :=
    tendsto_p.comp (P1Int.P11.tendsto_lpTime a b)
  obtain ⟨n₀, hn₀⟩ := tendsto_atTop_atTop.mp hpTime 1
  refine ⟨n₀, fun x hx => ?_⟩
  let t := P1Int.lpTime a b x.length
  let g := a * (x.length ^ 2 + 1)
  change I 1 t ≠ 0 ∧ I 1 t * N t ≠ 0 ∧ B t ≠ 0 ∧ 2 ≤ B t * N t ∧
    P1Wit.SolSpace.guessBlocks g (bb t) = P1ChkDir.nGuessBlocks g (B t * N t) ∧ N t = 2 ^ h t
  have hI := (P1Int.P11.neZero_I 1 t le_rfl).out
  refine ⟨hI, mul_ne_zero hI (Nat.two_pow_pos _).ne', (B_pos t).ne', ?_, rfl, rfl⟩
  have hp : 1 ≤ p t := hn₀ x.length hx
  have hh : 1 ≤ h t := by
    unfold h
    omega
  calc
    2 = (2 : ℕ) ^ 1 := rfl
    _ ≤ N t := Nat.pow_le_pow_right (by decide) hh
    _ ≤ B t * N t := Nat.le_mul_of_pos_left _ (B_pos t)

example : ∀ {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)

    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ),
    P1Int.P11.SizeFactsTarget Bt V a b d bigBias termBias := @P1Int.P11.sizeFacts

#print axioms P1Int.P11.sizeFacts

end
