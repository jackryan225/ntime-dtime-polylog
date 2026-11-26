import P1ProgEng.KWShrinkResidents

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open P1P7
open C10
open scoped P1ChkFinal.AstraC10

noncomputable section

/-- The AB slice width, computed from the old bundle and this motif's rank in it. -/
def codedAB (a : ℕ) (p : RoleArgs × ArcRow) : ℕ :=
  let f := p.1
  let m := p.2
  let b := (rolesRow a f.1 f.2.1 f.2.2 m).1
  splitWidthNum (bundleWidthNum a f.1 f.2.1 b)
    (PackingData.pieceCount (oldDegree a) (colourBits a))
    (bundleRankNum a f (baseMotifRows a f.1 f.2.1) b m)

/-- The CD demand is the old motif wire. -/
def codedCD (a : ℕ) (p : RoleArgs × ArcRow) : ℕ :=
  oldWidth a p.1.1 p.1.2.1 p.2

def codedPayload (a : ℕ) (e : Bool × Fin 4) (p : RoleArgs × ArcRow) : ℕ :=
  read 0 (oldTerm a p.1.1 p.1.2.1 p.2) (termField e.1 e.2.val)

@[fun_prop] theorem codedAB_poly (a : ℕ) : Poly (codedAB a) := by
  unfold codedAB
  dsimp only
  fun_prop

@[fun_prop] theorem codedCD_poly (a : ℕ) : Poly (codedCD a) := by
  unfold codedCD
  fun_prop

@[fun_prop] theorem codedPayload_poly (a : ℕ) (e : Bool × Fin 4) :
    Poly (codedPayload a e) := by
  unfold codedPayload
  fun_prop

section Spec

variable {a g : ℕ} {k : Type} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

def codedSupply (a : ℕ) (e : Bool × Fin 4) (p : RoleArgs × ArcRow) : ℕ :=
  supplyWidthNum B (codedAB a p) (codedCD a p) (codedPayload a e p)

@[fun_prop] theorem codedSupply_poly (a : ℕ) (e : Bool × Fin 4) :
    Poly (codedSupply B a e) := by
  unfold codedSupply
  fun_prop

variable (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
variable {x : X.Base} {db : BallRows} (h : PayloadRows B X s x db)
variable (layout : Bool) (m : X.packingData.Motif)
variable (hb : (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2)

include h hb in
theorem codedAB_spec :
    codedAB a ((2 ^ g,db,layout), arcCode X m.val) =
      X.packingData.abWidth X.shrinkNumber X.packingWidth m := by
  obtain ⟨hs, ht⟩ := bundleEnds X h.toLocalRows m hb
  unfold codedAB
  dsimp only
  rw [rolesRow_spec h.toLocalRows.toGraphRows layout m hs ht]
  dsimp only
  rw [bundleWidthNum_spec B X s h _ hb, bundleRankNum_spec X h.toLocalRows layout m hb]
  exact splitWidthNum_spec _ _ (X.shrinkNumber (X.packingData.bundle m) ⟨m,rfl⟩)

include h hb in
theorem codedCD_spec :
    codedCD a ((2 ^ g,db,layout), arcCode X m.val) = X.packingWidth m.val :=
  h.oldWidth_eq _ (bundleEnds X h.toLocalRows m hb).1

include h hb in
theorem codedPayload_spec (e : Bool × Fin 4) :
    codedPayload a e ((2 ^ g,db,layout), arcCode X m.val) = (s m).val e :=
  h.selected_eq m e.1 e.2 (bundleEnds X h.toLocalRows m hb).1

include h hb in
theorem codedSupply_spec (e : Bool × Fin 4) :
    codedSupply B a e ((2 ^ g,db,layout), arcCode X m.val) = selW B X s m e := by
  unfold codedSupply
  rw [codedAB_spec B X s h layout m hb, codedCD_spec B X s h layout m hb,
    codedPayload_spec B X s h layout m hb, supplyWidthNum_spec B _ _ (s m).val e]

theorem bundle_near_of_role (r : PackedRole)
    (hx : (X.packingData.survivingRole layout r m).1 = x) :
    (baseGraph X).edist x (X.packingData.bundle m).1.1 ≤ 2 := by
  obtain ⟨hs,ht⟩ := role_ends X layout r m
  change (baseGraph X).edist x (X.packingData.C m).1.1 ≤ 2
  rcases C_base X m with he | he
  · exact he ▸ (hx ▸ hs)
  · exact he ▸ (hx ▸ ht)

/-- The strict supply-grid comparison forces at least one selector bit. -/
theorem shrink_selectorBits_pos : 0 < B.selectorBits := by
  classical
  let z : Bool → ℚ := fun _ => 0
  let d : Bool → ℝ := fun _ => 0
  let e : Bool × Fin 4 → ℝ := fun _ => 1
  have he : 0 < distanceEnergy (realWidths supplyMass) e := by
    unfold distanceEnergy
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    simpa only [e, one_pow, mul_one, realWidths, Rat.cast_pos] using supplyMass_pos i
  have hd : distanceEnergy (realWidths demandMass) d ≤
      (31 / 16) * distanceEnergy (realWidths supplyMass) e := by
    have hd0 : distanceEnergy (realWidths demandMass) d = 0 := by
      simp only [distanceEnergy, d, zero_pow (show (2 : ℕ) ≠ 0 by decide),
        mul_zero, Finset.sum_const_zero]
    rw [hd0]
    exact mul_nonneg (by norm_num) he.le
  obtain ⟨w, hw, hlt⟩ := B.grid.strict z B.grid.zero_mem_demands d e (fun _ => zero_le_one) he hd
  have hz : w ≠ (fun _ => 0) := by
    intro hzero
    rw [hzero] at hlt
    simp only [wireValue, realWidths, Rat.cast_zero, zero_mul, Finset.sum_const_zero] at hlt
    exact (lt_irrefl (0 : ℝ)) (by simpa only [d, mul_zero, Finset.sum_const_zero] using hlt)
  have hcard : 2 ≤ B.grid.supplies.card := by
    exact Finset.one_lt_card.mpr ⟨w, hw, _, B.grid.zero_mem_supplies, hz⟩
  have hpow : B.grid.supplies.card ≤ B.grid.supplies.card ^ B.power := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 0 < B.grid.supplies.card by omega) B.power_pos)
  have hcap := MotifWidths.selector_capacity B.copyCount B.grid.supplies.card B.power
  by_contra! h0
  have h0 : B.selectorBits = 0 := by omega
  change B.copyCount * B.grid.supplies.card ^ B.power ≤ 2 ^ B.selectorBits at hcap
  rw [h0, pow_zero] at hcap
  have hm := Nat.mul_le_mul_right (B.grid.supplies.card ^ B.power) (show 1 ≤ B.copyCount from B.copyCount_pos)
  simp only [one_mul] at hm
  omega

/-- Any incident word is a unary budget for all demand and payload tallies of
its motif. Admission supplies the payload bound and the tag supplies the clock. -/
theorem shrink_entry_width_bound :
    ∃ C : ℕ, ∀ (w : Bool → ℕ) (v : Bool × Fin 4 → ℕ),
      v ∈ outerIndices B w → ∀ e : Bool × Fin 4,
      (∀ d, w d ≤ C * (supplyWidths B w v e + 1)) ∧
      (∀ p, v p ≤ C * (supplyWidths B w v e + 1)) := by
  classical
  let D : ℕ := Finset.univ.sup fun p : B.grid.demands × Bool => baseDemand B p.1 p.2
  obtain ⟨A, hA⟩ := linear_index_bound B supplyMass_pos
  refine ⟨max D (A * (D + 1)), fun w v hv e => ?_⟩
  have hd (d : Bool) : w d ≤ repetitions B w * D :=
    (demand_le B demandMass_pos w d).trans (Nat.mul_le_mul_left _
      (Finset.le_sup (f := fun p : B.grid.demands × Bool => baseDemand B p.1 p.2)
        (Finset.mem_univ (demandGrid B demandMass_pos w, d))))
  have hu : repetitions B w ≤ supplyWidths B w v e := by
    unfold supplyWidths
    have hm := Nat.mul_le_mul_left (repetitions B w) (show 1 ≤ B.selectorBits from shrink_selectorBits_pos B)
    simp only [mul_one] at hm
    omega
  constructor
  · intro d
    refine (hd d).trans ?_
    rw [Nat.mul_comm (repetitions B w) D]
    exact Nat.mul_le_mul (le_max_left _ _) (Nat.le_succ_of_le hu)
  · intro p
    have hv' := (hA (repetitions B w * D) w hd).2 v hv p
    refine hv'.trans ?_
    calc
      A * (repetitions B w * D + 1) ≤ A * ((supplyWidths B w v e + 1) * (D + 1)) := by
        apply Nat.mul_le_mul_left
        have hmul := Nat.mul_le_mul_right D hu
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
        omega
      _ = A * (D + 1) * (supplyWidths B w v e + 1) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)

end Spec

end
end P1ProgEng.SolKWS
