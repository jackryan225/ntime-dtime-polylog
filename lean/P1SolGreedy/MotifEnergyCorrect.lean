import P1SolGreedy.MotifTermCorrect

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.MotifBlocks OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

set_option synthInstance.maxSize 2048

section At

variable (D : Dims) (u : List Bool) (ℓ a g : ℕ) (len Y key : NumberWord)

local notation "ctx" => (activeMotif true D ℓ a g len Y key)
local notation "bases" => (savedMotifBases ctx u)
local notation "near" => (savedMotifNear bases u)
local notation "leaf" => (savedMotifFields true near u)

variable {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
variable (B : FixedBlock 𝕜 demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
local notation "storedDW" => (DWLocal (a := a) (g := g) (D := D))

set_option maxHeartbeats 750000 in
theorem wireEnergy_reads (w : WireWords) (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g))
    (hw : MatchesWire w (packingArcEquiv ℕ a g ((P1Batch.bval Y, k), v))) (hr : w ∈ arcRoots true ctx)
    (l : Bool) :
    P1Batch.bval (wireEnergy B.scale B.selectorBits l (leaf, w)) =
      if IsMotifAt a g D u ℓ (P1Batch.bval Y) k v then
        ∑ j, P1P7.layoutCoeff j * WS a g D u ℓ B storedDW (P1Batch.bval Y) k v l j ^ 2 else 0 := by
  let p := (leaf, w)
  let y := P1Batch.bval Y
  let stored := rawS D u ℓ y (keyOf a g k v)
  let copies := copiesWords B.scale (wordDemand p)
  let overhead := Carry.times0 (copies, bin B.selectorBits)
  let m := wordMotif p
  let f := numberEq (termValueWord (p, []), [true])
  have hm : m = true ↔ IsMotifAt a g D u ℓ y k v := wordMotif_iff true D u ℓ a g len Y key w y k v hw hr
  have hf : f = true ↔ stored.1 = 1 := by
    unfold f
    rw [numberEq_spec]
    change P1Batch.bval (termValueWord (p, [])) = 1 ↔ _
    rw [termFlag_reads true D u ℓ a g len Y key w y k v hw hr]
  have hc : P1Batch.bval overhead =
      MotifConversion.repetitions B (storedDW u ℓ y (keyOf a g k v)) * B.selectorBits := by
    unfold overhead
    rw [bval_mul, bval_bin]
    exact congrArg (fun n => n * B.selectorBits) (copiesWords_reads true D u ℓ a g len Y key B w y k v hw hr)
  change P1Batch.bval (bif bitAnd (m, f) then
    sumWords (Code.polyPush (energyTerm l) ((p, overhead), wordRange (tally 4))) else []) = _
  unfold bitAnd
  dsimp only
  by_cases hMotif : IsMotifAt a g D u ℓ y k v
  · rw [hm.mpr hMotif, Bool.true_and, ite_eq_left hMotif]
    by_cases hFlag : stored.1 = 1
    · rw [hf.mpr hFlag, Bool.cond_true, bval_sumPush, sumWordRange]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : selectRow ([] : NumberWord) (Carry.born j.val, layoutWeightTable) = bin (P1P7.layoutCoeff j) := by
        unfold layoutWeightTable
        rw [selectRow_table, bval_born, ite_eq_left j.isLt, finOr0_fin]
      change P1Batch.bval (weightedSquare (selectRow [] (Carry.born j.val, layoutWeightTable),
        Bits.add (termValueWord (p, termIndexWord (l, Carry.born j.val)), overhead))) = _
      rw [hs, weightedSquare_value, bval_bin, bval_add, hc,
        termField_reads true D u ℓ a g len Y key w y k v hw hr l j]
      have H : WS a g D u ℓ B storedDW y k v l j =
          stored.2 (l, j) + MotifConversion.repetitions B (storedDW u ℓ y (keyOf a g k v)) * B.selectorBits := by
        unfold WS
        rw [ite_eq_left hFlag]
        rfl
      rw [H]
    · rw [Bool.eq_false_iff.mpr (fun h => hFlag (hf.mp h)), Bool.cond_false]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have H : WS a g D u ℓ B storedDW y k v l j = 0 := by unfold WS; rw [ite_eq_right hFlag]
      rw [H, zero_pow (by decide : 2 ≠ 0), Nat.mul_zero]
  · rw [Bool.eq_false_iff.mpr (fun h => hMotif (hm.mp h)), Bool.false_and, Bool.cond_false, ite_eq_right hMotif]
    rfl

theorem rootEnergy_mem (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g)) :
    ((Y, Carry.born k.val, Carry.born (bwNum v)) : WireWords) ∈ arcRoots true ctx := by
  apply List.mem_map_of_mem
  exact List.mem_product.mpr ⟨born_mem_wordRange k.isLt, born_mem_wordRange (bitWordFinEquiv _ v).isLt⟩

theorem rootEnergy_code (k : Fin (2 ^ a)) (v : BitWord (packingLaneBits a g)) :
    MatchesWire (Y, Carry.born k.val, Carry.born (bwNum v)) (packingArcEquiv ℕ a g ((P1Batch.bval Y, k), v)) := by
  rw [matchesWire_parts]
  refine ⟨rfl, ?_, ?_⟩
  · exact bval_born _
  · rw [Equiv.symm_apply_apply]
    exact bval_born _

set_option maxHeartbeats 750000 in
theorem sumRootEnergy_reads (l : Bool) :
    P1Batch.bval (sumRootEnergy B.scale B.selectorBits l leaf) =
      energyS a g D u ℓ B storedDW (P1Batch.bval Y) l := by
  let f := fun p : NumberWord × NumberWord => P1Batch.bval (wireEnergy B.scale B.selectorBits l (leaf, Y, p))
  change P1Batch.bval (sumWords (Code.polyPush (wireEnergy B.scale B.selectorBits l)
    (leaf, ((wordRange (tally (2 ^ a))).product (wordRange (tally (2 ^ packingLaneBits a g)))).map (Prod.mk Y)))) = _
  rw [bval_sumPush, List.map_map, sumWordProduct, energyS, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  let c := bitWordFinEquiv (packingLaneBits a g)
  change (∑ j : Fin (2 ^ packingLaneBits a g), f (Carry.born k.val, Carry.born j.val)) = _
  rw [← c.sum_comp (fun j : Fin (2 ^ packingLaneBits a g) => f (Carry.born k.val, Carry.born j.val))]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact wireEnergy_reads D u ℓ a g len Y key B _ k v (rootEnergy_code a g Y k v)
    (rootEnergy_mem D ℓ a g len Y key k v) l

theorem energyWord_reads (Z : NumberWord) (hZ : Z = Y ∨ Z = prevAddress Y) (l : Bool) :
    P1Batch.bval (energyWord l (leaf, Z)) = rdEnergy D u ℓ (P1Batch.bval Z) (eCode l) := by
  let r := energyRequest (levelRow D ℓ, Z, energyIndex l)
  have hm : r ∈ motThirdRaw true near := by
    change r ∈ leafColours near ++ leafWires true near ++ leafEnergies ctx
    apply List.mem_append_right
    change r ∈ [energyRequest (levelRow D ℓ, Y, []), energyRequest (levelRow D ℓ, Y, [true]),
      energyRequest (levelRow D ℓ, prevAddress Y, []), energyRequest (levelRow D ℓ, prevAddress Y, [true])]
    rcases hZ with rfl | rfl <;> cases l
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h := energyRequest_value D ℓ Z (energyIndex l)
  have hc : P1Batch.bval (energyIndex l) = eCode l := by cases l <;> rfl
  rw [hc] at h
  exact cacheRead_field' D u _ _ _ r ⟨_, hm, rfl⟩ h

theorem groupRecurrence_iff (l : Bool) :
    groupRecurrence B.scale B.selectorBits l leaf = true ↔
      rdEnergy D u ℓ (P1Batch.bval Y) (eCode l) =
        (if 0 < P1Batch.bval Y then rdEnergy D u ℓ (P1Batch.bval Y - 1) (eCode l) else 0) +
        energyS a g D u ℓ B storedDW (P1Batch.bval Y) l := by
  let v := energyWord l (leaf, Y)
  let p := energyWord l (leaf, prevAddress Y)
  change numberEq (v, Bits.add ((bif numberEq (Y, []) then [] else p),
    sumRootEnergy B.scale B.selectorBits l leaf)) = true ↔ _
  rw [numberEq_spec]
  change P1Batch.bval v = P1Batch.bval (Bits.add ((bif numberEq (Y, []) then [] else p),
    sumRootEnergy B.scale B.selectorBits l leaf)) ↔ _
  rw [bval_add, sumRootEnergy_reads D u ℓ a g len Y key B l]
  have hv : P1Batch.bval v = _ := energyWord_reads D u ℓ a g len Y key Y (Or.inl rfl) l
  have hp : P1Batch.bval p = rdEnergy D u ℓ (P1Batch.bval Y - 1) (eCode l) := by
    unfold p
    rw [energyWord_reads D u ℓ a g len Y key _ (Or.inr rfl), prevAddress_value]
  rw [hv]
  by_cases hY : P1Batch.bval Y = 0
  · rw [(numberEq_spec (Y, [])).mpr hY, Bool.cond_true, hY, ite_eq_right (Nat.lt_irrefl 0)]
    rfl
  · rw [Bool.eq_false_iff.mpr (fun hh => hY ((numberEq_spec (Y, [])).mp hh)), Bool.cond_false, hp,
      ite_eq_left (Nat.pos_of_ne_zero hY)]

theorem bothBool_iff (P : Bool → Prop) : P false ∧ P true ↔ ∀ l, P l := by
  constructor
  · rintro ⟨hb₀, hb₁⟩ l
    cases l
    · exact hb₀
    · exact hb₁
  · intro h
    exact ⟨h false, h true⟩

theorem decideEnergy_guard (L selector : ℕ) (s : MotifFields) (h : (fieldContext s).1.2.1 = true) :
    decideEnergyWords L selector s = bitAnd (groupRecurrence L selector false s, groupRecurrence L selector true s) := by
  rw [decideEnergyWords, h, Bool.cond_true]

set_option maxHeartbeats 900000 in
theorem decideEnergyWords_correct :
    decideEnergyWords B.scale B.selectorBits leaf = true ↔
      C8chk a g D u ℓ B storedDW (P1Batch.bval Y) := by
  let f := leaf
  let y := P1Batch.bval Y
  let G (l : Bool) := rdEnergy D u ℓ y (eCode l) =
    (if 0 < y then rdEnergy D u ℓ (y - 1) (eCode l) else 0) + energyS a g D u ℓ B storedDW y l
  change decideEnergyWords B.scale B.selectorBits f = true ↔ ∀ l, G l
  have hg : (fieldContext f).1.2.1 = true := rfl
  rw [decideEnergy_guard _ _ f hg, bitAnd, Bool.and_eq_true]
  have h₀ : groupRecurrence B.scale B.selectorBits false f = true ↔ G false :=
    groupRecurrence_iff D u ℓ a g len Y key B false
  have h₁ : groupRecurrence B.scale B.selectorBits true f = true ↔ G true :=
    groupRecurrence_iff D u ℓ a g len Y key B true
  calc
    (groupRecurrence B.scale B.selectorBits false f = true ∧
        groupRecurrence B.scale B.selectorBits true f = true) ↔ G false ∧ G true :=
      and_congr h₀ h₁
    _ ↔ ∀ l, G l := bothBool_iff G

end At

end P1SolGreedy.SolDemand
