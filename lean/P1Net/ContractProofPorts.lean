import P1Net.ContractProofContent

/-! The first physical port of each owned block supplies its initial contents. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor
open scoped Classical

variable {h : ℕ} {K : Type} [Fintype K] [DecidableEq K]

section Coordinates

variable (I : ℕ) (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

theorem portType_slot {Z : ℤ} (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portType I σ ι k Z = (portSlot I σ k ι (Z / 2 ^ h) : ℕ) := by
  have hs := portQ_portSlot I σ ho
  unfold portQ at hs
  unfold portType
  omega

theorem input_link {Q : ℤ} (ho : Owns I σ k ι Q) :
    netMate I σ ((ι, Loc.portIn k (portSlot I σ k ι Q)), 1) =
      (prevOwner I σ k ι Q).map (fun j : Fin I => ((j, Loc.portOut k (portSlot I σ k j Q)), 1)) := by
  cases hp : prevOwner I σ k ι Q <;>
    simp [netMate, locMate, interMate, portQ_portSlot I σ ho, hp]

private theorem ownerSet_nonempty {Q : ℤ} (ex : ∃ j : Fin I, Owns I σ k j Q) :
    (Finset.univ.filter fun j : Fin I => Owns I σ k j Q).Nonempty := by
  obtain ⟨j, hj⟩ := ex
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩

noncomputable def firstOwner (Q : ℤ) (ex : ∃ j : Fin I, Owns I σ k j Q) : Fin I :=
  (Finset.univ.filter fun j : Fin I => Owns I σ k j Q).min' (ownerSet_nonempty I σ k ex)

theorem firstOwner_spec {Q : ℤ} (ex : ∃ j : Fin I, Owns I σ k j Q) :
    Owns I σ k (firstOwner I σ k Q ex) Q ∧
    ∀ j : Fin I, Owns I σ k j Q → firstOwner I σ k Q ex ≤ j := by
  unfold firstOwner
  exact ⟨(Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun j : Fin I => Owns I σ k j Q)
      (ownerSet_nonempty I σ k ex))).2,
    fun j hj => Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩

theorem firstOwner_prev {Q : ℤ} (ex : ∃ j : Fin I, Owns I σ k j Q) :
    prevOwner I σ k (firstOwner I σ k Q ex) Q = none := by
  cases hp : prevOwner I σ k (firstOwner I σ k Q ex) Q with
  | none => rfl
  | some j =>
    obtain ⟨hlt, ho, _⟩ := prevOwner_spec hp
    exact False.elim (not_lt_of_ge ((firstOwner_spec I σ k ex).2 j ho) hlt)

theorem firstOwner_eq {Q : ℤ} (ho : Owns I σ k ι Q) (hp : prevOwner I σ k ι Q = none)
    (ex : ∃ j : Fin I, Owns I σ k j Q) : firstOwner I σ k Q ex = ι := by
  obtain ⟨hf, hle⟩ := firstOwner_spec I σ k ex
  apply le_antisymm (hle ι ho)
  exact le_of_not_gt (fun hlt => no_owner_before_of_none I σ ι k hp _ hlt hf)

end Coordinates

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)

noncomputable def portInput (z : Labels V B I σ ha) (ι : Fin I) (k : V.K) (Z : ℤ) :
    Fin (strWidth V B) → Bool :=
  contentInput V B I σ ha z ι k (typ (portType I σ ι k Z), portLane h Z)

noncomputable def portOutput (z : Labels V B I σ ha) (ι : Fin I) (k : V.K) (Z : ℤ) :
    Fin (strWidth V B) → Bool :=
  contentOutput V B I σ ha z ι k (typ (portType I σ ι k Z), portLane h Z)

noncomputable def seedWord (z : Labels V B I σ ha) (k : V.K) (Z : ℤ) : Fin (strWidth V B) → Bool :=
  if ex : ∃ j : Fin I, Owns I σ k j (Z / 2 ^ h) then
    portInput V B I σ ha z (firstOwner I σ k (Z / 2 ^ h) ex) k Z
  else fun _ => false

variable (z : RoutedGood V B L I σ ha bset) (ι : Fin I) (k : V.K) (Z : ℤ)

theorem portInput_word (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portInput V B I σ ha z.val ι k Z =
      slotOut V B I σ ha z.val (ι, .portIn k (portSlot I σ k ι (Z / 2 ^ h)))
        ((laneEquiv h).symm (portLane h Z)) 0 (strWidth V B) := by
  rw [portInput, portType_slot I σ ι k ho]
  exact input_from_port V B L I σ ha bset z ι k _ _

theorem portOutput_word (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portOutput V B I σ ha z.val ι k Z =
      slotIn V B I σ ha z.val (ι, .portOut k (portSlot I σ k ι (Z / 2 ^ h)))
        ((laneEquiv h).symm (portLane h Z)) 0 (strWidth V B) := by
  rw [portOutput, portType_slot I σ ι k ho]
  exact output_to_port V B L I σ ha bset z ι k _ _

theorem first_pin (ho : Owns I σ k ι (Z / 2 ^ h)) (hp : prevOwner I σ k ι (Z / 2 ^ h) = none) :
    ∃ p : Fin B → V.Γ, PinOK B L k Z p ∧ portInput V B I σ ha z.val ι k Z = encC V B p := by
  let δ := portSlot I σ k ι (Z / 2 ^ h)
  let l := (laneEquiv h).symm (portLane h Z)
  have hm : netMate I σ ((ι, Loc.portIn k δ), 1) = none := by
    rw [input_link I σ ι k ho, hp] <;> rfl
  have hf := z.property (((ι, Loc.portIn k δ), false), l)
  change (if netMate I σ ((ι, Loc.portIn k δ), 1) = none then _ else _) at hf
  rw [if_pos hm] at hf
  obtain ⟨p, hpin, hcode⟩ := hf
  obtain ⟨hl, hr⟩ := bounds_of_owns I σ ι k ho
  have he : portBlock I σ ι k δ (laneEquiv h l) = Z := by
    change portBlock I σ ι k (portSlot I σ k ι (Z / 2 ^ h))
      (laneEquiv h ((laneEquiv h).symm (portLane h Z))) = Z
    rw [Equiv.apply_symm_apply, ← portType_slot I σ ι k ho]
    exact (portBlock_of_owned I σ ι k hl hr).2
  rw [portInput_word V B L I σ ha bset z ι k Z ho]
  exact ⟨p, he ▸ hpin, hcode⟩

theorem seed_pin (ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h)) :
    ∃ p : Fin B → V.Γ, PinOK B L k Z p ∧ seedWord V B I σ ha z.val k Z = encC V B p := by
  rw [seedWord, dif_pos ex]
  exact first_pin V B L I σ ha bset z _ k Z (firstOwner_spec I σ k ex).1 (firstOwner_prev I σ k ex)

theorem copy_from_owner {j : Fin I} (ho : Owns I σ k ι (Z / 2 ^ h))
    (hp : prevOwner I σ k ι (Z / 2 ^ h) = some j) :
    portInput V B I σ ha z.val ι k Z = portOutput V B I σ ha z.val j k Z := by
  let v : Fin I × Loc V.K h := (ι, .portIn k (portSlot I σ k ι (Z / 2 ^ h)))
  let v' : Fin I × Loc V.K h := (j, .portOut k (portSlot I σ k j (Z / 2 ^ h)))
  let l := (laneEquiv h).symm (portLane h Z)
  have hm : netMate I σ (v, 1) = some (v', 1) := by
    rw [input_link I σ ι k ho, hp] <;> rfl
  have hn : netMate I σ (v, 1) ≠ none := by rw [hm]; exact Option.some_ne_none _
  have hn' : netMate I σ (v', 1) ≠ none := by
    rw [netMate_symm I σ hm]
    exact Option.some_ne_none _
  have hd : netDisp I σ (v, 1) = 0 := by simp only [netDisp, hm, v, v', disp1, add_zero]
  have hpin := z.property ((v, false), l)
  change (if netMate I σ (v, 1) = none then _ else _) at hpin
  rw [if_neg hn] at hpin
  have hpout : netMate I σ (v', 1) ≠ none →
      slotOut V B I σ ha z.val v' l 1 (strWidth V B) = slotIn V B I σ ha z.val v' l 0 (strWidth V B) :=
    z.property ((v', false), l)
  rw [portInput_word V B L I σ ha bset z ι k Z ho,
    portOutput_word V B L I σ ha bset z j k Z (prevOwner_spec hp).2.1]
  change slotOut V B I σ ha z.val v l 0 _ = slotIn V B I σ ha z.val v' l 0 _
  have wire := slotIn_mate V B I σ ha z.val hm l (strWidth V B)
  rw [hd, add_zero] at wire
  exact Eq.trans hpin (wire.trans (hpout hn'))

/-- The owner input equation extracted from the original sites, with its first pin identified. -/
theorem physical_owner_in (ho : Owns I σ k ι (Z / 2 ^ h)) :
    portInput V B I σ ha z.val ι k Z =
      match prevOwner I σ k ι (Z / 2 ^ h) with
      | none => seedWord V B I σ ha z.val k Z
      | some j => portOutput V B I σ ha z.val j k Z := by
  cases hp : prevOwner I σ k ι (Z / 2 ^ h) with
  | none =>
    have ex : ∃ i : Fin I, Owns I σ k i (Z / 2 ^ h) := ⟨ι, ho⟩
    rw [seedWord, dif_pos ex, firstOwner_eq I σ ι k ho hp ex]
  | some j => exact copy_from_owner V B L I σ ha bset z ι k Z ho hp

end P1Net.AstraContract
