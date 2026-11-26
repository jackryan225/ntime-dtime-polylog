import P1Net.ContractProofCount
import P1Net.Glue

/-! Decoding the physical table path, for every ordering of its external slots. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ}

def intervalEquiv (I h : ℕ) : Fin I × BitWord h ≃ Fin (I * 2 ^ h) :=
  ((Equiv.refl (Fin I)).prodCongr (laneEquiv h)).trans finProdFinEquiv

theorem intervalEquiv_val {I : ℕ} (ι : Fin I) (l : BitWord h) :
    ((intervalEquiv I h (ι, l) : Fin (I * 2 ^ h)) : ℕ) = (ι : ℕ) * 2 ^ h + (laneEquiv h l : ℕ) := by
  change ((finProdFinEquiv (ι, laneEquiv h l) : Fin (I * 2 ^ h)) : ℕ) = _
  rw [finProdFinEquiv_apply_val]
  ring

section Slot

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)

abbrev Labels := (e : (rnState V B I σ ha).network.Edge) → (rnState V B I σ ha).network.Payload e

noncomputable def slotIn (z : Labels V B I σ ha) (v : Fin I × Loc V.K h)
    (l : BitWord h) (s : Fin 4) (W : ℕ) : Fin W → Bool :=
  let X := rnState V B I σ ha
  inWord X ((v, false), l) (edgeAssignment X.network.src X.network.dst z ((v, false), l)) (s.castLE ha) W

noncomputable def slotOut (z : Labels V B I σ ha) (v : Fin I × Loc V.K h)
    (l : BitWord h) (s : Fin 4) (W : ℕ) : Fin W → Bool :=
  let X := rnState V B I σ ha
  outWord X ((v, false), l) (edgeAssignment X.network.src X.network.dst z ((v, false), l)) (s.castLE ha) W

theorem local_mate (ι : Fin I) {v v' : Loc V.K h} {s s' : Fin 4}
    (hm : locMate v s = some (v', s')) :
    netMate I σ ((ι, v), s) = some ((ι, v'), s') := by
  simp only [netMate, hm]

theorem slotIn_mate (z : Labels V B I σ ha) {v v' : Fin I × Loc V.K h} {s s' : Fin 4}
    (hm : netMate I σ (v, s) = some (v', s')) (l : BitWord h) (W : ℕ) :
    slotIn V B I σ ha z v l s W =
      slotOut V B I σ ha z v' (l + netDisp I σ (v, s)) s' W :=
  inWord_regularize_mate (preGraph I σ) ha _ z hm false l W

theorem slotIn_local (z : Labels V B I σ ha) (ι : Fin I) {v v' : Loc V.K h} {s s' : Fin 4}
    (hm : locMate v s = some (v', s')) (d : disp1 I ((ι, v), s) = 0)
    (d' : disp1 I ((ι, v'), s') = 0) (l : BitWord h) (W : ℕ) :
    slotIn V B I σ ha z (ι, v) l s W = slotOut V B I σ ha z (ι, v') l s' W := by
  have hn := local_mate V I σ ι hm
  have hd : netDisp I σ ((ι, v), s) = 0 := by simp only [netDisp, hn, d, d', add_zero]
  simpa only [hd, add_zero] using slotIn_mate V B I σ ha z hn l W

theorem tableCode_injective :
    Function.Injective (fun d : LocalIn V B => tupleWord V B (extData V B d (evolve d))) := by
  intro d e hcode
  have hf := tupleWord_injective V B hcode
  have hstate := encS_injective V B (congrFun hf Ext.stIn)
  apply LocalIn.ext
  · exact hstate.1
  · exact hstate.2
  · funext k δ
    exact encC_injective V B (congrFun hf (Ext.cIn k δ))

end Slot

section Tables

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m)
  (z : RoutedGood V B L I σ ha bset)

local notation "readIn" => slotIn V B I σ ha z.val
local notation "readOut" => slotOut V B I σ ha z.val

theorem path_factor (ι : Fin I) (l : BitWord h) (c : Ext V.K) :
    (netMate I σ ((ι, Loc.tabP c), 1) ≠ none →
      readOut (ι, .tabP c) l 1 (tupWidth V B) = readIn (ι, .tabP c) l 0 (tupWidth V B)) ∧
    (if Ext.isIn V c then
      readIn (ι, .tabP c) l 2 (strWidth V B) = segment V B c (readIn (ι, .tabP c) l 0 (tupWidth V B))
    else
      readOut (ι, .tabP c) l 2 (strWidth V B) = segment V B c (readIn (ι, .tabP c) l 0 (tupWidth V B))) :=
  z.property (((ι, .tabP c), false), l)

/-- Every path site's incoming tuple is the original center tuple. -/
theorem path_eq_center (ι : Fin I) (l : BitWord h) (c : Ext V.K) :
    readIn (ι, .tabP c) l 0 (tupWidth V B) = readOut (ι, .tabC) l 0 (tupWidth V B) := by
  suffices all : ∀ n (b : Ext V.K), (extIdx V.K b).val = n →
      readIn (ι, .tabP b) l 0 (tupWidth V B) = readOut (ι, .tabC) l 0 (tupWidth V B) from
    all _ c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hb
    cases hp : prevExt b with
    | none =>
      exact slotIn_local V B I σ ha z.val ι (v := .tabP b) (v' := .tabC) (s := 0) (s' := 0)
        (by simp only [locMate, ↓reduceIte, hp]) rfl rfl l _
    | some b' =>
      have hn := nextExt_eq_some.2 hp
      have hm : locMate (.tabP b' : Loc V.K h) 1 = some (.tabP b, 0) := by
        simp [locMate, hn]
      have linked : netMate I σ ((ι, Loc.tabP b'), 1) ≠ none := by
        rw [local_mate V I σ ι hm]
        exact Option.some_ne_none _
      have he : readIn (ι, .tabP b) l 0 (tupWidth V B) =
          readOut (ι, .tabP b') l 1 (tupWidth V B) :=
        slotIn_local V B I σ ha z.val ι (by simp only [locMate, ↓reduceIte, hp]) rfl rfl l _
      have hidx := nextExt_val hn
      exact he.trans (((path_factor V B L I σ ha bset z ι l b').1 linked).trans
        (ih (extIdx V.K b').val (by omega) b' rfl))

theorem center_witness (ι : Fin I) (l : BitWord h) :
    ∃ d : LocalIn V B,
      readOut (ι, .tabC) l 0 (tupWidth V B) = tupleWord V B (extData V B d (evolve d)) ∧
      (evolve d).move = σ (intervalEquiv I h (ι, l)) ∧
      ((intervalEquiv I h (ι, l) : ℕ) + 1 = I * 2 ^ h → Accepts B (evolve d)) := by
  let i : ℕ := (ι : ℕ) * 2 ^ h + (laneEquiv h l : ℕ)
  obtain ⟨d, hcode, hm, hlast⟩ :
      ∃ d : LocalIn V B,
        readOut (ι, .tabC) l 0 (tupWidth V B) = tupleWord V B (extData V B d (evolve d)) ∧
        (∀ hi : i < I * 2 ^ h, (evolve d).move = σ ⟨i, hi⟩) ∧
        (i + 1 = I * 2 ^ h → Accepts B (evolve d)) :=
    z.property (((ι, .tabC), false), l)
  have he : (intervalEquiv I h (ι, l) : ℕ) = i := intervalEquiv_val ι l
  have hi : i < I * 2 ^ h := he ▸ (intervalEquiv I h (ι, l)).isLt
  have hf : (⟨i, hi⟩ : Fin (I * 2 ^ h)) = intervalEquiv I h (ι, l) := Fin.ext he.symm
  exact ⟨d, hcode, hf ▸ hm hi, fun hh => hlast (he ▸ hh)⟩

noncomputable def centerData (ι : Fin I) (l : BitWord h) : LocalIn V B :=
  Classical.choose (center_witness V B L I σ ha bset z ι l)

theorem center_spec (ι : Fin I) (l : BitWord h) :
    let d := centerData V B L I σ ha bset z ι l
    readOut (ι, .tabC) l 0 (tupWidth V B) = tupleWord V B (extData V B d (evolve d)) ∧
    (evolve d).move = σ (intervalEquiv I h (ι, l)) ∧
    ((intervalEquiv I h (ι, l) : ℕ) + 1 = I * 2 ^ h → Accepts B (evolve d)) :=
  Classical.choose_spec (center_witness V B L I σ ha bset z ι l)

/-- The actual external word in slot 2 is the indicated string of the center data. -/
theorem external_eq (ι : Fin I) (l : BitWord h) (c : Ext V.K) :
    let d := centerData V B L I σ ha bset z ι l
    (if Ext.isIn V c then readIn (ι, .tabP c) l 2 (strWidth V B)
      else readOut (ι, .tabP c) l 2 (strWidth V B)) = extData V B d (evolve d) c := by
  have hp := (path_factor V B L I σ ha bset z ι l c).2
  rw [path_eq_center V B L I σ ha bset z ι l c, (center_spec V B L I σ ha bset z ι l).1,
    segment_tupleWord] at hp
  cases hc : Ext.isIn V c <;> simpa only [hc, Bool.false_eq_true, if_false, if_true] using hp

end Tables

end P1Net.AstraContract
