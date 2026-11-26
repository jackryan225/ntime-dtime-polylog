import P1SolFactor.SiteKeys

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open scoped BigOperators Classical

noncomputable section

/-- A list word read at the requested width, with zero bits beyond its actual length. -/
def wordAtWidth (width : ℕ) (word : List Bool) : List Bool :=
  List.ofFn fun j : Fin width => word.getD j.val false

theorem getD_ofFn {width : ℕ} (word : Fin width → Bool) (position : ℕ) :
    (List.ofFn word).getD position false = if hi : position < width then word ⟨position, hi⟩ else false := by
  split
  next hi =>
    have hlen : position < (List.ofFn word).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
  next hi =>
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]
    rfl

theorem wordAtWidth_ofFn {actual : ℕ} (width : ℕ) (word : Fin actual → Bool) :
    wordAtWidth width (List.ofFn word) = List.ofFn (asWord width word) := by
  unfold wordAtWidth
  congr 1
  funext j
  exact getD_ofFn word j.val

theorem wordAtWidth_zero (width : ℕ) : wordAtWidth width [] = List.replicate width false := by
  simp [wordAtWidth, List.ofFn_const]

section Half

variable {a h : ℕ} (X : State a h) (u : X.network.Site)

theorem slotWidth_le_total (dir : Bool) (s : Fin (2 ^ a)) :
    slotWidth X u dir s ≤ halfWidthSum X u := by
  have h : slotWidth X u dir s ≤ ∑ j, slotWidth X u dir j :=
    Finset.single_le_sum (f := slotWidth X u dir) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  exact h.trans (Finset.single_le_sum (f := fun d => ∑ j, slotWidth X u d j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ dir))

/-- The physical list at one slot, without padding. -/
def fieldBits (z : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) : List Bool :=
  List.ofFn (slotBits X u z dir j)

theorem fieldBits_length (z : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) :
    (fieldBits X u z dir j).length = slotWidth X u dir j := List.length_ofFn

theorem fieldBits_from_pack (z : X.network.Half u) (dir : Bool) (j : Fin (2 ^ a)) :
    fieldBits X u z dir j =
      List.ofFn fun k : Fin (slotWidth X u dir j) =>
        (packHalf X u z).getD (slotStart X u dir j + k.val) false := by
  unfold fieldBits
  congr 1
  funext k
  exact (packHalf_getD_slot X u z dir j k).symm

theorem wordAtWidth_out (z : X.network.Half u) (j : Fin (2 ^ a)) (width : ℕ) :
    wordAtWidth width (fieldBits X u z false j) = List.ofFn (outWord X u z j width) :=
  wordAtWidth_ofFn width _

theorem wordAtWidth_in (z : X.network.Half u) (j : Fin (2 ^ a)) (width : ℕ) :
    wordAtWidth width (fieldBits X u z true j) = List.ofFn (inWord X u z j width) :=
  wordAtWidth_ofFn width _

end Half

/-- The evaluator encoding lists the values at binary indices in order. -/
theorem encState_siteKeys {a h : ℕ} (X : State a h) (u : X.network.Site)
    {R : Type} [CommRing R] (F : NetworkKernel.Factors R X.network) :
    P1P5.encState (P1P5.stateOfO (siteKeys X u) F) =
      List.ofFn fun i : Fin (2 ^ halfWidthSum X u) =>
        Sum.inl (F u (halfOfIndex X u i)) := by
  simp only [P1P5.encState, P1P5.stateOfO, siteKeys, List.map_ofFn, Function.comp_def, halfOfIndex]

section RoutedSite

variable (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] {g : ℕ} (L : GuessLayout V g)
  (I : ℕ) [NeZero I] {h : ℕ} (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  {R : Type} [CommRing R] (bset : RouteSettings)

theorem factorRegsWith_widths (u : (rnState V B I σ ha).network.Site) (c : R) :
    let X := rnState V B I σ ha
    factorRegsWith V B L I σ ha bset u c 1 =
      (List.ofFn (slotWidth X u false)).flatMap P1P5.encPtr ++
      (List.ofFn (slotWidth X u true)).flatMap P1P5.encPtr := by
  obtain ⟨⟨⟨ι, loc⟩, twin⟩, lane⟩ := u
  cases twin <;> cases loc <;> simp [factorRegsWith, factor0Regs] <;> rfl

omit [CommRing R] in
private theorem widthsEncoding_length (widths : List ℕ) :
    (widths.flatMap (P1P5.encPtr (R := R))).length = widths.sum + widths.length := by
  induction widths with
  | nil => rfl
  | cons w widths ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [P1P5.encPtr, List.length_append, List.length_replicate, List.length_nil,
      List.sum_cons, List.length_cons]
    omega

theorem factorRegsWith_widths_length (u : (rnState V B I σ ha).network.Site) (c : R) :
    (factorRegsWith V B L I σ ha bset u c 1).length = halfWidthSum (rnState V B I σ ha) u + 2 * 2 ^ a := by
  rw [factorRegsWith_widths, List.length_append, widthsEncoding_length, widthsEncoding_length]
  simp only [List.length_ofFn, List.sum_ofFn, halfWidthSum, Fintype.sum_bool]
  omega

theorem factorStateWith_ofFn (u : (rnState V B I σ ha).network.Site) (c : R) :
    let X := rnState V B I σ ha
    factorStateWith V B L I σ ha bset u c =
      List.ofFn fun i : Fin (2 ^ halfWidthSum X u) =>
        Sum.inl (c * (if rnSiteOK V B L I σ ha bset u (halfOfIndex X u i) then 1 else 0)) :=
  encState_siteKeys ..

theorem factorStateWith_length (u : (rnState V B I σ ha).network.Site) (c : R) :
    (factorStateWith V B L I σ ha bset u c).length = 2 ^ halfWidthSum (rnState V B I σ ha) u := by
  rw [factorStateWith_ofFn, List.length_ofFn]

end RoutedSite

end

end P1SolFactor.SolHalf

#print axioms P1SolFactor.SolHalf.halfOfIndex_injective
#print axioms P1SolFactor.SolHalf.factorStateWith_ofFn
#print axioms P1SolFactor.SolHalf.factorRegsWith_widths_length
