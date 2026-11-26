import P1P7.SolKernlocSupply

namespace P1P7.SolKernloc

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.MotifDemandPadding
open OAI.Computability.VPVNP.NetworkKernel

attribute [local instance] instDecEqBaseT

private theorem sum_equiv_at {A A' R : Type*} [AddCommMonoid R] {i : Fintype A} {i' : Fintype A'}
    (e : A ≃ A') {f : A → R} {g : A' → R} (h : ∀ a, f a = g (e a)) :
    @Finset.sum A R _ (@Finset.univ A i) f = @Finset.sum A' R _ (@Finset.univ A' i') g := by
  letI := i
  letI := i'
  exact Fintype.sum_equiv e f g h

private theorem prod_equiv_at {A A' R : Type*} [CommMonoid R] {i : Fintype A} {i' : Fintype A'}
    (e : A ≃ A') {f : A → R} {g : A' → R} (h : ∀ a, f a = g (e a)) :
    @Finset.prod A R _ (@Finset.univ A i) f = @Finset.prod A' R _ (@Finset.univ A' i') g := by
  letI := i
  letI := i'
  exact Fintype.prod_equiv e f g h

section Kernel

variable {a b g : ℕ} {δ factor : ℝ} {K : Type*} [Field K]
variable (B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)

theorem entry_eq {w w' : Bool → ℕ} {u u' : Bool × Fin 4 → ℕ} (p : Fin 6)
    (hw : w = w') (hu : u = u')
    {d : HalfBits demandSource demandTarget w p} {d' : HalfBits demandSource demandTarget w' p}
    {y : HalfBits supply.src supply.dst (supplyWidths B w u) p}
    {y' : HalfBits supply.src supply.dst (supplyWidths B w' u') p}
    (hd : HEq d' d) (hy : HEq y' y) :
    evalEntry κ (entry B demandMass_pos w u p d y) =
      evalEntry κ (entry B demandMass_pos w' u' p d' y') := by
  subst w'
  subst u'
  cases hd
  cases hy
  rfl

variable {X X' : State a (packingLaneBits a g)} {x : X.Base}
variable (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
variable (hg : Good3 X X' x) (hg' : Good3 X' X (pb X X' x)) (hch : Ch3 B X X' s s' x)
variable (hLL : layoutBit B X s = layoutBit B X' s') (j : TagW a) (l : BitWord g)

local notation "v₀" => ((x, j), l)
local notation "v₁" => ((pb X X' x, j), l)
local notation "L₀" => layoutBit B X s
local notation "L₁" => layoutBit B X' s'
local notation "Y₀" => X.shrinkNext B ready s
local notation "Y₁" => X'.shrinkNext B ready s'
local notation "eP" => oldPlacedEquiv hg hg' hLL j l

open scoped Classical in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 600000 in
include hch in
theorem kernel_eq
    (pa : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half v₀)
    (z : (X.shrinkNext B ready s).network.Half ((x, j), l))
    (z' : (X'.shrinkNext B ready s').network.Half ((pb X X' x, j), l))
    (hzo : ∀ k : Fin (2 ^ b),
      HEq (z'.1 (outEdge Y₁ v₁ k) (outEdge_src Y₁ v₁ k)) (z.1 (outEdge Y₀ v₀ k) (outEdge_src Y₀ v₀ k)))
    (hzi : ∀ k : Fin (2 ^ b),
      HEq (z'.2 (inEdge Y₁ v₁ k) (inEdge_dst Y₁ v₁ k)) (z.2 (inEdge Y₀ v₀ k) (inEdge_dst Y₀ v₀ k))) :
    ((X'.shrinkStatePass B κ hκ ready).step.term s').kernel v₁ (eP pa) z' =
      ((X.shrinkStatePass B κ hκ ready).step.term s).kernel v₀ pa z := by
  have ho := pull_out B ready κ hκ (X := X) (X' := X') s s' (v := v₀) (v' := v₁)
    pa (eP pa) (oldPlaced_out hg hg' hLL j l pa)
  have hn := pull_in B ready κ hκ (X := X) (X' := X') hg j l s s'
    pa (eP pa) (oldPlaced_in hg hg' hLL j l pa)
  have h₀ := shrink_kernel_resident' B ready κ hκ X s v₀ pa z
  have h₁ := shrink_kernel_resident' B ready κ hκ X' s' v₁ (eP pa) z'
  refine h₁.trans (Eq.trans ?_ h₀.symm)
  symm
  refine sum_equiv_at (internalEquiv (B := B) (s := s) (s' := s') hg hg' hch hLL (j := j) (l := l)) ?_
  intro h
  refine prod_equiv_at (resEquiv hg hg' L₀ L₁ hLL j l) ?_
  rintro ⟨⟨m,p⟩, hp⟩
  have hx : (X.packingData.survivingRole L₀ (partyRole L₀ p) m).1 = x :=
    congrArg (fun v => v.1.1) hp
  have hE := resident_ends hg L₀ j l (m,p) hp
  have hp' : X'.packingData.shrinkPartySite L₁ (tM m hE) p = v₁ :=
    (resEquiv hg hg' L₀ L₁ hLL j l ⟨(m,p), hp⟩).2
  have data := role_data hg L₀ (partyRole L₀ p) m hx
  refine entry_eq B κ p (demandWidths_eq hg L₀ (partyRole L₀ p) m hx hE)
    (choiceVal_eq B hg s s' hch L₀ (partyRole L₀ p) m hx hE) ?_ ?_
  · exact demandArg_heq hE data.2.1 data.2.2.1 ho hn p hp.symm hp'.symm
  · exact supplyArg_heq hg m hE hLL hg' hch hzo hzi p h hp.symm hp'.symm

end Kernel

end P1P7.SolKernloc

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.NetworkKernel

section Kernel

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 600000 in
/-- P7, kernel locality of a shrinking substep (paper (a)(i), kernel part), radius 3. -/
theorem shrink_kernel_local (X X' : State a (packingLaneBits a g))
    (s : X.ShrinkSelection B) (s' : X'.ShrinkSelection B)
    (x : X.Base) (x' : X'.Base) (hx : addr X x = addr X' x')
    (hagree : ∀ y y', addr X y = addr X' y' → (baseGraph X).edist x y ≤ 3 →
      shrinkData B X s y = shrinkData B X' s' y')
    (hlayout : layoutBit B X s = layoutBit B X' s')
    (j : BitWord (packingTagBits (2 ^ a))) (l : BitWord g) :
    ∃ (eP : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half ((x, j), l) ≃
          Placed ((X'.shrinkStatePass B κ hκ ready).step.term s').place X'.network.Half ((x', j), l))
      (eO : (X.shrinkNext B ready s).network.Half ((x, j), l) ≃
          (X'.shrinkNext B ready s').network.Half ((x', j), l)),
      (∀ pa u (hu : ((x, j), l) = ((X.shrinkStatePass B κ hκ ready).step.term s).place u)
          (hu' : ((x', j), l) = ((X'.shrinkStatePass B κ hκ ready).step.term s').place (tPos X X' u))
          (kk : Fin (2 ^ a)),
        HEq ((eP pa (tPos X X' u) hu').1 (outEdge X' (tPos X X' u) kk) (outEdge_src X' (tPos X X' u) kk))
          ((pa u hu).1 (outEdge X u kk) (outEdge_src X u kk))) ∧
      (∀ pa u (hu : ((x, j), l) = ((X.shrinkStatePass B κ hκ ready).step.term s).place u)
          (hu' : ((x', j), l) = ((X'.shrinkStatePass B κ hκ ready).step.term s').place (tPos X X' u))
          (kk : Fin (2 ^ a)),
        HEq ((eP pa (tPos X X' u) hu').2 (inEdge X' (tPos X X' u) kk) (inEdge_dst X' (tPos X X' u) kk))
          ((pa u hu).2 (inEdge X u kk) (inEdge_dst X u kk))) ∧
      (∀ z (kk : Fin (2 ^ b)),
        HEq ((eO z).1 (outEdge (X'.shrinkNext B ready s') ((x', j), l) kk)
            (outEdge_src (X'.shrinkNext B ready s') ((x', j), l) kk))
          (z.1 (outEdge (X.shrinkNext B ready s) ((x, j), l) kk)
            (outEdge_src (X.shrinkNext B ready s) ((x, j), l) kk))) ∧
      (∀ z (kk : Fin (2 ^ b)),
        HEq ((eO z).2 (inEdge (X'.shrinkNext B ready s') ((x', j), l) kk)
            (inEdge_dst (X'.shrinkNext B ready s') ((x', j), l) kk))
          (z.2 (inEdge (X.shrinkNext B ready s) ((x, j), l) kk)
            (inEdge_dst (X.shrinkNext B ready s) ((x, j), l) kk))) ∧
      ∀ pa z, ((X'.shrinkStatePass B κ hκ ready).step.term s').kernel ((x', j), l) (eP pa) (eO z) =
        ((X.shrinkStatePass B κ hκ ready).step.term s).kernel ((x, j), l) pa z := by
  have hxx : pb X X' x = x' := pb_eq X X' hx
  subst x'
  have hs := agree_symm B X X' s s' x (pb X X' x) hx hagree
  have h := good_of_agree B X X' s s' x (pb X X' x) hx 2 (fun y y' hh hd => hagree y y' hh (by simpa using hd))
  have h' := good_of_agree B X' X s' s (pb X X' x) x hx.symm 2
    (fun y' y hh hd => hs y' y hh (by simpa using hd))
  have hg : Good3 X X' x := fun y hy => (h y (by simpa using hy)).1
  have hg' : Good3 X' X (pb X X' x) := fun y hy => (h' y (by simpa using hy)).1
  have hch : Ch3 B X X' s s' x := fun y hy => (h y (by simpa using hy)).2
  let eP := SolKernloc.oldPlacedEquiv hg hg' hlayout j l
  let Y := X.shrinkNext B ready s
  let Y' := X'.shrinkNext B ready s'
  let v : Y.network.Site := ((x, j), l)
  let v' : Y'.network.Site := ((pb X X' x, j), l)
  let hout := SolKernloc.outWidth_pair (ready := ready) hg s s' hch hlayout j l
  let hin := SolKernloc.inWidth_pair (ready := ready) hg s s' hch hlayout j l
  let eO := halfEquiv Y Y' v v' hout hin
  refine ⟨eP, eO, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun pa u hu hu' kk => SolKernloc.oldPlaced_out hg hg' hlayout j l pa u hu hu' kk
  · exact fun pa u hu hu' kk => SolKernloc.oldPlaced_in hg hg' hlayout j l pa u hu hu' kk
  · change ∀ z : Y.network.Half v, @SolKernloc.SlotOut b g g Y Y' v v' z (eO z)
    exact SolKernloc.halfEquiv_slotOut Y Y' v v' hout hin
  · change ∀ z : Y.network.Half v, @SolKernloc.SlotIn b g g Y Y' v v' z (eO z)
    exact SolKernloc.halfEquiv_slotIn Y Y' v v' hout hin
  · intro pa z
    exact SolKernloc.kernel_eq B ready κ hκ s s' hg hg' hch hlayout j l pa z (eO z)
      (SolKernloc.halfEquiv_slotOut Y Y' v v' hout hin z)
      (SolKernloc.halfEquiv_slotIn Y Y' v v' hout hin z)

end Kernel

#print axioms shrink_kernel_local

end P1P7
