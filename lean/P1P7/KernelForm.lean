import P1P7.Defs

/-!
# P7, shrinking substep: the RESIDENT FORM of a kernel (interface for P5 / P8b)

`shrink_kernel_resident`: every entry of the actual shrinking kernel of OpenAI's state pass
(`X.shrinkStatePass B κ hκ ready`, ShrinkStatePass.lean:91) at a new site `v` is

  Σ over the absorbed internal words `h` owned by `v` (`Placed (shrinkInternalOwner L) (internalLabel W L) v`)
  of the product over the RESIDENT maps `(m, j)` at `v` (`shrinkPartySite L m j = v`) of
  `shrinkMap m (s m) j (dArg) (sArg) = evalEntry κ (entry B demandMass_pos (shrinkDemandWidths m) (s m).val j dArg sArg)`,

with every datum named by an OpenAI definition:
* layout `L = layoutBit B X s` (P1P7.Defs; an integer comparison by `layoutBit_eq_int`);
* widths `wd = X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m` (AB width, CD width);
* payload vector `u = (s m).val` (the term choice of motif `m`);
* party `j : Fin 6`;
* demand argument `dArg = shrinkLocalDemandArg ... m j (pulled old half-wires placed at v)`;
* supply argument `sArg = shrinkLocalSupplyArg ... m j h z` (internal words and new half-wires at v);
* the internal owners `shrinkInternalOwner L` and the resident sites `shrinkPartySite L`.
`shrink_kernel_resident'` is the same with the product over the subtype of resident maps (OpenAI's
`partyProduct_eq_resident`). Both are equalities of definitions (no hypothesis).
-/

namespace P1P7

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.Compression.ShrinkEnergy
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.MotifConversion
open OAI.Computability.VPVNP.NetworkKernel

section Resident

/-- The same classical equality test on bases as ShrinkStatePass.lean:27 (exported: ONE instance for all kernel
files that import this one). -/
noncomputable instance instDecEqBaseK {a g : ℕ} (X : State a g) : DecidableEq X.Base :=
  Classical.decEq _

variable {a b g : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)

/-- The supply widths of the selected terms (the `width` argument of OpenAI's `shrinkLayout`). -/
noncomputable abbrev selW (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B) :
    X.packingData.Motif → Bool × Fin 4 → ℕ :=
  fun m ↦ X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B m (s m)

/-- The old half-wires placed at `v`, pulled back to the packed coordinates (as in `Term.reindex`). -/
noncomputable def pullPlaced (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (v : ((X.shrinkStatePass B κ hκ ready).step.term s).output.Site)
    (pa : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half v) :
    Placed (U := (X.packingData.oldWireNetwork X.packingWidth).Site)
      (X.packingData.shrinkPlace (layoutBit B X s))
      (X.packingData.oldWireNetwork X.packingWidth).Half v :=
  fun u hu ↦ X.packingInputIso.pullHalf u (pa (X.packingInputIso.site u) (by
    refine hu.trans ?_
    change _ = X.packingData.shrinkPlace (layoutBit B X s)
      (X.packingInputIso.site.symm (X.packingInputIso.site u))
    rw [Equiv.symm_apply_apply]))

open scoped Classical in
/-- **Resident form of the shrinking kernel** (partyProduct form, OpenAI's `shrinkLayout.entry` verbatim). -/
theorem shrink_kernel_resident (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (v : ((X.shrinkStatePass B κ hκ ready).step.term s).output.Site)
    (pa : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half v)
    (z : ((X.shrinkStatePass B κ hκ ready).step.term s).output.Half v) :
    ((X.shrinkStatePass B κ hκ ready).step.term s).kernel v pa z =
      ∑ h : Placed (X.packingData.shrinkInternalOwner (layoutBit B X s))
          (internalLabel (selW B X s) (layoutBit B X s)) v,
        partyProduct (X.packingData.shrinkPartySite (layoutBit B X s)) v fun m j hv ↦
          X.packingData.shrinkMap X.shrinkNumber X.packingWidth B κ m (s m) j
            (X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
              X.shrinkNumber X.shrinkOrder X.packingWidth (layoutBit B X s) m j
              (hv ▸ pullPlaced B ready κ hκ X s v pa))
            (X.packingData.shrinkLocalSupplyArg (layoutBit B X s)
              (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)) (selW B X s)
              (X.shrinkStateIndex ready (layoutBit B X s)) ready.count_pos m j (hv ▸ h) (hv ▸ z)) :=
  Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ ↦ rfl)

open scoped Classical in
/-- **Resident form, product over the resident maps** (OpenAI's `partyProduct_eq_resident`), with every factor
written as P5's `evalEntry κ (entry B demandMass_pos wd u j x y)`:
`wd = shrinkDemandWidths m`, `u = (s m).val`, `j` the party, `x` the local demand argument, `y` the local supply
argument. This is the input format of `P1P5.entry_eval`. -/
theorem shrink_kernel_resident' (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
    (v : ((X.shrinkStatePass B κ hκ ready).step.term s).output.Site)
    (pa : Placed ((X.shrinkStatePass B κ hκ ready).step.term s).place X.network.Half v)
    (z : ((X.shrinkStatePass B κ hκ ready).step.term s).output.Half v) :
    ((X.shrinkStatePass B κ hκ ready).step.term s).kernel v pa z =
      ∑ h : Placed (X.packingData.shrinkInternalOwner (layoutBit B X s))
          (internalLabel (selW B X s) (layoutBit B X s)) v,
        ∏ r : {p : X.packingData.Motif × Fin 6 // X.packingData.shrinkPartySite (layoutBit B X s) p.1 p.2 = v},
          evalEntry κ (entry B demandMass_pos
            (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth r.1.1) (s r.1.1).val r.1.2
            (X.packingData.shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
              X.shrinkNumber X.shrinkOrder X.packingWidth (layoutBit B X s) r.1.1 r.1.2
              (r.2.symm ▸ pullPlaced B ready κ hκ X s v pa))
            (X.packingData.shrinkLocalSupplyArg (layoutBit B X s)
              (subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)) (selW B X s)
              (X.shrinkStateIndex ready (layoutBit B X s)) ready.count_pos r.1.1 r.1.2
              (r.2.symm ▸ h) (r.2.symm ▸ z))) := by
  rw [shrink_kernel_resident]
  refine Finset.sum_congr rfl (fun h _ ↦ ?_)
  rw [partyProduct_eq_resident (k := R) (X.packingData.shrinkPartySite (layoutBit B X s)) v]
  exact Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ ↦ rfl)

end Resident

end P1P7
