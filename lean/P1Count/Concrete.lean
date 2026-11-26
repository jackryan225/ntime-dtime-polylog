import P1Count.Bookkeeping
import OAI.Computability.VPVNP.NetworkKernel

/-!
# P1Count.Concrete: the parity count in network form (task P9, target (3), lane P1-lean-W2-count)

The abstract count `P1Count.CountData.count_mod2` with its data taken from OpenAI's networks:

* `NetData`: for each skeleton candidate `σ` the branches `ι` of the compressor execution, the final
  network `Y σ ι`, the pushed factors `G σ ι` at its sites (P5: `chainPush (E.termChain ..) F1`), an order
  `ord σ ι` of the final sites (the address order of P6), the exponent `unowned σ` of the scalar (C14) and
  the number `acc σ` of accepting guesses with skeleton `σ`.
* `contract_siteFactor`: a factor `e u` that is `1` away from one site `s` comes out of the contraction.
  This is how the scalar `2 ^ uOwned` of `P1Net.rnFactors` (at `P1Net.scalarSite`) leaves the network.
* `NetData.hP`: from P4 in the form of `P1Net.ContractEqCount` (factors `e σ u * F1 σ u z`) and P5 in the
  form of `P1P5.contract_eq_push` (for the unscaled factors `F1`), the hypothesis `hP` of the count.
* `NetData.valid_mk_iff`: check C13 in site form. A tuple `(σ, ι, z, j)` is valid iff C14 holds
  (`unowned σ = 0`), the chain start `b.repr 1 (j 0) = 1`, one link per final site `v`:
  `mulEntry b (G σ ι v (z at v)) (j (ord v)) (j (ord v + 1)) = 1`, and the chain end `l (b (j P)) = 1`.
* `NetData.count_mod2`, `NetData.lang_iff`: the count in network form.
-/

namespace P1Count

open Module
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.WireTensor

noncomputable section

section Scale

variable {k : Type*} [CommSemiring k]

/-- A factor that is `1` away from the site `s` comes out of the contraction. -/
theorem contract_siteFactor (N : Network) (F : Factors k N) (e : N.Site → k) (s : N.Site)
    (he : ∀ u, u ≠ s → e u = 1) :
    contract N (fun u z => e u * F u z) = e s * contract N F := by
  unfold contract
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib,
    Finset.prod_eq_single s (fun u _ hu => he u hu) (fun h => absurd (Finset.mem_univ s) h)]
  ring

end Scale

/-- The network data of the parity count for one input. -/
structure NetData (F : Type*) where
  /-- Skeleton candidates `σ`. -/
  Sk : Type
  skFin : Fintype Sk
  /-- Branches `ι` of the compressor execution on `N_{x,σ}` (P5: `E.Choices`). -/
  Ch : Sk → Type
  chFin : ∀ σ, Fintype (Ch σ)
  /-- The final network of branch `ι` (P5: `(E.finalState ι).network`). -/
  Y : (σ : Sk) → Ch σ → Network
  /-- The pushed factors at the final sites (P5: `chainPush (E.termChain ..) F1`). -/
  G : (σ : Sk) → (ι : Ch σ) → Factors F (Y σ ι)
  /-- Number of final sites. -/
  P : (σ : Sk) → Ch σ → ℕ
  /-- The order of the final sites (address order, P6). -/
  ord : (σ : Sk) → (ι : Ch σ) → (Y σ ι).Site ≃ Fin (P σ ι)
  /-- Exponent of the scalar (`P1Net.uOwned`; check C14). -/
  unowned : Sk → ℕ
  /-- Accepting guesses with skeleton `σ`. -/
  acc : Sk → ℕ

attribute [instance] NetData.skFin NetData.chFin

namespace NetData

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (C : NetData F) {D : ℕ}

/-- The vertex tensor at final position `i`: the pushed factor at site `(ord σ ι).symm i`, read at the
restriction of the edge payloads `z` to that site. -/
def Wt (σ : C.Sk) (ι : C.Ch σ) (z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e)
    (i : Fin (C.P σ ι)) : F :=
  C.G σ ι ((C.ord σ ι).symm i)
    (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z ((C.ord σ ι).symm i))

open scoped Classical in
/-- The data of the abstract count. -/
abbrev toCountData : CountData F where
  Sk := C.Sk
  skFin := C.skFin
  Ch := C.Ch
  chFin := C.chFin
  Pay σ ι := (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e
  payFin _ _ := inferInstance
  P := C.P
  W := C.Wt
  unowned := C.unowned
  acc := C.acc

/-- The product over final positions is the product over final sites. -/
theorem prod_Wt (σ : C.Sk) (ι : C.Ch σ) (z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e) :
    ∏ i, C.Wt σ ι z i = ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v) :=
  Equiv.prod_comp (C.ord σ ι).symm
    (fun v => C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))

open scoped Classical in
/-- **`hP` from P4 and P5.** `Xn σ` is the network `N_{x,σ}`, `F1 σ` its unscaled factors, `e σ` the scalar
factor (`1` away from the site `s σ`, `2 ^ unowned σ` at `s σ`).
* `hP4` (P4, the form of `P1Net.ContractEqCount`): the contraction with the factors `e σ u * F1 σ u z` is
  `acc σ`;
* `hP5` (P5, the form of `P1P5.contract_eq_push`): the contraction with `F1 σ` is the sum over branches and
  final payloads of the product of the pushed factors. -/
theorem hP (Xn : C.Sk → Network) (F1 : ∀ σ, Factors F (Xn σ)) (s : ∀ σ, (Xn σ).Site)
    (e : ∀ σ, (Xn σ).Site → F) (he : ∀ σ u, u ≠ s σ → e σ u = 1)
    (hes : ∀ σ, e σ (s σ) = (2 : F) ^ C.unowned σ)
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v)) (σ : C.Sk) :
    (2 : F) ^ C.toCountData.unowned σ * ∑ ι, ∑ z, ∏ i, C.toCountData.W σ ι z i =
      (C.toCountData.acc σ : F) := by
  change (2 : F) ^ C.unowned σ * ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e, ∏ i, C.Wt σ ι z i = (C.acc σ : F)
  simp only [prod_Wt]
  rw [← hP5 σ, ← hes σ, ← contract_siteFactor _ _ _ (s σ) (he σ)]
  exact hP4 σ

/-- The vertex tensor at the position of site `v` is the pushed factor at `v`. -/
theorem Wt_ord (σ : C.Sk) (ι : C.Ch σ) (z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e)
    (v : (C.Y σ ι).Site) :
    C.Wt σ ι z (C.ord σ ι v) = C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v) := by
  unfold Wt
  rw [Equiv.symm_apply_apply]

/-- **Check C13 in site form, C14 and the chain ends.** -/
theorem valid_mk_iff (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (σ : C.Sk)
    (ι : C.Ch σ) (z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e) (j : Fin (C.P σ ι + 1) → Fin D) :
    C.toCountData.Valid b l ⟨σ, ι, z, j⟩ ↔
      C.unowned σ = 0 ∧ b.repr 1 (j 0) = 1 ∧
        (∀ v : (C.Y σ ι).Site,
          mulEntry b (C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
            (j (C.ord σ ι v).castSucc) (j (C.ord σ ι v).succ) = 1) ∧
        l (b (j (Fin.last (C.P σ ι)))) = 1 := by
  change C.unowned σ = 0 ∧ ChainOK b l (C.Wt σ ι z) j ↔ _
  unfold ChainOK
  have hlink : (∀ i : Fin (C.P σ ι), mulEntry b (C.Wt σ ι z i) (j i.castSucc) (j i.succ) = 1) ↔
      ∀ v : (C.Y σ ι).Site,
        mulEntry b (C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
          (j (C.ord σ ι v).castSucc) (j (C.ord σ ι v).succ) = 1 := by
    constructor
    · intro h v
      rw [← C.Wt_ord σ ι z v]
      exact h (C.ord σ ι v)
    · intro h i
      obtain ⟨v, rfl⟩ := (C.ord σ ι).surjective i
      rw [C.Wt_ord σ ι z v]
      exact h v
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr hlink Iff.rfl))

open scoped Classical in
/-- **P9 (3), `count_mod2`, network form.** -/
theorem count_mod2 (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (Xn : C.Sk → Network) (F1 : ∀ σ, Factors F (Xn σ)) (s : ∀ σ, (Xn σ).Site)
    (e : ∀ σ, (Xn σ).Site → F) (he : ∀ σ u, u ≠ s σ → e σ u = 1)
    (hes : ∀ σ, e σ (s σ) = (2 : F) ^ C.unowned σ)
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
    {U : Type*} [Fintype U] (Pass : U → Prop) [DecidablePred Pass] (enc : C.toCountData.Tup D → U)
    (hinj : Function.Injective enc)
    (hpass : ∀ u, Pass u ↔ ∃ t, C.toCountData.Valid b l t ∧ enc t = u) :
    ((Finset.univ.filter Pass).card : ZMod 2) = ((∑ σ, C.acc σ : ℕ) : ZMod 2) :=
  C.toCountData.count_mod2 b l hl (C.hP Xn F1 s e he hes hP4 hP5) Pass enc hinj hpass

open scoped Classical in
/-- **Language form.** If the language bit is the parity of the accepting guesses (P4 with
`P1Net.sum_card_skeleton` and `P1Int.parDecides_oai`), it is the parity of the passing witnesses. -/
theorem lang_iff (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
    (Xn : C.Sk → Network) (F1 : ∀ σ, Factors F (Xn σ)) (s : ∀ σ, (Xn σ).Site)
    (e : ∀ σ, (Xn σ).Site → F) (he : ∀ σ u, u ≠ s σ → e σ u = 1)
    (hes : ∀ σ, e σ (s σ) = (2 : F) ^ C.unowned σ)
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
    {U : Type*} [Fintype U] (Pass : U → Prop) [DecidablePred Pass] (enc : C.toCountData.Tup D → U)
    (hinj : Function.Injective enc)
    (hpass : ∀ u, Pass u ↔ ∃ t, C.toCountData.Valid b l t ∧ enc t = u)
    (Lx : Prop) (hL : Lx ↔ Odd (∑ σ, C.acc σ)) :
    Lx ↔ Odd (Finset.univ.filter Pass).card := by
  rw [hL, ← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    C.count_mod2 b l hl Xn F1 s e he hes hP4 hP5 Pass enc hinj hpass]

end NetData

end

end P1Count
