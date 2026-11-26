import P1Count.Concrete
import P1P5.Main

/-!
# P1Count.LinkP5: the count data from the compressor execution (lane P1-lean-W2-count)

`NetData.ofExec`: the `NetData` of the parity count, built from OpenAI's execution
`E σ := B.execute κ hκ T hn (X σ)` of Theorem 7.1 on the network `X σ` of each skeleton candidate `σ`:
branches `ι : (E σ).Choices`, final networks `((E σ).finalState ι).network`, pushed factors
`P1P5.chainPush ((E σ).termChain (B.records κ hκ T hn (X σ)) ι) (F1 σ)` (P5), an order `ord` of the final
sites (P6 address order), `unowned` (P1Net.uOwned) and `acc` (run counts).

`NetData.ofExec_hP5`: the hypothesis `hP5` of `P1Count.NetData.count_mod2` is `P1P5.contract_eq_push`.
`NetData.ofExec_count_mod2`: the count for this data; only P4 (`hP4`, the routed `P1Net.ContractEqCount`
with the scalar split off), the basis, the witness encoding and the checks remain as hypotheses.
-/

namespace P1Count

open Module
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.WireTensor

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {F : Type*} [CommRing F] (κ : B.Entry → F) (hκ : B.IsSolution κ)

/-- The count data of the compressor execution on the networks `X σ`. -/
abbrev NetData.ofExec (Sk : Type) [Fintype Sk] {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n)
    (X : Sk → State (S.degreeExponent 0) n) (F1 : ∀ σ, Factors F (X σ).network)
    (ord : ∀ σ (ι : (B.execute κ hκ T hn (X σ)).Choices),
      ((B.execute κ hκ T hn (X σ)).finalState ι).network.Site ≃
        Fin (Fintype.card ((B.execute κ hκ T hn (X σ)).finalState ι).network.Site))
    (unowned acc : Sk → ℕ) : NetData F where
  Sk := Sk
  skFin := inferInstance
  Ch σ := (B.execute κ hκ T hn (X σ)).Choices
  chFin _ := inferInstance
  Y σ ι := ((B.execute κ hκ T hn (X σ)).finalState ι).network
  G σ ι := P1P5.chainPush ((B.execute κ hκ T hn (X σ)).termChain (B.records κ hκ T hn (X σ)) ι) (F1 σ)
  P σ ι := Fintype.card ((B.execute κ hκ T hn (X σ)).finalState ι).network.Site
  ord := ord
  unowned := unowned
  acc := acc

variable (Sk : Type) [Fintype Sk] {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n)
  (X : Sk → State (S.degreeExponent 0) n) (F1 : ∀ σ, Factors F (X σ).network)
  (ord : ∀ σ (ι : (B.execute κ hκ T hn (X σ)).Choices),
    ((B.execute κ hκ T hn (X σ)).finalState ι).network.Site ≃
      Fin (Fintype.card ((B.execute κ hκ T hn (X σ)).finalState ι).network.Site))
  (unowned acc : Sk → ℕ)

open scoped Classical in
/-- **`hP5` is P5.** -/
theorem NetData.ofExec_hP5 (σ : Sk) :
    contract (X σ).network (F1 σ) =
      ∑ ι : (NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).Ch σ,
        ∑ z : (e : ((NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).Y σ ι).Edge) →
            ((NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).Y σ ι).Payload e,
          ∏ v, (NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).G σ ι v
            (edgeAssignment ((NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).Y σ ι).src
              ((NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).Y σ ι).dst z v) :=
  P1P5.contract_eq_push B κ hκ T hn (X σ) (F1 σ)

open scoped Classical in
/-- **The count for the compressor execution.** `hP4`: P4 for the network `X σ` with the scalar factor
`e σ` split off (`P1Net.ContractEqCount`: `e σ u = if u = scalarSite then 2 ^ uOwned else 1`, `F1 σ` =
the `rnSiteOK` indicators). -/
theorem NetData.ofExec_count_mod2 [Algebra (ZMod 2) F] {D : ℕ} (b : Basis (Fin D) (ZMod 2) F)
    (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1) (s : ∀ σ, (X σ).network.Site)
    (e : ∀ σ, (X σ).network.Site → F) (he : ∀ σ u, u ≠ s σ → e σ u = 1)
    (hes : ∀ σ, e σ (s σ) = (2 : F) ^ unowned σ)
    (hP4 : ∀ σ, contract (X σ).network (fun u z => e σ u * F1 σ u z) = (acc σ : F))
    {U : Type*} [Fintype U] (Pass : U → Prop) [DecidablePred Pass]
    (enc : (NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).toCountData.Tup D → U)
    (hinj : Function.Injective enc)
    (hpass : ∀ u, Pass u ↔
      ∃ t, (NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).toCountData.Valid b l t ∧ enc t = u) :
    ((Finset.univ.filter Pass).card : ZMod 2) = ((∑ σ, acc σ : ℕ) : ZMod 2) :=
  (NetData.ofExec B κ hκ Sk T hn X F1 ord unowned acc).count_mod2 b l hl (fun σ => (X σ).network) F1
    s e he hes hP4 (NetData.ofExec_hP5 B κ hκ Sk T hn X F1 ord unowned acc) Pass enc hinj hpass

end

end P1Count
