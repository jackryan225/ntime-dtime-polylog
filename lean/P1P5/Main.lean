import P1P5.Cover

/-!
# P1, task P5: the two target theorems (interface for P8 and P9)

`contract_eq_push` (P5 a): push form of the exact identity of OpenAI's Theorem 7.1.
`pushed_factor_bounds` (P5 b): faithfulness of the pushed factors: each one is an explicit finite
enumeration over the old half-wire assignments of its placement tree (actual `Term.place` and
`Term.kernel` of the selected terms), with at most `C₂^T` sites, wires of at most `C₂^T (W₀+1)` bits,
and at most `C₂^T · C₂^T (W₀+1)` enumeration bits.

`S`, `B` are arbitrary here; Case 2 takes them from `Compression.exists_iterated_compression`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.WireTensor

open scoped Classical

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)

/-- **P5 (a), push form.** For the execution `E := B.execute κ hκ T hn X` of Theorem 7.1 and all
original vertex factors `F`: the contraction is the sum over the branches `ι` (sequences of selected
terms), and over one payload `z` per final wire, of the product over the final sites `v` of the pushed
factor `W_v = chainPush (E.termChain (B.records κ hκ T hn X) ι) F v` read at the restriction of `z`
to the wires at `v`. -/
theorem contract_eq_push {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (F : Factors R X.network) :
    let E := B.execute κ hκ T hn X
    contract X.network F =
      ∑ ι : E.Choices,
        ∑ z : (e : (E.finalState ι).network.Edge) → (E.finalState ι).network.Payload e,
          ∏ v, chainPush (E.termChain (B.records κ hκ T hn X) ι) F v
            (edgeAssignment (E.finalState ι).network.src (E.finalState ι).network.dst z v) := by
  intro E
  rw [contract_eq_sum_chainPush E (B.records κ hκ T hn X) F]
  apply Finset.sum_congr rfl
  intro ι _
  exact contract_edgeSum _ _

/-- The wires of a state network carry exactly `totalWidth` bits: the payload assignments `z` of
`contract_eq_push` on a final network number `2 ^ Y.totalWidth` (OpenAI's `branch_bounds` bounds
`Y.totalWidth ≤ sqrt Y.energy ≤ (sqrt X.energy + B.widthAllowance * X.positions) / 2^T`). -/
theorem card_final_payloads {a g : ℕ} (Y : State a g) :
    Fintype.card ((e : Y.network.Edge) → Y.network.Payload e) = 2 ^ Y.totalWidth := by
  rw [Fintype.card_pi]
  simp only [card_payload]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Equiv.sum_comp
    ({ toFun := fun e => ((e.1.1, e.2), e.1.2), invFun := fun e => ((e.1.1, e.2), e.1.2),
       left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      Y.network.Edge ≃ (Y.Base × Fin (2 ^ a)) × BitWord g) Y.width

/-- **P5 (b), faithfulness.** Along every branch `ι` of `E := B.execute κ hκ T hn X`, with the
selected chain `chain := E.termChain (B.records κ hκ T hn X) ι` (the chain whose records Theorem 7.1
bounds), `C := B.growthConstant` and `M := C ^ T * (X.maxWireWidth + 1)` (the paper's `C₂^T (W₀+1)`):
1. each pushed factor `W_v = chainPush chain F v` is the finite sum over its enumeration domain
   `chainDom chain (fun _ => Unit) v` of `chainSummand`: the product of the original factors at the
   level-0 sites and of the actual kernels at the later sites of the placement tree of `v`;
2. that placement tree has at most `C ^ T` sites (all levels), so each summand has at most `C ^ T`
   local factors;
3. every wire of every network of the branch carries at most `M` bits;
4. the enumeration domain of `W_v` has at most `2 ^ (C ^ T * M)` elements (`C₂^T · C₂^T (W₀+1)` bits). -/
theorem pushed_factor_bounds {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (ι : (B.execute κ hκ T hn X).Choices) :
    let chain := (B.execute κ hκ T hn X).termChain (B.records κ hκ T hn X) ι
    let C := B.growthConstant
    let M := C ^ T * (X.maxWireWidth + 1)
    (∀ (F : Factors R X.network) v z,
        chainPush chain F v z =
          ∑ d : chainDom chain (fun _ => Unit) v,
            chainSummand chain (fun _ => Unit) (fun u _ x => F u x) v d z) ∧
      (∀ v, chainAncestors chain (fun _ => 1) v ≤ C ^ T) ∧
      ChainPayloadLe chain M ∧
      (∀ v, Fintype.card (chainDom chain (fun _ => Unit) v) ≤ 2 ^ (C ^ T * M)) := by
  intro chain C M
  obtain ⟨-, -, -, hocc, hrec, -⟩ := B.branch_bounds κ hκ T hn X ι
  have hb : (B.execute κ hκ T hn X).Bounded B.recordLimit (B.records κ hκ T hn X) :=
    (Procedure.repeat_recordBounds (B.recordBounds κ hκ) (n - T * S.laneBits) T n
      (Nat.add_sub_of_le hn).symm X).1
  have hcov : ChainHalfCovered chain :=
    termChain_halfCovered _ _ (execute_halfCovered B κ hκ T hn X) ι
  have hCT : 0 < C ^ T := pow_pos (lt_of_lt_of_le (by norm_num) B.growthConstant_ge_two) T
  have hXM : X.maxWireWidth ≤ M :=
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hCT)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F v z
    exact chainPush_eq_sum chain (fun _ => Unit) (fun u _ x => F u x) F
      (fun u x => (Fintype.sum_unique (fun _ : Unit => F u x)).symm) v z
  · intro v
    exact (chainAncestors_le chain _ _ (fun _ => le_rfl) v).trans (hocc v)
  · exact termChain_payloadLe _ _ hb hXM ι hrec
  · intro v
    refine (card_chainDom_le chain hcov hrec (fun _ => Unit) (fun _ => 1)
      (fun _ => by rw [Fintype.card_unit, one_mul]; exact Nat.one_le_two_pow) v).trans ?_
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (hocc v))

end

end P1P5
