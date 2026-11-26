import P1P5.Defs

/-!
# P1, task P5: generic lemmas on pushed chains

* `push_eq_sum`, `chainPush_eq_sum`: a pushed factor is the finite sum of `chainSummand` over `chainDom`.
* `card_chainDom_le`: under `ChainHalfCovered` and OpenAI's `AllRecordsLe M`, the domain has at most
  `2 ^ (occurrences * M)` elements (`occurrences` = OpenAI's `TermChain.occurrences`).
* `chainAncestors_le`: the placement tree has at most `occurrences` sites.
* `contract_eq_sum_chainPush`: the contraction of the initial network is the sum over the branches of
  an execution of the contractions of the final networks against the pushed factors.
* `termChain_halfCovered`, `termChain_payloadLe`: transport of execution-level facts to the chains
  `E.termChain recs z`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.WireTensor

open scoped Classical

noncomputable section

section Chain

variable {k : Type*} [CommSemiring k]

/-! ### Casts along `StatePass.output_eq` (the same form as OpenAI's `cast_peak`) -/

theorem chainPush_cast {N Y Z : Network} (h : N = Y) (c : TermChain k Y Z) (F : Factors k N) :
    chainPush (h.symm ▸ c : TermChain k N Z) F = chainPush c (h ▸ F : Factors k Y) := by
  subst h
  rfl

theorem contract_cast {N Y : Network} (h : N = Y) (F : Factors k N) :
    contract N F = contract Y (h ▸ F : Factors k Y) := by
  subst h
  rfl

theorem halfCovered_cast {N Y Z : Network} (h : N = Y) (c : TermChain k Y Z) :
    ChainHalfCovered (h.symm ▸ c : TermChain k N Z) ↔ ChainHalfCovered c := by
  subst h
  rfl

theorem payloadLe_cast {N Y Z : Network} (h : N = Y) (c : TermChain k Y Z) (M : ℕ) :
    ChainPayloadLe (h.symm ▸ c : TermChain k N Z) M ↔ ChainPayloadLe c M := by
  subst h
  rfl

theorem allRecordsLe_cast {N Y Z : Network} (h : N = Y) (c : TermChain k Y Z) (M : ℕ) :
    (h.symm ▸ c : TermChain k N Z).AllRecordsLe M ↔ c.AllRecordsLe M := by
  subst h
  rfl

/-! ### One level: a pushed factor as a finite sum -/

/-- A product of dependent sums over the fibre of a predicate is a sum over placed choices. -/
theorem prod_dite_sum {U : Type} [Fintype U] (P : U → Prop) (D : U → Type)
    [∀ u, Fintype (D u)] (g : ∀ u, P u → D u → k) :
    (∏ u, if h : P u then ∑ d : D u, g u h d else 1) =
      ∑ e : (u : U) → P u → D u, ∏ u, if h : P u then g u h (e u h) else 1 := by
  rw [← Fintype.prod_sum (fun u (e : P u → D u) => if h : P u then g u h (e h) else 1)]
  apply Finset.prod_congr rfl
  intro u _
  by_cases hu : P u
  · rw [dif_pos hu]
    simp only [dif_pos hu]
    exact (Fintype.sum_equiv
      { toFun := fun e : P u → D u => e hu, invFun := fun d _ => d,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      (fun e : P u → D u => g u hu (e hu)) (fun d => g u hu d) (fun _ => rfl)).symm
  · rw [dif_neg hu]
    simp only [dif_neg hu]
    haveI : IsEmpty (P u) := ⟨hu⟩
    simp

/-- One pushed factor (`Term.push`) as a finite sum over the old half-wire assignments placed at the
new site and the domains of the placed old factors. -/
theorem push_eq_sum {N : Network} (t : Term k N) (D : N.Site → Type) [∀ u, Fintype (D u)]
    (G : ∀ u, D u → N.Half u → k) (F : Factors k N)
    (hF : ∀ u x, F u x = ∑ d : D u, G u d x) (w : t.output.Site) (z : t.output.Half w) :
    t.push F w z = ∑ d : Placed t.place N.Half w × Placed t.place D w,
      (∏ u, if h : w = t.place u then G u (d.2 u h) (d.1 u h) else 1) * t.kernel w d.1 z := by
  simp only [Term.push, Term.placedProduct]
  rw [Fintype.sum_prod_type]
  dsimp only
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul]
  congr 1
  simp only [hF]
  exact prod_dite_sum (fun u => w = t.place u) D (fun u h d => G u d (a u h))

/-- **Enumeration form.** Along a whole chain, the pushed factor is the finite sum of the summands
over the enumeration domain. -/
theorem chainPush_eq_sum : ∀ {N Y : Network} (c : TermChain k N Y) (D : N.Site → Type)
    [∀ u, Fintype (D u)] (G : ∀ u, D u → N.Half u → k) (F : Factors k N),
    (∀ u x, F u x = ∑ d : D u, G u d x) →
    ∀ v z, chainPush c F v z = ∑ d : chainDom c D v, chainSummand c D G v d z := by
  intro N Y c
  induction c with
  | done N =>
    intro D _ G F hF v z
    exact hF v z
  | more t recs tail ih =>
    intro D _ G F hF v z
    exact ih _ _ (t.push F) (push_eq_sum t D G F hF) v z

/-! ### Size of the enumeration domain -/

/-- Placed assignments at `w` are the assignments of the placement fibre of `w`. -/
def placedEquiv {U V : Type} (p : U → V) (B : U → Type) (w : V) :
    Placed p B w ≃ ((u : {u // w = p u}) → B u.val) where
  toFun a u := a u.1 u.2
  invFun b u h := b ⟨u, h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_placed {U V : Type} [Fintype U] (p : U → V) (B : U → Type) [∀ u, Fintype (B u)]
    (w : V) : Fintype.card (Placed p B w) = ∏ u : {u // w = p u}, Fintype.card (B u.val) := by
  rw [Fintype.card_congr (placedEquiv p B w), Fintype.card_pi]

/-- **Domain bound.** If every level is half-covered by its records and every record is at most `M`,
the enumeration domain at a final site has at most `2 ^ (occurrences * M)` elements. -/
theorem card_chainDom_le : ∀ {N Y : Network} (c : TermChain k N Y), ChainHalfCovered c →
    ∀ {M : ℕ}, c.AllRecordsLe M → ∀ (D : N.Site → Type) [∀ u, Fintype (D u)] (init : N.Site → ℕ),
    (∀ u, Fintype.card (D u) ≤ 2 ^ (init u * M)) →
    ∀ v, Fintype.card (chainDom c D v) ≤ 2 ^ (c.occurrences init v * M) := by
  intro N Y c
  induction c with
  | done N =>
    intro _ M _ D _ init hD v
    exact hD v
  | more t recs tail ih =>
    intro hc M hM D _ init hD v
    obtain ⟨hcov, hc'⟩ := hc
    obtain ⟨hw, -, hM'⟩ := hM
    refine ih hc' hM' _ (t.pushHistorySize recs init) ?_ v
    intro w
    rw [Fintype.card_prod, card_placed, card_placed]
    have h1 := hcov w
    have h2 : ∏ u : t.Preimage w, Fintype.card (D u.val) ≤ ∏ u : t.Preimage w, 2 ^ (init u.val * M) :=
      Finset.prod_le_prod (fun u _ => hD u.val)
    rw [Finset.prod_pow_eq_pow_sum] at h2
    have h3 : ∑ f, (recs w).width f ≤ (recs w).count * M := by
      calc ∑ f, (recs w).width f ≤ ∑ _f : (recs w).Field, M := Finset.sum_le_sum (fun f _ => hw w f)
        _ = Fintype.card (recs w).Field * M := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ ≤ (recs w).count * M := Nat.mul_le_mul_right _ (by unfold SiteRecords.count; omega)
    have hexp : ∑ f, (recs w).width f + ∑ u : t.Preimage w, init u.val * M ≤
        t.pushHistorySize recs init w * M := by
      unfold Term.pushHistorySize
      rw [Nat.add_mul, Finset.sum_mul]
      exact Nat.add_le_add_right h3 _
    calc _ ≤ 2 ^ (∑ f, (recs w).width f) * 2 ^ (∑ u : t.Preimage w, init u.val * M) :=
          Nat.mul_le_mul h1 h2
      _ = 2 ^ (∑ f, (recs w).width f + ∑ u : t.Preimage w, init u.val * M) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (t.pushHistorySize recs init w * M) := Nat.pow_le_pow_right (by norm_num) hexp

/-- The placement tree has at most as many sites as OpenAI's occurrence count. -/
theorem chainAncestors_le : ∀ {N Y : Network} (c : TermChain k N Y) (init init' : N.Site → ℕ),
    (∀ u, init u ≤ init' u) → ∀ v, chainAncestors c init v ≤ c.occurrences init' v := by
  intro N Y c
  induction c with
  | done N =>
    intro init init' h v
    exact h v
  | more t recs tail ih =>
    intro init init' h v
    refine ih _ _ (fun w => ?_) v
    unfold Term.pushHistorySize
    have h1 : 1 ≤ (recs w).count := by unfold SiteRecords.count; omega
    exact Nat.add_le_add h1 (Finset.sum_le_sum (fun u _ => h u.val))

end Chain

/-! ### Executions -/

section Exec

variable {R : Type*} [CommSemiring R] {b n : ℕ}

theorem sum_choices_done {M : Type*} [AddCommMonoid M] (X : State b n)
    (f : (StateExecution.done (R := R) X).Choices → M) : ∑ ι, f ι = f () :=
  Fintype.sum_unique (fun ι : Unit => f ι)

theorem sum_choices_more {M : Type*} [AddCommMonoid M] {a g a' g' : ℕ} {X : State a g}
    (p : StatePass R X a' g') (tail : ∀ i, StateExecution R b n (p.next i))
    (f : (StateExecution.more p tail).Choices → M) :
    ∑ ι, f ι = ∑ i, ∑ ι' : (tail i).Choices, f ⟨i, ι'⟩ :=
  Fintype.sum_sigma f

/-- **Push form, any execution.** The contraction of the initial network equals the sum over the
branches of the contractions of the final networks against the pushed factors. -/
theorem contract_eq_sum_chainPush : ∀ {a g : ℕ} {X : State a g} (E : StateExecution R b n X)
    (recs : E.Records) (F : Factors R X.network),
    contract X.network F =
      ∑ ι : E.Choices, contract (E.finalState ι).network (chainPush (E.termChain recs ι) F) := by
  intro a g X E
  induction E with
  | done X =>
    intro recs F
    rw [sum_choices_done]
    rfl
  | more p tail ih =>
    intro recs F
    rw [p.step.contract_eq_sum F, sum_choices_more]
    apply Finset.sum_congr rfl
    intro i _
    rw [contract_cast (p.output_eq i), ih i (recs.2 i)]
    apply Finset.sum_congr rfl
    intro z _
    exact (congrArg (contract ((tail i).finalState z).network)
      (chainPush_cast (p.output_eq i) ((tail i).termChain (recs.2 i) z)
        ((p.step.term i).push F))).symm

/-- Pass level: the old half-wire domains placed at each new site fit into the recorded widths. -/
def PassHalfCovered {a g a' g' : ℕ} {X : State a g} (p : StatePass R X a' g') (recs : p.Records) :
    Prop :=
  ∀ i w, ∏ u : (p.step.term i).Preimage w, Fintype.card (X.network.Half u.val) ≤
    2 ^ ∑ f, (recs i w).width f

/-- Execution level: every pass on every branch is half-covered by its records. -/
def ExecHalfCovered : {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) → E.Records → Prop
  | _, _, _, .done _, _ => True
  | _, _, _, .more p tail, recs => PassHalfCovered p recs.1 ∧ ∀ i, ExecHalfCovered (tail i) (recs.2 i)

theorem termChain_halfCovered : ∀ {a g : ℕ} {X : State a g} (E : StateExecution R b n X)
    (recs : E.Records), ExecHalfCovered E recs → ∀ z, ChainHalfCovered (E.termChain recs z) := by
  intro a g X E
  induction E with
  | done X =>
    intro recs _ z
    trivial
  | more p tail ih =>
    intro recs h z
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1 z.1, (halfCovered_cast (p.output_eq z.1) ((tail z.1).termChain (recs.2 z.1) z.2)).mpr
      (ih z.1 (recs.2 z.1) (h2 z.1) z.2)⟩

theorem card_payload {a g : ℕ} (X : State a g) (e : X.network.Edge) :
    Fintype.card (X.network.Payload e) = 2 ^ X.width ((e.1.1, e.2), e.1.2) := by
  show Fintype.card (Fin (X.width ((e.1.1, e.2), e.1.2)) → Bool) = _
  simp

theorem payload_le {a g : ℕ} (X : State a g) {M : ℕ} (hX : X.maxWireWidth ≤ M)
    (e : X.network.Edge) : Fintype.card (X.network.Payload e) ≤ 2 ^ M := by
  rw [card_payload]
  exact Nat.pow_le_pow_right (by norm_num) ((X.width_le_maxWireWidth _).trans hX)

/-- Every wire of every network of a selected chain has at most `M` bits, when the initial widths
and all records of the chain are at most `M` and the execution satisfies OpenAI's `Bounded`. -/
theorem termChain_payloadLe : ∀ {a g : ℕ} {X : State a g} (E : StateExecution R b n X)
    (recs : E.Records) {C : ℕ}, E.Bounded C recs → ∀ {M : ℕ}, X.maxWireWidth ≤ M →
    ∀ z, (E.termChain recs z).AllRecordsLe M → ChainPayloadLe (E.termChain recs z) M := by
  intro a g X E
  induction E with
  | done =>
    intro recs C _ M hX z _
    exact payload_le _ hX
  | more p tail ih =>
    intro recs C hb M hX z hM
    obtain ⟨hw, hd, hM'⟩ := hM
    have hM'' := (allRecordsLe_cast (p.output_eq z.1) ((tail z.1).termChain (recs.2 z.1) z.2) M).mp hM'
    have hnext : (p.next z.1).maxWireWidth ≤ M := by
      refine ((hb.1 z.1).2.2).trans ?_
      unfold TermChain.largest
      apply Finset.sup_le
      intro v _
      unfold SiteRecords.largest
      apply max_le
      · exact Finset.sup_le (fun f _ => hw v f)
      · exact Finset.sup_le (fun j _ => hd v j)
    exact ⟨payload_le _ hX, (payloadLe_cast (p.output_eq z.1) ((tail z.1).termChain (recs.2 z.1) z.2) M).mpr
      (ih z.1 (recs.2 z.1) (hb.2 z.1) hnext z.2 hM'')⟩

end Exec

end

end P1P5
