import P1P5.Generic

/-!
# P1, task P5: the records of `B.execute` cover the enumeration domains (faithfulness link)

OpenAI's `StatePass.slotRecords` (StatePassHistory.lean:41) records, at each new site, both
half-fields of every placed old site with the actual widths `State.halfWidth`. Here:

* `card_half`: the half-wire assignments at a site of a state network number exactly
  `2 ^ (∑ dir, ∑ slot, halfWidth)` (outgoing and incoming slots of `Refresh.actualWireGraph`);
* `slotRecords_halfCovered`: hence every pass with slot records is half-covered;
* the property is carried through `RecordBounds.ofPass/seq/mono/reindex`, the shrink prefix, the block
  assembly and the repetition, exactly along OpenAI's proof of `execute_degreeCovered`
  (CompressionDegreeCoverage.lean, CompressionDegreeAssembly.lean);
* `execute_halfCovered`: the records `B.records` of `B.execute` are half-covered.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh

open scoped Classical

noncomputable section

section StateNet

variable {a g : ℕ}

/-- Outgoing wires at a site of a state network: one per slot. -/
def outEquiv (X : State a g) (u : X.network.Site) :
    {e : X.network.Edge // u = X.network.src e} ≃ Fin (2 ^ a) where
  toFun e := e.val.2
  invFun j := ⟨(u, j), rfl⟩
  left_inv e := by
    obtain ⟨⟨u', j⟩, h⟩ := e
    change u = u' at h
    subst h
    rfl
  right_inv _ := rfl

/-- Incoming wires at a site of a state network: one per slot. -/
def inEquiv (X : State a g) (u : X.network.Site) :
    {e : X.network.Edge // u = X.network.dst e} ≃ Fin (2 ^ a) where
  toFun e := (X.slots.actualGraph.target e.val).2
  invFun j := ⟨X.slots.actualGraph.target.symm (u, j), by
    show u = (X.slots.actualGraph.target (X.slots.actualGraph.target.symm (u, j))).1
    rw [Equiv.apply_symm_apply]⟩
  left_inv e := by
    obtain ⟨e, h⟩ := e
    apply Subtype.ext
    change X.slots.actualGraph.target.symm (u, (X.slots.actualGraph.target e).2) = e
    have h' : u = (X.slots.actualGraph.target e).1 := h
    rw [h', Prod.mk.eta]
    exact X.slots.actualGraph.target.symm_apply_apply e
  right_inv j := by
    change (X.slots.actualGraph.target (X.slots.actualGraph.target.symm (u, j))).2 = j
    rw [Equiv.apply_symm_apply]

theorem sum_out (X : State a g) (u : X.network.Site) :
    ∑ e : {e : X.network.Edge // u = X.network.src e}, X.width ((e.val.1.1, e.val.2), e.val.1.2) =
      ∑ j : Fin (2 ^ a), X.halfWidth u false j := by
  refine Fintype.sum_equiv (outEquiv X u) _ _ (fun e => ?_)
  obtain ⟨⟨u', j⟩, h⟩ := e
  change u = u' at h
  subst h
  rfl

theorem sum_in (X : State a g) (u : X.network.Site) :
    ∑ e : {e : X.network.Edge // u = X.network.dst e}, X.width ((e.val.1.1, e.val.2), e.val.1.2) =
      ∑ j : Fin (2 ^ a), X.halfWidth u true j := by
  refine Fintype.sum_equiv (inEquiv X u) _ _ (fun e => ?_)
  obtain ⟨⟨⟨x, l⟩, i⟩, h⟩ := e
  have h' : u = (X.slots.actualGraph.target ((x, l), i)).1 := h
  subst h'
  show X.width ((x, i), l) = X.halfWidth (X.slots.actualGraph.target ((x, l), i)).1 true
    (X.slots.actualGraph.target ((x, l), i)).2
  simp [State.halfWidth, LiftedSlots.actualGraph_target, LiftedSlots.actualTarget_symm_apply]

/-- The half-wire assignments at a site of a state network: one word of the actual width per
outgoing and per incoming slot. -/
theorem card_half (X : State a g) (u : X.network.Site) :
    Fintype.card (X.network.Half u) = 2 ^ ∑ dir : Bool, ∑ j : Fin (2 ^ a), X.halfWidth u dir j := by
  rw [Fintype.card_prod, card_placed X.network.src X.network.Payload u,
    card_placed X.network.dst X.network.Payload u]
  simp only [card_payload]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, sum_out, sum_in,
    Fintype.sum_bool]
  congr 1
  exact Nat.add_comm _ _

end StateNet

section Exec

variable {R : Type*} [CommSemiring R]

/-- Slot records contain both half-fields of every placed old site: every pass with slot records is
half-covered, whatever its extra motif records are. -/
theorem slotRecords_halfCovered {a g b n : ℕ} {X : State a g} (p : StatePass R X b n)
    (extra : p.Records) : PassHalfCovered p (p.slotRecords extra) := by
  intro i w
  simp only [card_half]
  rw [Finset.prod_pow_eq_pow_sum]
  apply Nat.pow_le_pow_right (by norm_num)
  show _ ≤ ∑ f : (extra i w).Field ⊕ (((p.step.term i).Preimage w × (Bool × Fin (2 ^ a))) ⊕
      (Bool × Fin (2 ^ b))), Sum.elim (extra i w).width (Sum.elim
        (fun x => X.halfWidth x.1.val x.2.1 x.2.2)
        (fun x => (p.next i).halfWidth (p.outputSite i w) x.1 x.2)) f
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  exact le_add_left (le_add_right le_rfl)

theorem execHalfCovered_bind {b n b' n' : ℕ} : ∀ {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (u : E.Records) (v : ∀ z, (f z).Records),
    ExecHalfCovered E u → (∀ z, ExecHalfCovered (f z) (v z)) →
    ExecHalfCovered (E.bind f) (E.bindRecords f u v) := by
  intro a g X E
  induction E with
  | done X =>
    intro f u v _ hv
    exact hv ()
  | more p tail ih =>
    intro f u v hu hv
    exact ⟨hu.1, fun i => ih i _ (u.2 i) _ (hu.2 i) (fun z => hv ⟨i, z⟩)⟩

/-- Half-covering for every admissible input of a procedure. -/
def ProcHalfCovered {a b l d C m : ℕ} {μ : ℝ} {P : Procedure R a b l d μ}
    (B : P.RecordBounds C m) : Prop :=
  ∀ g n h X, ExecHalfCovered (P.run g n h X) (B.records g n h X)

namespace ProcHalfCovered

variable {a b l d C m : ℕ} {μ : ℝ}

theorem id (a C : ℕ) : ProcHalfCovered (Procedure.RecordBounds.id R a C) := by
  intro g n h X
  have hn := h.trans (Nat.zero_add g)
  subst g
  trivial

theorem ofPass {A : ℝ} (hd : 0 < d) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (f : ∀ g (X : State a (l + g)), StatePass R X b g)
    (hc : ∀ g X (i : (f g X).step.Choice), X.positions = d * ((f g X).next i).positions)
    (he : ∀ g X (i : (f g X).step.Choice),
      ((f g X).next i).energy ≤ μ * X.energy + A * (X.positions : ℝ) ^ 2)
    (rec : ∀ g X, (f g X).Records) (hb : ∀ g X, (f g X).Bounded (rec g X) C)
    (hcov : ∀ g X, PassHalfCovered (f g X) (rec g X)) :
    ProcHalfCovered (Procedure.RecordBounds.ofPass hd hμ hA f hc he rec hb) := by
  intro g n h X
  subst n
  exact ⟨hcov g X, fun _ => trivial⟩

theorem seq {c l' d' D n : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {B : P.RecordBounds C m} {B' : Q.RecordBounds D n}
    (h : ProcHalfCovered B) (h' : ProcHalfCovered B') : ProcHalfCovered (B.seq B') :=
  fun g n eqn X =>
    let E := P.run (l' + g) n (eqn.trans (Nat.add_assoc l l' g)) X
    execHalfCovered_bind E _ _ _ (h _ _ _ X) (fun z => h' _ _ _ (E.finalState z))

theorem mono {P : Procedure R a b l d μ} {B : P.RecordBounds C m} {D n : ℕ}
    (h : ProcHalfCovered B) (hC : C ≤ D) (hm : m ≤ n) : ProcHalfCovered (B.mono hC hm) := h

theorem reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {B : P.RecordBounds C m}
    (h : ProcHalfCovered B) {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    ProcHalfCovered (B.reindex (ha := ha) (hb := hb) (hk := hl) (hp := hd) (hμ := hμ)) := by
  subst a' b' l' d' μ'
  exact h

end ProcHalfCovered

theorem repeat_halfCovered {a l d C m : ℕ} {μ : ℝ} {P : Procedure R a a l d μ}
    {B : P.RecordBounds C m} (hc : ProcHalfCovered B) (g T n : ℕ) (h : n = T * l + g)
    (X : State a n) :
    ExecHalfCovered (P.repeatExecution g T n h X) (Procedure.repeatRecords B g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t * l + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact execHalfCovered_bind E _ _ _ (hc _ _ _ X) (fun z => ih _ rfl (E.finalState z))

end Exec

section Block

open private prefixRecordBounds from OAI.Computability.VPVNP.CompressionBlockHistory

variable {R : Type*} [CommRing R] {k : Type*} [Field k] (S : BlockSchedule k)

private theorem prefix_halfCovered {C : ℕ} (shrink : S.ShrinkProcedures R)
    (B : ∀ i, (shrink i).RecordBounds C 1) (h : ∀ i, ProcHalfCovered (B i))
    (j : ℕ) (hj : j ≤ S.steps) : ProcHalfCovered (prefixRecordBounds S shrink B j hj) := by
  induction j with
  | zero =>
    simp only [prefixRecordBounds, BlockSchedule.shrinkPrefix]
    exact (ProcHalfCovered.id _ C).reindex
  | succ j ih =>
    simp only [prefixRecordBounds, BlockSchedule.shrinkPrefix]
    exact (((ih (Nat.le_of_succ_le hj)).seq (h ⟨j, hj⟩).reindex).mono
      (max_le le_rfl le_rfl) le_rfl).reindex

theorem assemble_halfCovered {C : ℕ} (shrink : S.ShrinkProcedures R)
    (refresh : S.RefreshProcedure R) {D : Fin S.steps → ℕ}
    (B : ∀ i, (shrink i).RecordBounds (D i) 1) (B' : refresh.RecordBounds C 1)
    (h : ∀ i, ProcHalfCovered (B i)) (h' : ProcHalfCovered B') :
    ProcHalfCovered (S.assembleBlockRecords shrink refresh B B') := by
  unfold BlockSchedule.assembleBlockRecords
  apply ProcHalfCovered.reindex
  apply ProcHalfCovered.seq _ h'
  apply ProcHalfCovered.reindex
  exact prefix_halfCovered S shrink _ (fun i => h i) S.steps le_rfl

end Block

section Templates

open private recordsAt from OAI.Computability.VPVNP.ShrinkProcedureHistory

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

theorem shrinkPass_halfCovered (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    PassHalfCovered (B.shrinkPassAt f hf i h X) (recordsAt B f hf i h X) := by
  subst n
  exact slotRecords_halfCovered
    (X.shrinkStatePass B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i))
    (X.shrinkExtraRecords B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i))

theorem shrinkProcedure_halfCovered (i : Fin S.steps) :
    ProcHalfCovered (B.shrinkProcedureRecords f hf i) :=
  ProcHalfCovered.ofPass _ _ _ _ _ _ _ _
    (fun g X => shrinkPass_halfCovered B f hf i (packingLaneBits_add _ g) X)

theorem refreshProcedure_halfCovered : ProcHalfCovered (B.refreshProcedureRecords f hf) := by
  intro g n h X
  subst n
  exact ⟨slotRecords_halfCovered
    (dyadicRefreshPass X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh S.port_order S.degree_bounds.2 (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2)
    (refreshLocalRecords X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh S.port_order S.degree_bounds.2 (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2),
    fun _ => trivial⟩

theorem procedure_halfCovered : ProcHalfCovered (B.recordBounds f hf) :=
  assemble_halfCovered S _ _ _ _ (fun i => shrinkProcedure_halfCovered B f hf i)
    (refreshProcedure_halfCovered B f hf)

/-- **Faithfulness link.** The actual records of `B.execute` half-cover every selected term. -/
theorem execute_halfCovered {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    ExecHalfCovered (B.execute f hf T h X) (B.records f hf T h X) :=
  repeat_halfCovered (procedure_halfCovered B f hf) _ T n (Nat.add_sub_of_le h).symm X

end Templates

end

end P1P5
