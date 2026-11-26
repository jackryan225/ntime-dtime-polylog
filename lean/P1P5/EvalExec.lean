import P1P5.EvalSize

/-!
# P1, task P8a: site bounds along `B.execute`, and the size of the cone encoding

* `slotRecords_newCovered`: OpenAI's slot records contain the half-fields of every NEW site, so the
  half-assignments of a new site number at most `2 ^ (sum of its recorded widths)`; carried to
  `B.records` (`execute_newCovered`) exactly as `execute_halfCovered` (Cover.lean).
* `termChain_siteLe`: every half-assignment set and placed set on a selected chain has at most
  `2 ^ (C' M)` elements (`C'` = the pass constant of `Bounded`), given the bound on the input network.
* `encSize_le'`: the cone encoding of every branch of `B.execute` has
  `dataSize ≤ 8 (C^T+1)^3 2^(3 (C + 2·2^{d₀}) M) + (steps+1) T`, `M = C^T (W₀+1)`, `d₀ = S.degreeExponent 0`.
-/

namespace P1P5

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.Refresh

open scoped Classical

noncomputable section

theorem card_half_cast {N Y : Network} (h : N = Y) (w : N.Site) :
    Fintype.card (N.Half w) = Fintype.card (Y.Half (Equiv.cast (congrArg Network.Site h) w)) := by
  subst h
  rfl

section Exec

variable {R : Type*} [CommSemiring R]

/-- Pass level: the half-assignments of each new site fit into its recorded widths. -/
def PassNewCovered {a g a' g' : ℕ} {X : State a g} (p : StatePass R X a' g') (recs : p.Records) :
    Prop :=
  ∀ i w, Fintype.card ((p.step.term i).output.Half w) ≤ 2 ^ ∑ f, (recs i w).width f

theorem slotRecords_newCovered {a g b n : ℕ} {X : State a g} (p : StatePass R X b n)
    (extra : p.Records) : PassNewCovered p (p.slotRecords extra) := by
  intro i w
  rw [card_half_cast (p.output_eq i) w]
  change Fintype.card ((p.next i).network.Half (p.outputSite i w)) ≤ _
  rw [card_half]
  apply Nat.pow_le_pow_right (by norm_num)
  show _ ≤ ∑ f : (extra i w).Field ⊕ (((p.step.term i).Preimage w × (Bool × Fin (2 ^ a))) ⊕
      (Bool × Fin (2 ^ b))), Sum.elim (extra i w).width (Sum.elim
        (fun x => X.halfWidth x.1.val x.2.1 x.2.2)
        (fun x => (p.next i).halfWidth (p.outputSite i w) x.1 x.2)) f
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  exact le_add_left (le_add_left le_rfl)

def ExecNewCovered {b n : ℕ} : {a g : ℕ} → {X : State a g} → (E : StateExecution R b n X) →
    E.Records → Prop
  | _, _, _, .done _, _ => True
  | _, _, _, .more p tail, recs => PassNewCovered p recs.1 ∧ ∀ i, ExecNewCovered (tail i) (recs.2 i)

theorem execNewCovered_bind {b n b' n' : ℕ} : ∀ {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (f : (z : E.Choices) → StateExecution R b' n' (E.finalState z))
    (u : E.Records) (v : ∀ z, (f z).Records),
    ExecNewCovered E u → (∀ z, ExecNewCovered (f z) (v z)) →
    ExecNewCovered (E.bind f) (E.bindRecords f u v) := by
  intro a g X E
  induction E with
  | done X =>
    intro f u v _ hv
    exact hv ()
  | more p tail ih =>
    intro f u v hu hv
    exact ⟨hu.1, fun i => ih i _ (u.2 i) _ (hu.2 i) (fun z => hv ⟨i, z⟩)⟩

def ProcNewCovered {a b l d C m : ℕ} {μ : ℝ} {P : Procedure R a b l d μ}
    (B : P.RecordBounds C m) : Prop :=
  ∀ g n h X, ExecNewCovered (P.run g n h X) (B.records g n h X)

namespace ProcNewCovered

variable {a b l d C m : ℕ} {μ : ℝ}

theorem id (a C : ℕ) : ProcNewCovered (Procedure.RecordBounds.id R a C) := by
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
    (hcov : ∀ g X, PassNewCovered (f g X) (rec g X)) :
    ProcNewCovered (Procedure.RecordBounds.ofPass hd hμ hA f hc he rec hb) := by
  intro g n h X
  subst n
  exact ⟨hcov g X, fun _ => trivial⟩

theorem seq {c l' d' D n : ℕ} {ν : ℝ} {P : Procedure R a b l d μ} {Q : Procedure R b c l' d' ν}
    {B : P.RecordBounds C m} {B' : Q.RecordBounds D n}
    (h : ProcNewCovered B) (h' : ProcNewCovered B') : ProcNewCovered (B.seq B') :=
  fun g n eqn X =>
    let E := P.run (l' + g) n (eqn.trans (Nat.add_assoc l l' g)) X
    execNewCovered_bind E _ _ _ (h _ _ _ X) (fun z => h' _ _ _ (E.finalState z))

theorem mono {P : Procedure R a b l d μ} {B : P.RecordBounds C m} {D n : ℕ}
    (h : ProcNewCovered B) (hC : C ≤ D) (hm : m ≤ n) : ProcNewCovered (B.mono hC hm) := h

theorem reindex {a' b' l' d' : ℕ} {μ' : ℝ} {P : Procedure R a b l d μ} {B : P.RecordBounds C m}
    (h : ProcNewCovered B) {ha : a = a'} {hb : b = b'} {hl : l = l'} {hd : d = d'} {hμ : μ = μ'} :
    ProcNewCovered (B.reindex (ha := ha) (hb := hb) (hk := hl) (hp := hd) (hμ := hμ)) := by
  subst a' b' l' d' μ'
  exact h

end ProcNewCovered

theorem repeat_newCovered {a l d C m : ℕ} {μ : ℝ} {P : Procedure R a a l d μ}
    {B : P.RecordBounds C m} (hc : ProcNewCovered B) (g T n : ℕ) (h : n = T * l + g)
    (X : State a n) :
    ExecNewCovered (P.repeatExecution g T n h X) (Procedure.repeatRecords B g T n h X) := by
  induction T generalizing n with
  | zero =>
    have hn : n = g := by simpa using h
    subst g
    trivial
  | succ t ih =>
    let E := P.run (t * l + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact execNewCovered_bind E _ _ _ (hc _ _ _ X) (fun z => ih _ rfl (E.finalState z))

/-- Site bounds along every selected chain of an execution. -/
theorem termChain_siteLe {b n : ℕ} : ∀ {a g : ℕ} {X : State a g} (E : StateExecution R b n X)
    (recs : E.Records) {C : ℕ}, E.Bounded C recs → ExecHalfCovered E recs → ExecNewCovered E recs →
    ∀ {M A : ℕ}, 2 ^ (C * M) ≤ A → (∀ u, Fintype.card (X.network.Half u) ≤ A) →
    ∀ z, (E.termChain recs z).AllRecordsLe M → ChainSiteLe (E.termChain recs z) A := by
  intro a g X E
  induction E with
  | done =>
    intro recs C _ _ _ M A _ hX z _
    exact hX
  | @more a0 g0 a1 g1 X0 p tail ih =>
    intro recs C hb hh hn M A hA hX z hM
    obtain ⟨hw, -, hM'⟩ := hM
    have hM'' := (allRecordsLe_cast (p.output_eq z.1) ((tail z.1).termChain (recs.2 z.1) z.2) M).mp hM'
    have hwid : ∀ w, 2 ^ (∑ f, (recs.1 z.1 w).width f) ≤ A := by
      intro w
      refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hA
      calc ∑ f, (recs.1 z.1 w).width f ≤ ∑ _f : (recs.1 z.1 w).Field, M :=
            Finset.sum_le_sum (fun f _ => hw w f)
        _ = Fintype.card (recs.1 z.1 w).Field * M := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        _ ≤ C * M := by
            apply Nat.mul_le_mul_right
            have h1 := ((hb.1 z.1).1 w)
            unfold SiteRecords.count at h1
            omega
    have hplaced : ∀ w, Fintype.card (Placed (p.step.term z.1).place X0.network.Half w) ≤ A := by
      intro w
      rw [card_placed]
      exact (hh.1 z.1 w).trans (hwid w)
    have hnext : ∀ u, Fintype.card ((p.next z.1).network.Half u) ≤ A := by
      intro u
      have e := card_half_cast (p.output_eq z.1) ((p.outputSite z.1).symm u)
      have e2 : Equiv.cast (congrArg Network.Site (p.output_eq z.1)) ((p.outputSite z.1).symm u) = u :=
        (p.outputSite z.1).apply_symm_apply u
      rw [e2] at e
      rw [← e]
      exact (hn.1 z.1 _).trans (hwid _)
    exact ⟨hX, hplaced, (siteLe_cast (p.output_eq z.1) ((tail z.1).termChain (recs.2 z.1) z.2) A).mpr
      (ih z.1 (recs.2 z.1) (hb.2 z.1) (hh.2 z.1) (hn.2 z.1) hA hnext z.2 hM'')⟩

end Exec

section Block

open private prefixRecordBounds from OAI.Computability.VPVNP.CompressionBlockHistory

variable {R : Type*} [CommRing R] {k : Type*} [Field k] (S : BlockSchedule k)

private theorem prefix_newCovered {C : ℕ} (shrink : S.ShrinkProcedures R)
    (B : ∀ i, (shrink i).RecordBounds C 1) (h : ∀ i, ProcNewCovered (B i))
    (j : ℕ) (hj : j ≤ S.steps) : ProcNewCovered (prefixRecordBounds S shrink B j hj) := by
  induction j with
  | zero =>
    simp only [prefixRecordBounds, BlockSchedule.shrinkPrefix]
    exact (ProcNewCovered.id _ C).reindex
  | succ j ih =>
    simp only [prefixRecordBounds, BlockSchedule.shrinkPrefix]
    exact (((ih (Nat.le_of_succ_le hj)).seq (h ⟨j, hj⟩).reindex).mono
      (max_le le_rfl le_rfl) le_rfl).reindex

theorem assemble_newCovered {C : ℕ} (shrink : S.ShrinkProcedures R)
    (refresh : S.RefreshProcedure R) {D : Fin S.steps → ℕ}
    (B : ∀ i, (shrink i).RecordBounds (D i) 1) (B' : refresh.RecordBounds C 1)
    (h : ∀ i, ProcNewCovered (B i)) (h' : ProcNewCovered B') :
    ProcNewCovered (S.assembleBlockRecords shrink refresh B B') := by
  unfold BlockSchedule.assembleBlockRecords
  apply ProcNewCovered.reindex
  apply ProcNewCovered.seq _ h'
  apply ProcNewCovered.reindex
  exact prefix_newCovered S shrink _ (fun i => h i) S.steps le_rfl

end Block

section Templates

open private recordsAt from OAI.Computability.VPVNP.ShrinkProcedureHistory

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

theorem shrinkPass_newCovered (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    PassNewCovered (B.shrinkPassAt f hf i h X) (recordsAt B f hf i h X) := by
  subst n
  exact slotRecords_newCovered
    (X.shrinkStatePass B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i))
    (X.shrinkExtraRecords B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i))

theorem shrinkProcedure_newCovered (i : Fin S.steps) :
    ProcNewCovered (B.shrinkProcedureRecords f hf i) :=
  ProcNewCovered.ofPass _ _ _ _ _ _ _ _
    (fun g X => shrinkPass_newCovered B f hf i (packingLaneBits_add _ g) X)

theorem refreshProcedure_newCovered : ProcNewCovered (B.refreshProcedureRecords f hf) := by
  intro g n h X
  subst n
  exact ⟨slotRecords_newCovered
    (dyadicRefreshPass X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh S.port_order S.degree_bounds.2 (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2)
    (refreshLocalRecords X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1
      B.refresh S.port_order S.degree_bounds.2 (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2),
    fun _ => trivial⟩

theorem procedure_newCovered : ProcNewCovered (B.recordBounds f hf) :=
  assemble_newCovered S _ _ _ _ (fun i => shrinkProcedure_newCovered B f hf i)
    (refreshProcedure_newCovered B f hf)

theorem execute_newCovered {n : ℕ} (T : ℕ) (h : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) :
    ExecNewCovered (B.execute f hf T h X) (B.records f hf T h X) :=
  repeat_newCovered (procedure_newCovered B f hf) _ T n (Nat.add_sub_of_le h).symm X

end Templates

section Size

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type} [CommRing R] (κ : B.Entry → R) (hκ : B.IsSolution κ)

theorem recordLimit_le_growth : B.recordLimit ≤ B.growthConstant := by
  show B.recordLimit ≤ max 2 (B.recordLimit ^ (S.steps + 1))
  exact le_max_of_le_right (Nat.le_self_pow (Nat.succ_ne_zero _) _)

theorem card_half_le {a g : ℕ} (X : State a g) (u : X.network.Site) {M : ℕ}
    (hM : X.maxWireWidth ≤ M) : Fintype.card (X.network.Half u) ≤ 2 ^ (2 * 2 ^ a * M) := by
  rw [card_half]
  apply Nat.pow_le_pow_right (by norm_num)
  calc ∑ dir : Bool, ∑ j : Fin (2 ^ a), X.halfWidth u dir j ≤ ∑ _dir : Bool, ∑ _j : Fin (2 ^ a), M :=
        Finset.sum_le_sum (fun dir _ => Finset.sum_le_sum (fun j _ =>
          (X.halfWidth_le_max u dir j).trans hM))
    _ = 2 * 2 ^ a * M := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Nat.mul_assoc]

/-- **Size of the cone encoding of every branch of `B.execute`.** -/
theorem encSize_le' {n : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n) (ι : (B.execute κ hκ T hn X).Choices)
    (F : Factors R X.network) (v : ((B.execute κ hκ T hn X).finalState ι).network.Site)
    (z : ((B.execute κ hκ T hn X).finalState ι).network.Half v) :
    dataSize (encLevels ((B.execute κ hκ T hn X).termChain (B.records κ hκ T hn X) ι) v)
        (stateOf X.network
          (fun u => toFinal ((B.execute κ hκ T hn X).termChain (B.records κ hκ T hn X) ι) u = v) F)
        (finalIndex _ v z) ≤
      8 * (B.growthConstant ^ T + 1) ^ 3 *
          2 ^ (3 * ((B.growthConstant + 2 * 2 ^ S.degreeExponent 0) *
            (B.growthConstant ^ T * (X.maxWireWidth + 1)))) +
        (S.steps + 1) * T := by
  set chain := (B.execute κ hκ T hn X).termChain (B.records κ hκ T hn X) ι with hchain
  set C := B.growthConstant with hC
  set M := C ^ T * (X.maxWireWidth + 1) with hM
  set e := (C + 2 * 2 ^ S.degreeExponent 0) * M with he
  set A := 2 ^ e with hAdef
  set Q := C ^ T with hQdef
  obtain ⟨-, -, -, hocc, hrec, -⟩ := B.branch_bounds κ hκ T hn X ι
  have hrb := Procedure.repeat_recordBounds (B.recordBounds κ hκ) (n - T * S.laneBits) T n
    (Nat.add_sub_of_le hn).symm X
  have hb : (B.execute κ hκ T hn X).Bounded B.recordLimit (B.records κ hκ T hn X) := hrb.1
  have hlen : chain.length ≤ (S.steps + 1) * T := hrb.2 ι
  have hCT : 0 < C ^ T := pow_pos (lt_of_lt_of_le (by norm_num) B.growthConstant_ge_two) T
  have hXM : X.maxWireWidth ≤ M := (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hCT)
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  have hAr : 2 ^ (B.recordLimit * M) ≤ A := by
    apply Nat.pow_le_pow_right (by norm_num)
    apply Nat.mul_le_mul_right
    exact (recordLimit_le_growth B).trans (Nat.le_add_right _ _)
  have hX : ∀ u, Fintype.card (X.network.Half u) ≤ A := by
    intro u
    refine (card_half_le X u hXM).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  have hS : ChainSiteLe chain A :=
    termChain_siteLe _ _ hb (execute_halfCovered B κ hκ T hn X) (execute_newCovered B κ hκ T hn X)
      hAr hX ι hrec
  have hgen := dataSize_le_generic chain F v z A Q hA1 hS (hocc v)
  have e1 : A * Q + A ≤ A ^ 3 * (Q + 1) ^ 3 := by
    have h := Nat.mul_le_mul (Nat.le_self_pow (n := 3) (by norm_num) A)
      (Nat.le_self_pow (n := 3) (by norm_num) (Q + 1))
    calc A * Q + A = A * (Q + 1) := by ring
      _ ≤ _ := h
  have e2 : 4 * A ^ 3 * (Q + 1) ^ 2 * Q ≤ 4 * (A ^ 3 * (Q + 1) ^ 3) := by
    calc 4 * A ^ 3 * (Q + 1) ^ 2 * Q = 4 * A ^ 3 * ((Q + 1) ^ 2 * Q) := by ring
      _ ≤ 4 * A ^ 3 * ((Q + 1) ^ 2 * (Q + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ Q))
      _ = 4 * (A ^ 3 * (Q + 1) ^ 3) := by ring
  have e3 : 8 * (Q + 1) ^ 3 * 2 ^ (3 * e) = 8 * (A ^ 3 * (Q + 1) ^ 3) := by
    rw [hAdef, ← pow_mul]
    ring_nf
  rw [e3]
  omega

end Size

end

end P1P5
