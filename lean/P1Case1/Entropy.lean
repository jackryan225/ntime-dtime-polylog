import P1Case1.Table
import OAI.Computability.MultitapeWeakETH.BitRates
import OAI.Computability.MultitapeWeakETH.ExternalRoot

/-!
# P1, Case 1, task G4 + the entropy step: `TransEntropyBound K` for every field `K`

Application of OpenAI's `paired_entropy_external_root` to a network that displays `xᵀ`:
* law: uniform on the set `S` of inputs `x` whose contraction is `c(x) · e_{xᵀ}` (`c(x) ≠ 0`);
* labels: the `N²` bits of `x`; bit `m` is the wire from the input terminal of its block to the output
  terminal of the block of its transposed position `tr m`;
* pins: at every vertex, the input bits attached to it (at most one row, `N` bits);
* local maps: decode the binary edge alphabets to words, feed the pin as the input bits and the
  bit-wire labels as the output bits of OpenAI's table, and check the input end of every bit-wire
  against the pin.
-/

namespace P1Case1.Entropy

open OAI.Computability.MultitapeWeakETH (Word Network block paired_entropy_external_root bitRate
  bitRate_range)
open OAI.Computability.VPVNP.WireTensor Finset OAI.MatrixMultiplication
  OAI.MatrixMultiplication.Foundation
open scoped Classical

noncomputable section

/-! ## Index arithmetic -/

/-- Transposed position: `(r, s) ↦ (s, r)` in row-major order. -/
def tr {N : ℕ} (m : Fin (N * N)) : Fin (N * N) := finProdFinEquiv (finProdFinEquiv.symm m).swap

theorem tr_tr {N : ℕ} (m : Fin (N * N)) : tr (tr m) = m := by
  unfold tr
  rw [Equiv.symm_apply_apply, Prod.swap_swap, Equiv.apply_symm_apply]

theorem transposeWord_apply {N : ℕ} (x : Word (N * N)) (i : Fin (N * N)) :
    transposeWord x i = x (tr i) := rfl

theorem block_eq {N l : ℕ} (hl : l < N * N) : (N * N - 1 - l) / N = N - 1 - l / N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hl
    · exact h
  have hq : l / N < N := (Nat.div_lt_iff_lt_mul hN).mpr hl
  have hs : l % N < N := Nat.mod_lt _ hN
  have hdm := Nat.div_add_mod l N
  generalize l / N = q at hq hdm ⊢
  generalize l % N = r at hs hdm
  have h1 : 1 + l ≤ N * N := by omega
  have e : N * N - 1 - l = (N - 1 - q) * N + (N - 1 - r) := by
    have hN1 : 1 ≤ N := hN
    have h0 : 1 ≤ N * N := by omega
    zify [h0, h1, hN1, show 1 + q ≤ N by omega, show 1 + r ≤ N by omega,
      show l ≤ N * N - 1 by omega, show q ≤ N - 1 by omega, show r ≤ N - 1 by omega]
    have hdz : (N : ℤ) * q + r = l := by exact_mod_cast hdm
    linear_combination hdz
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem tr_div {N : ℕ} (m : Fin (N * N)) : (tr m).val / N = m.val % N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact m.elim0
    · exact h
  have hq : m.val / N < N := (Nat.div_lt_iff_lt_mul hN).mpr m.isLt
  simp only [tr, finProdFinEquiv_apply_val, Prod.fst_swap, Prod.snd_swap,
    finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]
  rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hq, Nat.zero_add]

theorem block_lt {N : ℕ} (m : Fin (N * N)) : block N m < N * N ⌈/⌉ N := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact m.elim0
    · exact h
  rw [ceilDiv_self_mul N hN]
  unfold block
  rw [block_eq m.isLt]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hN Nat.one_pos)

/-- The input block of bit `m`. -/
def blkIn {N : ℕ} (m : Fin (N * N)) : Fin (N * N ⌈/⌉ N) := ⟨block N m, block_lt m⟩
/-- The output block of the transposed position of bit `m`. -/
def blkOut {N : ℕ} (m : Fin (N * N)) : Fin (N * N ⌈/⌉ N) := blkIn (tr m)

theorem blk_injective {N : ℕ} : Function.Injective fun m : Fin (N * N) => (blkOut m, blkIn m) := by
  intro m m' h
  simp only [Prod.mk.injEq, blkOut, blkIn, Fin.mk.injEq, block] at h
  obtain ⟨h1, h2⟩ := h
  rw [block_eq (tr m).isLt, block_eq (tr m').isLt, tr_div, tr_div] at h1
  rw [block_eq m.isLt, block_eq m'.isLt] at h2
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact m.elim0
    · exact h
  have hq : m.val / N < N := (Nat.div_lt_iff_lt_mul hN).mpr m.isLt
  have hq' : m'.val / N < N := (Nat.div_lt_iff_lt_mul hN).mpr m'.isLt
  have hs : m.val % N < N := Nat.mod_lt _ hN
  have hs' : m'.val % N < N := Nat.mod_lt _ hN
  have e1 : m.val / N = m'.val / N := by omega
  have e2 : m.val % N = m'.val % N := by omega
  apply Fin.ext
  rw [← Nat.div_add_mod m.val N, ← Nat.div_add_mod m'.val N, e1, e2]

/-- Positions with the same block are at most `N`. -/
theorem card_block_le {N : ℕ} (t : ℕ) :
    (univ.filter fun i : Fin (N * N) => block N i = t).card ≤ N := by
  have hle : (univ.filter fun i : Fin (N * N) => block N i = t).card ≤ (univ : Finset (Fin N)).card := by
    rcases Nat.eq_zero_or_pos N with h | hN
    · subst h; simp
    apply Finset.card_le_card_of_injOn (fun i => (⟨i.val % N, Nat.mod_lt _ hN⟩ : Fin N))
    · intro i _; simp
    · intro i hi i' hi' h
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi hi'
      simp only [Fin.mk.injEq] at h
      unfold block at hi hi'
      rw [block_eq i.isLt] at hi
      rw [block_eq i'.isLt] at hi'
      have hq : i.val / N < N := (Nat.div_lt_iff_lt_mul hN).mpr i.isLt
      have hq' : i'.val / N < N := (Nat.div_lt_iff_lt_mul hN).mpr i'.isLt
      have e1 : i.val / N = i'.val / N := by omega
      apply Fin.ext
      rw [← Nat.div_add_mod i.val N, ← Nat.div_add_mod i'.val N, e1, h]
  simpa using hle

/-! ## The construction -/

variable {N : ℕ} (G : Network (N * N) N) {K : Type} [Field K]
  (tables : (v : Fin G.vertices) → G.View v → K)

/-- Input end of bit `m`. -/
def uEnd (m : Fin (N * N)) : Fin G.vertices := G.input (blkIn m)
/-- Output end of bit `m`. -/
def vEnd (m : Fin (N * N)) : Fin G.vertices := G.output (blkOut m)

abbrev Pin (j : Fin G.vertices) := G.localBits G.input j → Bool

theorem mem_in (m : Fin (N * N)) : ∃ t, t.val = block N m ∧ G.input t = uEnd G m :=
  ⟨blkIn m, rfl, rfl⟩

theorem vEnd_tr {j : Fin G.vertices} (i : G.localBits G.output j) : j = vEnd G (tr i.val) := by
  obtain ⟨t, ht, hj⟩ := i.property
  have h : vEnd G (tr i.val) = G.output t := by
    unfold vEnd blkOut
    congr 1
    apply Fin.ext
    simp only [blkIn, tr_tr, ht]
  exact hj.symm.trans h.symm

def dec (e : Fin G.edges) : Fin (2 ^ G.width e) ≃ Word (G.width e) :=
  (Fintype.equivOfCardEq (by simp)).symm

abbrev BitNet := wireNetwork (k := K) (uEnd G) (vEnd G) (fun _ : Fin (N * N) => Bool)
abbrev SupNet := wireNetwork (k := K) G.src G.dst (fun e => Fin (2 ^ G.width e))

def edgeWord {j : Fin G.vertices} (yb : (SupNet G (K := K)).Basis j)
    (e : { e // G.src e = j ∨ G.dst e = j }) : Word (G.width e.val) :=
  if h : j = G.src e.val then dec G e.val (yb.1 e.val h)
  else dec G e.val (yb.2 e.val (e.property.resolve_left (fun h' => h h'.symm)).symm)

def outBit {j : Fin G.vertices} (zb : (BitNet G (K := K)).Basis j) (i : G.localBits G.output j) :
    Bool := zb.2 (tr i.val) (vEnd_tr G i)

def maps (j : Fin G.vertices) (q : Pin G j) (zb : (BitNet G (K := K)).Basis j)
    (yb : (SupNet G (K := K)).Basis j) : K :=
  (∏ m : Fin (N * N), if h : j = uEnd G m then
      (if zb.1 m h = q ⟨m, by rw [h]; exact mem_in G m⟩ then 1 else 0) else 1) *
    tables j ⟨fun e => edgeWord G yb e, q, fun i => outBit G zb i⟩

def labels (x : Word (N * N)) (n : ℕ) : Bool := if h : n < N * N then x ⟨n, h⟩ else false

theorem labels_fin (x : Word (N * N)) (m : Fin (N * N)) : labels x m.val = x m := by
  simp [labels, m.isLt]

/-! ## Facts about wire assignments -/

theorem eq_edgeAssignment_iff {J E : Type} {a b : E → J} {I : E → Type}
    (z : (j : J) → ((e : E) → j = a e → I e) × ((e : E) → j = b e → I e)) (val : (e : E) → I e) :
    z = edgeAssignment a b val ↔ (∀ e, (z (a e)).1 e rfl = val e) ∧ (∀ e, (z (b e)).2 e rfl = val e) := by
  constructor
  · rintro rfl; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨h1, h2⟩
    funext j
    apply Prod.ext
    · funext e h; subst h; exact h1 e
    · funext e h; subst h; exact h2 e

theorem prod_dite_single {J : Type} [Fintype J] [DecidableEq J] (u : J) (f : (j : J) → j = u → K) :
    (∏ j, if h : j = u then f j h else 1) = f u rfl := by
  rw [Fintype.prod_eq_single u]
  · simp
  · intro j hj; simp [hj]

/-! ## The display identity -/

theorem half2_eq (z : (j : Fin G.vertices) → (BitNet G (K := K)).Basis j) (m : Fin (N * N))
    {j : Fin G.vertices} (h : j = vEnd G m) : (z j).2 m h = (z (vEnd G m)).2 m rfl := by
  subst h; rfl

theorem half2_congr (z : (j : Fin G.vertices) → (BitNet G (K := K)).Basis j) {m m' : Fin (N * N)}
    (h : m' = m) : (z (vEnd G m')).2 m' rfl = (z (vEnd G m)).2 m rfl := by
  subst h; rfl

theorem ite_one_mul_ite (A B : Prop) [Decidable A] [Decidable B] (c : K) :
    (if A then (1 : K) else 0) * (if B then c else 0) = if A ∧ B then c else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

theorem final_ind {ι : Type} [Fintype ι] (p : ι → Prop) {dp : DecidablePred p} (B : Prop)
    {dB : Decidable B} (Z : Prop) {dZ : Decidable Z} (c : K) (h : Z ↔ (∀ i, p i) ∧ B) :
    (∏ i, if p i then (1 : K) else 0) * (if B then c else 0) = if Z then c else 0 := by
  classical
  rw [Fintype.prod_boole]
  by_cases hZ : Z
  · obtain ⟨h1, h2⟩ := h.mp hZ
    simp [h1, h2, hZ]
  · by_cases h1 : ∀ i, p i
    · have h2 : ¬ B := fun h2 => hZ (h.mpr ⟨h1, h2⟩)
      simp [h1, h2, hZ]
    · simp [h1, hZ]

theorem display (x : Word (N * N)) (c : K)
    (hc : ∀ z, G.contract tables x z = if z = transposeWord x then c else 0) :
    applyLocal (fun j => maps G tables j (fun i => x i.val)) (SupNet G (K := K)).coeff =
      fun z => if z = edgeAssignment (uEnd G) (vEnd G) (fun m => labels x m.val) then c else 0 := by
  funext z
  rw [applyLocal_wireNetwork]
  let zout : Word (N * N) := fun i => (z (vEnd G (tr i))).2 (tr i) rfl
  have hsplit : ∀ y : (e : Fin G.edges) → Fin (2 ^ G.width e),
      (∏ j, maps G tables j (fun i => x i.val) (z j) (edgeAssignment G.src G.dst y j)) =
      (∏ m : Fin (N * N), if (z (uEnd G m)).1 m rfl = x m then (1 : K) else 0) *
        ∏ j, tables j (G.view (x, zout) (fun e => dec G e (y e)) j) := by
    intro y
    simp only [maps, prod_mul_distrib]
    congr 1
    · rw [prod_comm]
      apply prod_congr rfl
      intro m _
      exact prod_dite_single (K := K) (uEnd G m) (fun j h => if (z j).1 m h = x m then (1 : K) else 0)
    · apply prod_congr rfl
      intro j _
      simp only [Network.view]
      congr 1
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · funext e
        show edgeWord (K := K) G (edgeAssignment G.src G.dst y j) e = dec G e.val (y e.val)
        unfold edgeWord
        split_ifs <;> rfl
      · funext i
        exact half2_eq G z (tr i.val) (vEnd_tr G i)
  simp_rw [hsplit]
  rw [← mul_sum]
  have hiff : z = edgeAssignment (uEnd G) (vEnd G) (fun m => labels x m.val) ↔
      (∀ m, (z (uEnd G m)).1 m rfl = x m) ∧ zout = transposeWord x := by
    refine Iff.trans (eq_edgeAssignment_iff (I := fun _ => Bool) z (fun m => labels x m.val)) ?_
    simp only [labels_fin]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, funext fun i => h2 (tr i)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun m => ?_⟩
      have := congrFun h2 (tr m)
      simp only [zout, transposeWord_apply] at this
      exact (half2_congr G z (tr_tr m)).symm.trans (this.trans (congrArg x (tr_tr m)))
  calc _ = (∏ m : Fin (N * N), if (z (uEnd G m)).1 m rfl = x m then (1 : K) else 0) *
        G.contract tables x zout := by
        congr 1
        unfold Network.contract
        convert (Fintype.sum_equiv (Equiv.piCongrRight fun e => dec G e)
          (fun y => ∏ j, tables j (G.view (x, zout) (fun e => dec G e (y e)) j))
          (fun s => ∏ j, tables j (G.view (x, zout) s j)) (fun y => rfl))
    _ = _ := by
        rw [hc zout]
        exact final_ind (K := K) _ _ _ c hiff

/-! ## Labels separate the inputs -/

theorem record_eq_labels {A : Type} (lab : ℕ → A → Bool) (depth : ℕ) (a b : A)
    (equal : labelRecordOf lab depth a = labelRecordOf lab depth b) :
    ∀ i < depth, lab i a = lab i b := by
  induction depth with
  | zero => simp
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · exact ih (congrArg Prod.fst equal) i h
    · exact congrArg Prod.snd equal


/-! ## The entropy bound -/

instance localBitsFintype {n b : ℕ} (H : Network n b) (t : Fin (n ⌈/⌉ b) ↪ Fin H.vertices)
    (v : Fin H.vertices) : Fintype (H.localBits t v) := by
  unfold Network.localBits; infer_instance

theorem card_localBits_le (j : Fin G.vertices) :
    Fintype.card (G.localBits G.input j) ≤ N * (univ.filter fun t => G.input t = j).card := by
  change Fintype.card {i : Fin (N * N) // ∃ t, t.val = block N i ∧ G.input t = j} ≤ _
  rw [Fintype.card_subtype]
  have hsub : (univ.filter fun i : Fin (N * N) => ∃ t, t.val = block N i ∧ G.input t = j) ⊆
      (univ.filter fun t => G.input t = j).biUnion
        (fun t => univ.filter fun i : Fin (N * N) => block N i = t.val) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    obtain ⟨t, ht, hj⟩ := hi
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨t, hj, ht.symm⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ t ∈ univ.filter (fun t => G.input t = j),
        (univ.filter fun i : Fin (N * N) => block N i = t.val).card
      ≤ ∑ _t ∈ univ.filter (fun t => G.input t = j), N := sum_le_sum fun t _ => card_block_le t.val
    _ = N * (univ.filter fun t => G.input t = j).card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem count_input_le_one (j : Fin G.vertices) : (univ.filter fun t => G.input t = j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht t' ht'
  simp only [mem_filter, mem_univ, true_and] at ht ht'
  exact G.input.injective (ht.trans ht'.symm)

theorem sum_count_input : ∑ j : Fin G.vertices, ((univ.filter fun t => G.input t = j).card : ℝ) ≤ N := by
  have h := (Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin (N * N ⌈/⌉ N))))
    (t := (univ : Finset (Fin G.vertices))) (f := fun t => G.input t) (fun _ _ => mem_univ _))
  have hcard : ((univ : Finset (Fin (N * N ⌈/⌉ N))).card : ℝ) ≤ N := by
    rw [card_univ, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0; simp
    · rw [ceilDiv_self_mul N hN]
  calc ∑ j : Fin G.vertices, ((univ.filter fun t => G.input t = j).card : ℝ)
      = ((∑ j : Fin G.vertices, (univ.filter fun t => G.input t = j).card : ℕ) : ℝ) := by push_cast; rfl
    _ = ((univ : Finset (Fin (N * N ⌈/⌉ N))).card : ℝ) := by
        rw [h]
    _ ≤ N := hcard

theorem labels_separate (S : Type) (val : S → Word (N * N)) (inj : Function.Injective val) :
    Function.Injective (labelRecordOf (fun n (x : S) => labels (val x) n) (N * N)) := by
  intro a b h
  apply inj
  funext m
  have := record_eq_labels _ (N * N) a b h m.val m.isLt
  simpa [labels_fin] using this

theorem rate_term (r y : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : r - |y - 1| ≤ r * y := by
  have h2 : r * (1 - y) ≤ |y - 1| := by
    have : r * (1 - y) ≤ r * |y - 1| :=
      mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact le_abs_self _) h0
    have h3 : r * |y - 1| ≤ |y - 1| := mul_le_of_le_one_left (abs_nonneg _) h1
    linarith
  linarith

set_option maxHeartbeats 4000000 in
/-- **The entropy lemma for TRANS, over every field.** -/
theorem transEntropyBound (K : Type) [Field K] : TransEntropyBound K := by
  intro N G tables X _ realizable p root a ha
  -- the pin charges
  let S := {x : Word (N * N) // TransFieldGood G tables x}
  have hcardS : Fintype.card S = (univ.filter (TransFieldGood G tables)).card :=
    Fintype.card_subtype _
  by_cases hne : Nonempty S
  · choose c hc using fun x : S => x.property
    let pin : ∀ j : Fin G.vertices, S → Pin G j := fun j x i => x.val i.val
    let law : FiniteLaw S := FiniteLaw.uniform S
    let labs : ℕ → S → Bool := fun n x => labels x.val n
    have sep := labels_separate S Subtype.val Subtype.val_injective (N := N)
    have bound := paired_entropy_external_root (K := K) realizable p root G.src G.dst G.width (Pin G)
      pin law labs (N * N) sep (uEnd G) (vEnd G) (maps G tables) (fun x => c x)
      (fun x => (hc x).1) (fun x => (display G tables x.val (c x) (hc x).2).trans (funext fun z => by congr 1))
    let h : Fin G.vertices → ℝ := fun j => finiteEntropy ((law.map (pin j)).mass) / Real.log 2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbound_h : ∀ j, 0 ≤ h j ∧ h j ≤ N * (univ.filter fun t => G.input t = j).card := by
      intro j
      refine ⟨div_nonneg (FiniteLaw.entropy_nonneg _) hlog2.le, ?_⟩
      have h1 := FiniteLaw.entropy_le_log_card (law.map (pin j))
      have hc2 : (Fintype.card (Pin G j) : ℝ) = 2 ^ Fintype.card (G.localBits G.input j) := by
        simp [Pin, Fintype.card_fun]
      rw [hc2, Real.log_pow] at h1
      have h2 : (Fintype.card (G.localBits G.input j) : ℝ) ≤
          N * (univ.filter fun t => G.input t = j).card := by exact_mod_cast card_localBits_le G j
      show finiteEntropy ((law.map (pin j)).mass) / Real.log 2 ≤ _
      rw [div_le_iff₀ hlog2]
      nlinarith
    refine ⟨h, fun j => ⟨(hbound_h j).1, ?_⟩, ?_, ?_⟩
    · have := (hbound_h j).2
      have hc1 : ((univ.filter fun t => G.input t = j).card : ℝ) ≤ 1 := by
        exact_mod_cast count_input_le_one G j
      have : (N : ℝ) * (univ.filter fun t => G.input t = j).card ≤ N * 1 :=
        mul_le_mul_of_nonneg_left hc1 (Nat.cast_nonneg N)
      linarith
    · calc ∑ v, h v ≤ ∑ v : Fin G.vertices, (N : ℝ) * (univ.filter fun t => G.input t = v).card :=
            sum_le_sum fun v _ => (hbound_h v).2
        _ = N * ∑ v : Fin G.vertices, ((univ.filter fun t => G.input t = v).card : ℝ) := by
            rw [mul_sum]
        _ ≤ N * N := mul_le_mul_of_nonneg_left (sum_count_input G) (Nat.cast_nonneg N)
    · -- rates
      let R : Fin (N * N) → ℝ := fun l =>
        (FiniteLabelHierarchy.ofLawLabels law labs (N * N)).refinementEntropy l / Real.log 2
      have hR : ∀ l, 0 ≤ R l ∧ R l ≤ 1 := fun l => bitRate_range law labs (N * N) l
      have hsumR : ∑ l, R l = Real.logb 2 (Fintype.card S) := by
        simp only [R, ← sum_div, Real.logb]
        rw [Fin.sum_univ_eq_sum_range
          (fun i => (FiniteLabelHierarchy.ofLawLabels law labs (N * N)).refinementEntropy i),
          FiniteLabelHierarchy.ofLawLabels_refinementEntropy_sum _ _ _ sep, FiniteLaw.uniform_entropy]
      rw [← hcardS, ← hsumR]
      have scaled := mul_le_mul_of_nonneg_left bound ha
      -- lower bound of the left side
      have hlow : ∑ l, R l - ∑ l : Fin (N * N), |a * dist (p (uEnd G l)) (p (vEnd G l)) - 1| ≤
          a * ∑ l, R l * dist (p (uEnd G l)) (p (vEnd G l)) := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_le_sum
        intro l _
        have := rate_term (R l) (a * dist (p (uEnd G l)) (p (vEnd G l))) (hR l).1 (hR l).2
        linarith [show a * (R l * dist (p (uEnd G l)) (p (vEnd G l))) =
          R l * (a * dist (p (uEnd G l)) (p (vEnd G l))) by ring]
      -- the bit pairs are distinct block pairs
      have hpairs : ∑ l : Fin (N * N), |a * dist (p (uEnd G l)) (p (vEnd G l)) - 1| ≤
          ∑ j, ∑ i, |a * dist (p (G.input i)) (p (G.output j)) - 1| := by
        let f : Fin (N * N ⌈/⌉ N) × Fin (N * N ⌈/⌉ N) → ℝ := fun q =>
          |a * dist (p (G.input q.2)) (p (G.output q.1)) - 1|
        have e1 : ∑ l : Fin (N * N), |a * dist (p (uEnd G l)) (p (vEnd G l)) - 1| =
            ∑ q ∈ univ.image (fun m : Fin (N * N) => (blkOut m, blkIn m)), f q := by
          rw [sum_image (fun m _ m' _ h => blk_injective h)]
          rfl
        rw [e1, ← Fintype.sum_prod_type']
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun q _ _ => abs_nonneg _)
      have hrhs : a * (∑ e, (G.width e : ℝ) * dist (p (G.src e)) (p (G.dst e)) +
          ∑ j, finiteEntropy ((law.map (pin j)).mass) / Real.log 2 * dist root (p j)) =
          ∑ e, (G.width e : ℝ) * (a * dist (p (G.src e)) (p (G.dst e))) +
            ∑ v, h v * (a * dist (p v) root) := by
        rw [mul_add, mul_sum, mul_sum]
        congr 1
        · apply sum_congr rfl; intro e _; ring
        · apply sum_congr rfl; intro v _; rw [dist_comm]; ring
      have hleft : a * ∑ l, R l * dist (p (uEnd G l)) (p (vEnd G l)) ≤
          ∑ e, (G.width e : ℝ) * (a * dist (p (G.src e)) (p (G.dst e))) +
            ∑ v, h v * (a * dist (p v) root) := by
        rw [← hrhs]; exact scaled
      linarith
  · -- no good input: the left side is at most 0
    refine ⟨fun _ => 0, fun _ => ⟨le_refl _, Nat.cast_nonneg _⟩, by simp; positivity, ?_⟩
    have h0 : (univ.filter (TransFieldGood G tables)).card = 0 := by
      rw [← hcardS]; exact Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hne)
    rw [h0, Nat.cast_zero, Real.logb_zero, zero_sub]
    have h1 : 0 ≤ ∑ j, ∑ i, |a * dist (p (G.input i)) (p (G.output j)) - 1| :=
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 ≤ ∑ e, (G.width e : ℝ) * (a * dist (p (G.src e)) (p (G.dst e))) :=
      sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha dist_nonneg)
    simp only [zero_mul, sum_const_zero, add_zero]
    linarith

end

end P1Case1.Entropy
