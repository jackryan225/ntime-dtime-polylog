import P1Hier.Defs
import P1Hier.Spec

/-!
# P1Hier.Hierarchy: the parity hierarchy W2 (diagonal half proved, universal half open)

For `q ≥ 1` the diagonal language `D q` is: parse a machine code `c` from a prefix of `x`
(prefix-free bit code `serCode`); if `(|serCode c| + 1)² ≤ rootLog q |x|` (the guard), then
`D q x = !(odd number of guesses w ∈ {0,1}^(G q |x|) such that a valid transcript of an accepting run
of c on withGuess w x within Tb c |x| = |x|² / (|serCode c|+1)² steps exists)`; otherwise false.

* `diagonal` (PROVED): no machine parity-decides `D q` with guess length `G q n` and time `c·G q n`
  (plus the input length), for any `c`, `n₀`.
* `universal_verifier_of` (PROVED from the machine statement `AccUMachine q`; that statement, and
  `universal_verifier`, `parity_hierarchy` with no hypothesis, are in `P1Hier/W2.lean`): one machine `U` parity-decides `D q` with guess length
  `a(n²+1)` and time `b(n²+1)` (plus the input length). Construction: guess = (special bit, w,
  bit code of τ, forced zeros); the special guess `1 0…0` accepts iff the guard holds; otherwise
  U runs the W1 checker on (c, withGuess w x, Tb, τ). By `check_iff` exactly one τ per accepting
  run, so #accepting guesses = #{w : V accepts} + 1.

Two constants `a`, `b` (not one): see board 1362 and the message to G3-chief of 09:06Z.
-/

namespace P1Hier

open C1Challenge

/-! ## Halting is deterministic and monotone -/

theorem iter_after_halt (M : Machine) (c : Cfg M.K M.Γ M.Q) (h : M.step c = none) (k : ℕ) :
    (fun oc => Option.bind oc M.step)^[k + 1] (some c) = none := by
  rw [Function.iterate_succ_apply]
  simp [h, iterate_none]

theorem halts_det (M : Machine) (y : List Bool) {b b' : Bool} {T T' : ℕ}
    (h : HaltsWithin M y b T) (h' : HaltsWithin M y b' T') : b = b' := by
  obtain ⟨t, -, c, hc, hs, rfl⟩ := h
  obtain ⟨t', -, c', hc', hs', rfl⟩ := h'
  have key : ∀ {t t' : ℕ} {c c' : Cfg M.K M.Γ M.Q}, t ≤ t' →
      (fun oc => Option.bind oc M.step)^[t] (some (M.init y)) = some c → M.step c = none →
      (fun oc => Option.bind oc M.step)^[t'] (some (M.init y)) = some c' → c = c' := by
    intro t t' c c' hle hc hs hc'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rcases k with _ | k
    · rw [Nat.add_zero, hc] at hc'
      exact Option.some.inj hc'
    · rw [add_comm t, Function.iterate_add_apply, hc, iter_after_halt M c hs] at hc'
      cases hc'
  rcases le_total t t' with hle | hle
  · rw [key hle hc hs hc']
  · rw [key hle hc' hs' hc]

theorem halts_mono (M : Machine) (y : List Bool) {b : Bool} {T T' : ℕ}
    (h : HaltsWithin M y b T) (hT : T ≤ T') : HaltsWithin M y b T' := by
  obtain ⟨t, ht, c, hc, hs, hb⟩ := h
  exact ⟨t, ht.trans hT, c, hc, hs, hb⟩

theorem length_withGuess (w x : List Bool) :
    (withGuess w x).length = 2 * w.length + 1 + x.length := by
  induction w with
  | nil => simp [withGuess]; omega
  | cons b w ih =>
    simp only [withGuess, List.flatMap_cons, List.append_assoc, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

/-- Valid transcripts exist iff the machine accepts in time. -/
theorem exists_check_iff (M : Machine) (y : List Bool) (T : ℕ) :
    (∃ τ, Check (code M) y T τ) ↔ HaltsWithin M y true T := by
  constructor
  · rintro ⟨τ, h⟩; exact ((check_iff M y T τ).1 h).2
  · intro h; exact ⟨transcript M y T, (check_iff M y T _).2 ⟨rfl, h⟩⟩

/-! ## A prefix-free bit code of machine codes -/

/-- `f` is injective and prefix-free: `f a ++ r` has a unique parse. -/
def PF {α : Type*} (f : α → List Bool) : Prop :=
  ∀ a a' r r', f a ++ r = f a' ++ r' → a = a' ∧ r = r'

/-- Unary numbers. -/
def serN (k : ℕ) : List Bool := List.replicate k true ++ [false]

theorem serN_succ (k : ℕ) : serN (k + 1) = true :: serN k := by
  simp [serN, List.replicate_succ]

theorem pf_serN : PF serN := by
  intro a
  induction a with
  | zero =>
    intro a' r r' h
    cases a' with
    | zero => simpa [serN] using h
    | succ a' => simp [serN, List.replicate_succ] at h
  | succ a ih =>
    intro a' r r' h
    cases a' with
    | zero => simp [serN, List.replicate_succ] at h
    | succ a' =>
      rw [serN_succ, serN_succ, List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih a' r r' h.2
      exact ⟨by rw [h1], h2⟩

theorem pf_append {α β : Type*} {f : α → List Bool} {g : β → List Bool} (hf : PF f) (hg : PF g) :
    PF (fun p : α × β => f p.1 ++ g p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ r r' h
  simp only [List.append_assoc] at h
  obtain ⟨rfl, h2⟩ := hf a a' _ _ h
  obtain ⟨rfl, h3⟩ := hg b b' _ _ h2
  exact ⟨rfl, h3⟩

/-- Lists: each item is announced by `true`, the end by `false`. -/
def serL {α : Type*} (f : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (fun a => true :: f a) ++ [false]

theorem serL_nil {α : Type*} (f : α → List Bool) : serL f [] = [false] := rfl

theorem serL_cons {α : Type*} (f : α → List Bool) (a : α) (l : List α) :
    serL f (a :: l) = true :: (f a ++ serL f l) := by
  simp [serL, List.flatMap_cons, List.append_assoc]

theorem pf_serL {α : Type*} {f : α → List Bool} (hf : PF f) : PF (serL f) := by
  intro l
  induction l with
  | nil =>
    intro l' r r' h
    cases l' with
    | nil => simpa [serL_nil] using h
    | cons a' l' => simp [serL_nil, serL_cons] at h
  | cons a l ih =>
    intro l' r r' h
    cases l' with
    | nil => simp [serL_nil, serL_cons] at h
    | cons a' l' =>
      rw [serL_cons, serL_cons, List.cons_append, List.cons_append, List.cons.injEq,
        List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := hf a a' _ _ h.2
      obtain ⟨rfl, h3⟩ := ih l' r r' h2
      exact ⟨rfl, h3⟩

def serMv : Mv → List Bool
  | none => [false]
  | some b => [true, b]

theorem pf_serMv : PF serMv := by
  intro a a' r r' h
  cases a with
  | none => cases a' with
    | none => simpa [serMv] using h
    | some b' => simp [serMv] at h
  | some b => cases a' with
    | none => simp [serMv] at h
    | some b' =>
      simp only [serMv, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨by rw [h.1], h.2⟩

def serRes : ℕ ⊕ Bool → List Bool
  | Sum.inl q => false :: serN q
  | Sum.inr b => [true, b]

theorem pf_serRes : PF serRes := by
  intro a a' r r' h
  cases a with
  | inl q => cases a' with
    | inl q' =>
      simp only [serRes, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h2⟩ := pf_serN q q' r r' h
      exact ⟨rfl, h2⟩
    | inr b' => simp [serRes] at h
  | inr b => cases a' with
    | inl q' => simp [serRes] at h
    | inr b' =>
      simp only [serRes, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨by rw [h.1], h.2⟩

def serCell (x : Cell) : List Bool := serN x.1 ++ (serN x.2.1 ++ serMv x.2.2)

theorem pf_serCell : PF serCell :=
  pf_append pf_serN (pf_append pf_serN pf_serMv)

def serEntry (e : Entry) : List Bool := serN e.1 ++ (serL serCell e.2.1 ++ serRes e.2.2)

theorem pf_serEntry : PF serEntry :=
  pf_append pf_serN (pf_append (pf_serL pf_serCell) pf_serRes)

/-- The bit code of a machine code. -/
def serCode (c : MCode) : List Bool :=
  serN c.nK ++ (serN c.inp ++ (serN c.sym0 ++ (serN c.sym1 ++ (serN c.init ++
    serL serEntry c.table))))

theorem pf_serCode : PF serCode := by
  intro a a' r r' h
  have hp := pf_append pf_serN (pf_append pf_serN (pf_append pf_serN (pf_append pf_serN
    (pf_append pf_serN (pf_serL pf_serEntry)))))
  obtain ⟨he, hr⟩ := hp (a.nK, a.inp, a.sym0, a.sym1, a.init, a.table)
    (a'.nK, a'.inp, a'.sym0, a'.sym1, a'.init, a'.table) r r' h
  refine ⟨?_, hr⟩
  rcases a with ⟨_, _, _, _, _, _⟩
  rcases a' with ⟨_, _, _, _, _, _⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
  rfl

open Classical in
/-- Parse a machine code from a prefix of `x`. -/
noncomputable def px (x : List Bool) : Option MCode :=
  if h : ∃ c r, x = serCode c ++ r then some (Classical.choose h) else none

theorem px_serCode (c : MCode) (r : List Bool) : px (serCode c ++ r) = some c := by
  have h : ∃ c' r', serCode c ++ r = serCode c' ++ r' := ⟨c, r, rfl⟩
  rw [px, dite_cond_eq_true (eq_true h)]
  obtain ⟨r', hr'⟩ := Classical.choose_spec h
  exact congrArg some (pf_serCode _ _ _ _ hr').1.symm

/-! ## The diagonal language -/

/-- Size of a code, as seen by the universal machine. -/
def csz (c : MCode) : ℕ := (serCode c).length

/-- Simulation budget for code `c` on inputs of length `n`. -/
def Tb (c : MCode) (n : ℕ) : ℕ := n ^ 2 / (csz c + 1) ^ 2

/-- The universal machine simulates code `c` only when it is small against `rootLog q n`. -/
def guard (q : ℕ) (c : MCode) (n : ℕ) : Prop := (csz c + 1) ^ 2 ≤ rootLog q n

/-- Guess length of the universal verifier. -/
def gU (n : ℕ) : ℕ := 4 * (n ^ 2 + 1)

/-- Bits of a transcript. -/
def serT (τ : List Entry) : List Bool := serL serEntry τ

/-- What the universal verifier accepts on input `x` with guess `u`: a parsable code `c` passing
the guard, and either the special guess `1 0 … 0`, or `0 w (bits of τ) 0 … 0` with `|w| = G q n`
and `τ` a valid transcript for `c` on `withGuess w x` within the budget. -/
def accU (q : ℕ) (x u : List Bool) : Prop :=
  ∃ c, px x = some c ∧ guard q c x.length ∧
    (u = true :: List.replicate (gU x.length - 1) false ∨
     ∃ (w : List Bool) (τ : List Entry) (z : List Bool), w.length = G q x.length ∧
       (∀ b ∈ z, b = false) ∧ u = false :: (w ++ serT τ ++ z) ∧
       Check c (withGuess w x) (Tb c x.length) τ)

open Classical in
/-- The diagonal language of the parity hierarchy: the parity of the number of guesses of length
`gU |x|` that the universal verifier accepts. -/
noncomputable def D (q : ℕ) (x : List Bool) : Bool :=
  decide (Odd (Finset.univ.filter fun u : Fin (gU x.length) → Bool =>
    accU q x (List.ofFn u)).card)

/-! ## Counting the accepted guesses for a genuine machine code -/

theorem ofFn_getD (l : List Bool) (m : ℕ) (h : l.length ≤ m) :
    List.ofFn (fun i : Fin m => l.getD i false) = l ++ List.replicate (m - l.length) false := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    by_cases hi : i < l.length
    · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]
    · rw [List.getElem_append_right (by omega), List.getElem_replicate,
        List.getD_eq_default _ _ (by omega)]

theorem length_lt_serL {α : Type*} (f : α → List Bool) (l : List α) (a : α) (ha : a ∈ l) :
    (f a).length < (serL f l).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rw [serL_cons, List.length_cons, List.length_append]
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · have := ih ha; omega

theorem length_serL_le {α : Type*} (f : α → List Bool) (l : List α) (K : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ K) : (serL f l).length ≤ l.length * (K + 1) + 1 := by
  induction l with
  | nil => simp [serL_nil]
  | cons b l ih =>
    rw [serL_cons, List.length_cons, List.length_append, List.length_cons]
    have h1 := h b (by simp)
    have h2 := ih (fun a ha => h a (by simp [ha]))
    nlinarith

theorem length_serEntry_le (c : MCode) (e : Entry) (he : e ∈ c.table) :
    (serEntry e).length ≤ csz c := by
  have := length_lt_serL serEntry c.table e he
  simp only [csz, serCode, List.length_append] at this ⊢
  omega

/-- A valid transcript of a code fits into the guess of the universal verifier. -/
theorem fit (q : ℕ) (c : MCode) (n : ℕ) (hg : guard q c n) (y : List Bool) (τ : List Entry)
    (hτ : Check c y (Tb c n) τ) : 1 + G q n + (serT τ).length ≤ gU n := by
  obtain ⟨hlen, htab, -, -⟩ := hτ
  have h1 : (serT τ).length ≤ τ.length * (csz c + 1) + 1 :=
    length_serL_le serEntry τ (csz c) (fun e he => length_serEntry_le c e (htab e he))
  have h2 : τ.length * (csz c + 1) ≤ (Tb c n + 1) * (csz c + 1) := Nat.mul_le_mul_right _ hlen
  have h3 : Tb c n * (csz c + 1) ^ 2 ≤ n ^ 2 := Nat.div_mul_le_self _ _
  have h4 : Tb c n * (csz c + 1) ≤ Tb c n * (csz c + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have h5 : G q n ≤ n ^ 2 := Nat.div_le_self _ _
  have h6 : (csz c + 1) ^ 2 ≤ n + 1 :=
    hg.trans ((rootLog_le q n).trans (by have := Nat.log_le_self 2 n; omega))
  have h7 : csz c + 1 ≤ (csz c + 1) ^ 2 := by nlinarith
  unfold gU
  nlinarith

open Classical in
/-- For a genuine machine code that passes the guard, the universal verifier accepts exactly one
guess more than there are accepting runs of the machine (the special guess). -/
theorem count_accU (q : ℕ) (V : Machine) (x : List Bool) (hpx : px x = some (code V))
    (hg : guard q (code V) x.length) :
    (Finset.univ.filter fun u : Fin (gU x.length) → Bool => accU q x (List.ofFn u)).card =
      (Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true (Tb (code V) x.length)).card + 1 := by
  let enc : (Fin (G q x.length) → Bool) → List Bool := fun w =>
    false :: (List.ofFn w ++ serT (transcript V (withGuess (List.ofFn w) x) (Tb (code V) x.length)))
  let φ : (Fin (G q x.length) → Bool) → (Fin (gU x.length) → Bool) := fun w i => (enc w).getD i false
  let sp : Fin (gU x.length) → Bool := fun i => [true].getD i false
  have hGg : G q x.length + 1 < gU x.length := by
    have : G q x.length ≤ x.length ^ 2 := Nat.div_le_self _ _
    unfold gU; omega
  have hsp : List.ofFn sp = true :: List.replicate (gU x.length - 1) false := by
    rw [ofFn_getD [true] (gU x.length) (by simp; omega)]; rfl
  -- accepted runs give accepted guesses
  have hfit : ∀ w : Fin (G q x.length) → Bool,
      HaltsWithin V (withGuess (List.ofFn w) x) true (Tb (code V) x.length) → (enc w).length ≤ gU x.length := by
    intro w hw
    have hc := (check_iff V (withGuess (List.ofFn w) x) (Tb (code V) x.length) _).2 ⟨rfl, hw⟩
    have := fit q (code V) x.length hg _ _ hc
    simp only [enc, List.length_cons, List.length_append, List.length_ofFn]
    omega
  have hφ : ∀ w : Fin (G q x.length) → Bool, HaltsWithin V (withGuess (List.ofFn w) x) true (Tb (code V) x.length) →
      List.ofFn (φ w) = enc w ++ List.replicate (gU x.length - (enc w).length) false :=
    fun w hw => ofFn_getD _ _ (hfit w hw)
  have hφi : ∀ w : Fin (G q x.length) → Bool, ∀ i : Fin (G q x.length),
      φ w ⟨i.val + 1, by omega⟩ = w i := by
    intro w i
    simp only [φ, enc, List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  have hinj : Function.Injective φ := by
    intro w w' h
    funext i
    rw [← hφi w i, ← hφi w' i, h]
  have hφ0 : ∀ w, φ w ⟨0, by omega⟩ = false := fun w => rfl
  have hsp0 : sp ⟨0, by omega⟩ = true := rfl
  have hnot : sp ∉ (Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
      HaltsWithin V (withGuess (List.ofFn w) x) true (Tb (code V) x.length)).image φ := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro w _ h
    have := congrFun h ⟨0, by omega⟩
    rw [hφ0, hsp0] at this
    cases this
  have hset : (Finset.univ.filter fun u : Fin (gU x.length) → Bool => accU q x (List.ofFn u)) =
      insert sp ((Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true (Tb (code V) x.length)).image φ) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, -, h | ⟨w', τ, z, hw', hz, hu, hch⟩⟩
      · left
        apply List.ofFn_injective
        rw [hsp, h]
      · right
        rw [hpx] at hc
        cases hc
        let w : Fin (G q x.length) → Bool := fun i => w'[i.val]'(by omega)
        have hww : List.ofFn w = w' := by
          apply List.ext_getElem <;> simp [w, hw']
        rw [← hww] at hch hu
        have hcheck := (check_iff V _ _ τ).1 hch
        refine ⟨w, hcheck.2, ?_⟩
        have hτ : transcript V (withGuess (List.ofFn w) x) (Tb (code V) x.length) = τ :=
          hcheck.1.symm
        have hlen := congrArg List.length hu
        simp only [List.length_ofFn, List.length_cons, List.length_append] at hlen
        have hz' : z = List.replicate (gU x.length - (enc w).length) false := by
          rw [List.eq_replicate_iff]
          refine ⟨?_, hz⟩
          simp only [enc, hτ, List.length_cons, List.length_append, List.length_ofFn]
          omega
        apply List.ofFn_injective
        rw [hφ w hcheck.2, hu, hz']
        simp only [enc, hτ, List.cons_append, List.append_assoc]
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact ⟨code V, hpx, hg, Or.inl hsp⟩
      · refine ⟨code V, hpx, hg, Or.inr ⟨List.ofFn w,
          transcript V (withGuess (List.ofFn w) x) (Tb (code V) x.length),
          List.replicate (gU x.length - (enc w).length) false, by simp, ?_, ?_, ?_⟩⟩
        · intro b hb; exact (List.eq_of_mem_replicate hb)
        · rw [hφ w hw]; simp [enc]
        · exact (check_iff V _ _ _).2 ⟨rfl, hw⟩
  rw [hset, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]

/-! ## Arithmetic: the budget beats `c · G q n` eventually -/

theorem rootLog_ge (q B n : ℕ) (hn : 2 ^ (B ^ (max q 1)) ≤ n) : B ≤ rootLog q n := by
  by_contra hlt
  rw [not_le] at hlt
  have hq : max q 1 ≠ 0 := by have := le_max_right q 1; omega
  have h1 : rootLog q n ^ (max q 1) < B ^ (max q 1) := Nat.pow_lt_pow_left hlt hq
  have h2 := rootLog_spec q n
  have h3 : B ^ (max q 1) ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  omega

theorem budget_eventually (q c S : ℕ) (hS : 1 ≤ S) : ∃ N, ∀ n, N ≤ n →
    S ≤ rootLog q n ∧ (c * (n ^ 2 / rootLog q n) + (2 * (n ^ 2 / rootLog q n) + 1 + n)) * S ≤ n ^ 2 := by
  refine ⟨2 ^ ((2 * (c + 2) * S) ^ (max q 1)) + 4 * S, fun n hn => ?_⟩
  have hR : 2 * (c + 2) * S ≤ rootLog q n := rootLog_ge q _ n (le_trans (Nat.le_add_right _ _) hn)
  refine ⟨by nlinarith, ?_⟩
  set R := rootLog q n
  set g := n ^ 2 / R
  have hgR : g * R ≤ n ^ 2 := Nat.div_mul_le_self _ _
  have h1 : g * (2 * (c + 2) * S) ≤ n ^ 2 := le_trans (Nat.mul_le_mul_left g hR) hgR
  have hn4 : 4 * S ≤ n := le_trans (Nat.le_add_left _ _) hn
  have h2 : 2 * ((1 + n) * S) ≤ n ^ 2 := by nlinarith
  nlinarith

/-! ## The diagonal theorem -/

open Classical in
theorem diagonal (q : ℕ) (V : Machine) (c n₀ : ℕ) :
    ¬ ParDecidesFrom V (D q) (G q) (fun n => c * G q n) n₀ := by
  intro hV
  set cd := code V
  set S := (csz cd + 1) ^ 2 with hSdef
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (Nat.succ_pos _)
  obtain ⟨N, hN⟩ := budget_eventually q c S hS
  set x := serCode cd ++ List.replicate (max n₀ N) false with hx
  have hxlen : x.length = csz cd + max n₀ N := by rw [hx]; simp [csz]
  obtain ⟨hguard, hbud⟩ := hN x.length (by omega)
  obtain ⟨h1, h2⟩ := hV x (by omega)
  have hpx : px x = some cd := by rw [hx]; exact px_serCode _ _
  have hg : guard q cd x.length := by unfold guard; rw [← hSdef]; exact hguard
  -- within the budget, acceptance does not depend on the time bound
  have hset : (Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true (Tb cd x.length)) =
      (Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true
          (c * G q x.length + (withGuess (List.ofFn w) x).length)) := by
    apply Finset.filter_congr
    intro w _
    have hle : c * G q x.length + (withGuess (List.ofFn w) x).length ≤
        Tb cd x.length := by
      rw [length_withGuess, List.length_ofFn, Tb, Nat.le_div_iff_mul_le (by positivity), ← hSdef]
      exact hbud
    constructor
    · intro h
      obtain ⟨b, hb⟩ := h1 w
      have : b = true := halts_det V _ hb h
      rw [this] at hb
      exact hb
    · intro h
      exact halts_mono V _ h hle
  have hD : D q x = decide (Odd ((Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true (Tb cd x.length)).card + 1)) := by
    rw [D, count_accU q V x hpx hg]
  rw [hD, hset] at h2
  set N' := (Finset.univ.filter fun w : Fin (G q x.length) → Bool =>
        HaltsWithin V (withGuess (List.ofFn w) x) true
          (c * G q x.length + (withGuess (List.ofFn w) x).length)).card
  rw [decide_eq_true_iff, Nat.odd_add_one] at h2
  exact iff_not_self h2.symm

/-! ## The universal half (from the machine statement) and W2 -/

open Classical in
/-- The machine statement: one machine decides `accU q` on `withGuess u x` for all guesses of length
`gU |x|`, within time `b(|x|²+1)` plus the input length. PROVED in `P1Hier/W2.lean` from lane hierB's
`UM.accU_machine_of3` (code parser, transcript parser) and the W1 checker `check_task_of_phases`. -/
def AccUMachine (q : ℕ) : Prop := ∃ (U : Machine) (b : ℕ), ∀ (x : List Bool)
    (u : Fin (gU x.length) → Bool),
    HaltsWithin U (withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
      (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length)

open Classical in
theorem universal_verifier_of (q : ℕ) (hm : AccUMachine q) : ∃ (U : Machine) (a b : ℕ),
    ParDecidesFrom U (D q) (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0 := by
  obtain ⟨U, b, hU⟩ := hm
  refine ⟨U, 4, b, fun x _ => ⟨fun u => ⟨_, hU x u⟩, ?_⟩⟩
  rw [D, decide_eq_true_iff]
  have : (Finset.univ.filter fun u : Fin (4 * (x.length ^ 2 + 1)) → Bool =>
        HaltsWithin U (withGuess (List.ofFn u) x) true
          (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length)) =
      (Finset.univ.filter fun u : Fin (gU x.length) → Bool => accU q x (List.ofFn u)) := by
    apply Finset.filter_congr
    intro u _
    constructor
    · intro h
      have := halts_det U _ h (hU x u)
      exact of_decide_eq_true this.symm
    · intro h
      have := hU x u
      rwa [decide_eq_true h] at this
  rw [this]
  rfl

/-- **W2** (two-constant form, see the module doc), from the machine statement. The final theorem
`P1Hier.parity_hierarchy` (no hypothesis) is in `P1Hier/W2.lean`. -/
theorem parity_hierarchy_of (q : ℕ) (hm : AccUMachine q) : ∃ D : List Bool → Bool,
    (∃ (U : Machine) (a b : ℕ),
      ParDecidesFrom U D (fun n => a * (n ^ 2 + 1)) (fun n => b * (n ^ 2 + 1)) 0) ∧
    ∀ (V : Machine) (c n₀ : ℕ), ¬ ParDecidesFrom V D (G q) (fun n => c * G q n) n₀ :=
  ⟨D q, universal_verifier_of q hm, diagonal q⟩

end P1Hier
