import P1Wrap.MachineGlue
import P1Wrap.W3Support
import P1Hier.Spec

/-!
# The outer verifier `V*` at the functional level: the parity bookkeeping of W3

`outerVerdict M j a b w x` is what `V*` computes on the guess `w` and the input `x` (`n = |x|`, `m = m(n)`):
`u` = the first `m` bits of `w`; the rest of `w` must be `encT τ ++ 0^r` for a list `τ` of rows of the table of the
flipped machine `flipM M` (row `e` written as `1^(idx e + 1) 0`); and the W1 check `P1Hier.Check` must accept `τ`
as a transcript of `flipM M` on `padIn x u` within `|w|` steps.

`outer_count` (the bookkeeping, risk 4 of PLAN.md sec. 7): if `M` decides `L` within `Tb |y|` steps and the guess
length `g` leaves room `m + (|table| + 1) (Tb ν + 1) ≤ g`, then the guesses `w ∈ {0,1}^g` with `outerVerdict = true`
are exactly as many as the `u ∈ {0,1}^m` with `L (padIn x u) = false`: each such `u` has exactly one valid layout
(the transcript is unique by `P1Hier.check_iff`, the padding is forced to zeros), every other `u` has none.

`outerProg_of_impl`: `OuterProg` follows from `OuterImpl` (a stack program computes `outerVerdict` in time
`C (|w| + ν + 1) + |input|`), which is now a pure implementation task (W1 checker of lane hier + parsing + the
arithmetic of `m(n)`).
-/

namespace P1Wrap.W3

open P1Int C1Challenge OAI.Computability.IntegerMultiplication

noncomputable section

/-! ## Flipping the answer of a machine -/

/-- `M` with the answer flipped. -/
def flipM (M : Machine) : Machine := { M with accept := fun q => !M.accept q }

theorem haltsWithin_flipM {M : Machine} {y : List Bool} {v : Bool} {T : ℕ} :
    HaltsWithin (flipM M) y v T ↔ HaltsWithin M y (!v) T := by
  constructor
  · rintro ⟨t, ht, c, h1, h2, h3⟩
    refine ⟨t, ht, c, h1, h2, ?_⟩
    change (!M.accept c.q) = v at h3
    rw [← h3, Bool.not_not]
  · rintro ⟨t, ht, c, h1, h2, h3⟩
    refine ⟨t, ht, c, h1, h2, ?_⟩
    change (!M.accept c.q) = v
    rw [h3, Bool.not_not]

/-! ## Transcript layout in the guess -/

/-- Equality test on rows by decidable equality (so that `List.idxOf` has the lawful `BEq`). -/
instance (priority := high) entryDecEq : DecidableEq P1Hier.Entry := Classical.decEq _
instance (priority := high) entryBEq : BEq P1Hier.Entry := instBEqOfDecidableEq
instance (priority := high) entryLawful : LawfulBEq P1Hier.Entry := inferInstance

/-- Row `e` of `τ` written as `1^(idx e + 1) 0`, where `idx e` is its position in the table `tbl`. -/
def encT (tbl : List P1Hier.Entry) (τ : List P1Hier.Entry) : List Bool :=
  τ.flatMap fun e => List.replicate (tbl.idxOf e + 1) true ++ [false]

theorem encT_nil (tbl : List P1Hier.Entry) : encT tbl [] = [] := rfl

theorem encT_cons (tbl : List P1Hier.Entry) (e : P1Hier.Entry) (τ : List P1Hier.Entry) :
    encT tbl (e :: τ) = List.replicate (tbl.idxOf e + 1) true ++ false :: encT tbl τ := by
  simp [encT, List.flatMap_cons]

theorem length_encT_le (tbl : List P1Hier.Entry) :
    ∀ τ : List P1Hier.Entry, (∀ e ∈ τ, e ∈ tbl) → (encT tbl τ).length ≤ τ.length * (tbl.length + 1)
  | [], _ => by simp [encT_nil]
  | e :: τ, h => by
      have h1 : tbl.idxOf e < tbl.length := List.idxOf_lt_length_of_mem (h e (by simp))
      have h2 := length_encT_le tbl τ (fun e' he' => h e' (by simp [he']))
      rw [encT_cons]
      simp only [List.length_append, List.length_replicate, List.length_cons]
      nlinarith

theorem encT_pad_inj {tbl : List P1Hier.Entry} :
    ∀ (τ τ' : List P1Hier.Entry) (r r' : ℕ), (∀ e ∈ τ, e ∈ tbl) → (∀ e ∈ τ', e ∈ tbl) →
      encT tbl τ ++ List.replicate r false = encT tbl τ' ++ List.replicate r' false → τ = τ'
  | [], [], _, _, _, _, _ => rfl
  | [], e :: τ', r, r', _, _, h => by
      exfalso
      rw [encT_nil, encT_cons] at h
      cases r with
      | zero => simp [List.replicate_succ] at h
      | succ r => simp [List.replicate_succ] at h
  | e :: τ, [], r, r', _, _, h => by
      exfalso
      rw [encT_nil, encT_cons] at h
      cases r' with
      | zero => simp [List.replicate_succ] at h
      | succ r' => simp [List.replicate_succ] at h
  | e :: τ, e' :: τ', r, r', h1, h2, h => by
      rw [encT_cons, encT_cons, List.append_assoc, List.append_assoc, List.cons_append,
        List.cons_append] at h
      obtain ⟨hi, hrest⟩ := replicate_true_cons_false_inj _ _ _ _ h
      have he : e = e' := by
        have m1 : e ∈ tbl := h1 e (by simp)
        have m2 : e' ∈ tbl := h2 e' (by simp)
        have g1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem m1)
        have g2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem m2)
        have hi' : tbl.idxOf e = tbl.idxOf e' := by omega
        rw [← g1, ← g2]
        simp only [hi']
      have ht := encT_pad_inj τ τ' r r' (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) hrest
      rw [he, ht]

/-! ## Transcript length -/

theorem length_rowsFrom_le (M : Machine) : ∀ (t : ℕ) (c c' : Cfg M.K M.Γ M.Q) (n : ℕ),
    (fun oc => Option.bind oc M.step)^[t] (some c) = some c' → M.step c' = none →
    (P1Hier.rowsFrom M c n).length ≤ t + 1 := by
  intro t
  induction t with
  | zero =>
    intro c c' n h1 h2
    simp only [Function.iterate_zero, id, Option.some.injEq] at h1
    subst h1
    cases n with
    | zero => simp [P1Hier.rowsFrom]
    | succ n => simp [P1Hier.rowsFrom, h2]
  | succ t ih =>
    intro c c' n h1 h2
    rw [Function.iterate_succ_apply] at h1
    change (fun oc => Option.bind oc M.step)^[t] (M.step c) = some c' at h1
    cases hs : M.step c with
    | none =>
      rw [hs] at h1
      have : ∀ k, (fun oc => Option.bind oc M.step)^[k] (none : Option (Cfg M.K M.Γ M.Q)) = none := by
        intro k; induction k with
        | zero => rfl
        | succ k ihk => rw [Function.iterate_succ_apply]; exact ihk
      rw [this] at h1
      cases h1
    | some c₁ =>
      rw [hs] at h1
      cases n with
      | zero => simp [P1Hier.rowsFrom]
      | succ n =>
        have := ih c₁ c' n h1 h2
        simp [P1Hier.rowsFrom, hs]
        omega

theorem length_transcript_le {M : Machine} {y : List Bool} {v : Bool} {T : ℕ} (h : HaltsWithin M y v T)
    (T' : ℕ) : (P1Hier.transcript M y T').length ≤ T + 1 := by
  obtain ⟨t, ht, c, h1, h2, -⟩ := h
  have := length_rowsFrom_le M t (M.init y) c T' h1 h2
  unfold P1Hier.transcript
  omega

/-! ## The verdict of `V*` and its count -/

open Classical in
/-- What `V*` computes on the guess `w` and the input `x`. -/
def outerVerdict (M : Machine) (j a b : ℕ) (w x : List Bool) : Bool :=
  decide (lpM2 (sOf j) a b x.length ≤ w.length ∧
    ∃ (τ : List P1Hier.Entry) (r : ℕ), (∀ e ∈ τ, e ∈ (P1Hier.code (flipM M)).table) ∧
      w.drop (lpM2 (sOf j) a b x.length) =
        encT (P1Hier.code (flipM M)).table τ ++ List.replicate r false ∧
      P1Hier.Check (P1Hier.code (flipM M))
        (padIn j a b x (w.take (lpM2 (sOf j) a b x.length))) w.length τ)

/-- The first `m` bits of a guess. -/
def cut (m g : ℕ) (w : Fin g → Bool) : Fin m → Bool := fun k => if h : (k : ℕ) < g then w ⟨k, h⟩ else false

theorem take_ofFn_cut {m g : ℕ} (hmg : m ≤ g) (w : Fin g → Bool) :
    (List.ofFn w).take m = List.ofFn (cut m g w) := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn, cut]
    have hk : k < g := by simp at h2; omega
    simp [hk]

open Classical in
/-- **The parity bookkeeping of `V*`.** -/
theorem outer_count (L : List Bool → Bool) (M : Machine) (Tb : ℕ → ℕ)
    (hM : ∀ y : List Bool, ∃ T ≤ Tb y.length, HaltsWithin M y (L y) T)
    (j a b : ℕ) (x : List Bool) (g : ℕ)
    (hroom : lpM2 (sOf j) a b x.length +
      ((P1Hier.code (flipM M)).table.length + 1) * (Tb (nuOf j a b x.length) + 1) ≤ g) :
    (Finset.univ.filter fun w : Fin g → Bool => outerVerdict M j a b (List.ofFn w) x = true).card =
      (Finset.univ.filter fun u : Fin (lpM2 (sOf j) a b x.length) → Bool =>
        L (padIn j a b x (List.ofFn u)) = false).card := by
  set m := lpM2 (sOf j) a b x.length with hm
  set tbl := (P1Hier.code (flipM M)).table with htbl
  have hmg : m ≤ g := by
    have : 0 ≤ (tbl.length + 1) * (Tb (nuOf j a b x.length) + 1) := Nat.zero_le _
    omega
  have hTbg : Tb (nuOf j a b x.length) ≤ g := by
    have : Tb (nuOf j a b x.length) + 1 ≤ (tbl.length + 1) * (Tb (nuOf j a b x.length) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- an accepted guess gives a `u` with `L = false`, and determines its rest
  have accept_spec : ∀ w : Fin g → Bool, outerVerdict M j a b (List.ofFn w) x = true →
      L (padIn j a b x (List.ofFn (cut m g w))) = false ∧
      ∃ r, (List.ofFn w).drop m = encT tbl (P1Hier.transcript (flipM M)
        (padIn j a b x (List.ofFn (cut m g w))) g) ++ List.replicate r false := by
    intro w hw
    unfold outerVerdict at hw
    rw [decide_eq_true_iff] at hw
    obtain ⟨-, τ, r, hmem, hdrop, hcheck⟩ := hw
    rw [List.length_ofFn, take_ofFn_cut hmg] at hcheck
    obtain ⟨hτ, hh⟩ := (P1Hier.check_iff (flipM M) _ _ _).1 hcheck
    refine ⟨?_, r, by rw [hdrop, hτ]⟩
    have h1 : HaltsWithin M (padIn j a b x (List.ofFn (cut m g w))) false g := haltsWithin_flipM.1 hh
    obtain ⟨T, -, h2⟩ := hM (padIn j a b x (List.ofFn (cut m g w)))
    exact (halts_unique M h1 h2).symm
  apply Finset.card_bij (fun w _ => cut m g w)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact (accept_spec w hw).1
  · intro w₁ hw₁ w₂ hw₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
    obtain ⟨-, r₁, hr₁⟩ := accept_spec w₁ hw₁
    obtain ⟨-, r₂, hr₂⟩ := accept_spec w₂ hw₂
    rw [heq] at hr₁
    have hl : ((List.ofFn w₁).drop m).length = ((List.ofFn w₂).drop m).length := by simp
    have hd : (List.ofFn w₁).drop m = (List.ofFn w₂).drop m := by
      rw [hr₁, hr₂] at hl ⊢
      simp only [List.length_append, List.length_replicate] at hl
      have : r₁ = r₂ := by omega
      rw [this]
    have ht : (List.ofFn w₁).take m = (List.ofFn w₂).take m := by
      rw [take_ofFn_cut hmg, take_ofFn_cut hmg, heq]
    apply List.ofFn_injective
    rw [← List.take_append_drop m (List.ofFn w₁), ← List.take_append_drop m (List.ofFn w₂), ht, hd]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    set y := padIn j a b x (List.ofFn u) with hy
    have hylen : y.length = nuOf j a b x.length := length_padIn_eq j a b x u
    obtain ⟨T, hT, hMy⟩ := hM y
    rw [hu, hylen] at *
    have hflip : HaltsWithin (flipM M) y true T := haltsWithin_flipM.2 hMy
    have hflipg : HaltsWithin (flipM M) y true g := hflip.mono (le_trans hT hTbg)
    set τ := P1Hier.transcript (flipM M) y g with hτ
    have hcheck : P1Hier.Check (P1Hier.code (flipM M)) y g τ :=
      (P1Hier.check_iff (flipM M) y g τ).2 ⟨rfl, hflipg⟩
    have hmem : ∀ e ∈ τ, e ∈ tbl := hcheck.2.1
    have hτlen : τ.length ≤ Tb (nuOf j a b x.length) + 1 := by
      have := length_transcript_le hflip g
      rw [← hτ] at this
      omega
    have henc : (encT tbl τ).length ≤ (Tb (nuOf j a b x.length) + 1) * (tbl.length + 1) :=
      le_trans (length_encT_le tbl τ hmem) (Nat.mul_le_mul_right _ hτlen)
    have hfit : m + (encT tbl τ).length ≤ g := by
      have : (Tb (nuOf j a b x.length) + 1) * (tbl.length + 1) =
          (tbl.length + 1) * (Tb (nuOf j a b x.length) + 1) := by ring
      omega
    set wl := List.ofFn u ++ (encT tbl τ ++ List.replicate (g - m - (encT tbl τ).length) false) with hwl
    have hwlen : wl.length = g := by
      simp only [hwl, List.length_append, List.length_ofFn, List.length_replicate]
      omega
    refine ⟨fun k => wl[(k : ℕ)]'(by rw [hwlen]; exact k.isLt), ?_, ?_⟩
    · have hofn : List.ofFn (fun k : Fin g => wl[(k : ℕ)]'(by rw [hwlen]; exact k.isLt)) = wl := by
        apply List.ext_getElem
        · simp [hwlen]
        · intro k h1 h2; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hofn]
      unfold outerVerdict
      rw [decide_eq_true_iff]
      have hu_len : (List.ofFn u).length = m := List.length_ofFn
      refine ⟨by omega, τ, g - m - (encT tbl τ).length, hmem, ?_, ?_⟩
      · rw [hwl, List.drop_left' hu_len]
      · rw [hwl, List.take_left' hu_len, hwlen]
        exact hcheck
    · funext k
      simp only [cut]
      have hk : (k : ℕ) < g := lt_of_lt_of_le k.isLt hmg
      rw [dif_pos hk]
      simp only [hwl]
      rw [List.getElem_append_left (by simp)]
      simp

/-- **Machine lemma B, implementation form**: a stack program computes `outerVerdict` (for the flipped `M`) in time
`C (|w| + ν + 1) + |withGuess w x|`, for every input and every guess (any length). -/
def OuterImpl (j a b : ℕ) : Prop :=
  ∀ M : Machine, ∃ (B : Type) (_ : Fintype B) (P : Prog B) (letB : Bool → B) (_ : Function.Injective letB)
    (ans : Option B → Bool) (C : ℕ), ∀ x w : List Bool, ∃ n r,
      Prog.Run [] P (initRegs letB (withGuess w x)) n r ∧
      n ≤ C * (w.length + nuOf j a b x.length + 1) + (withGuess w x).length ∧
      ans (r 0).head? = outerVerdict M j a b w x

theorem outerProg_of_impl {j a b : ℕ} (h : OuterImpl j a b) : OuterProg j a b := by
  intro L M Tb hM
  refine ⟨(P1Hier.code (flipM M)).table.length + 1, fun g n₂ hfit => ?_⟩
  obtain ⟨B, hB, P, letB, hinj, ans, C, hP⟩ := h M
  refine ⟨B, hB, P, letB, hinj, ans, fun w x => outerVerdict M j a b w x, C, fun x hx => ⟨?_, ?_⟩⟩
  · intro w
    obtain ⟨n, r, hr, hn, hv⟩ := hP x (List.ofFn w)
    rw [List.length_ofFn] at hn
    exact ⟨n, r, hr, hn, hv⟩
  · exact outer_count L M Tb hM j a b x (g x.length) (hfit x.length hx)

end

end P1Wrap.W3
