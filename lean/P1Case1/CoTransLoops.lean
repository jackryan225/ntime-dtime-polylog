import P1Case1.CoTransLoopsA

/-!
# P1, Case 1, task C1: the loops of the coTRANS verifier and their closed forms (part 2 of 2)

Part 1 (pop loop, skips, fuel, the loop that computes `N`): `CoTransLoopsA.lean`. R-build split the original file
on 2026-11-25 (no change of text; original: `research/p1/lean/notes/CoTransLoops.lean.orig-20261125`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace P1Case1.CoTrans

open OAI.Computability.IntegerMultiplication

/-! ## Arithmetic of the rounds -/

theorem rnd_inv (n : ℕ) : ∀ j : ℕ, (rnd^[j] (0, n, 0)).1 ≤ j ∧ (rnd^[j] (0, n, 0)).2.1 ≤ n ∧
    ((rnd^[j] (0, n, 0)).2.2 = 0 →
      n = 2 * (rnd^[j] (0, n, 0)).1 * (rnd^[j] (0, n, 0)).1 + (rnd^[j] (0, n, 0)).2.1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    generalize rnd^[j] (0, n, 0) = s at ih ⊢
    obtain ⟨N, m, f⟩ := s
    obtain ⟨h1, h2, h3⟩ := ih
    dsimp only at h1 h2 h3
    unfold rnd
    dsimp only
    split_ifs with hm <;> dsimp only
    · exact ⟨by omega, h2, h3⟩
    · refine ⟨by omega, by omega, fun hf => ?_⟩
      have hf0 : f = 0 := by omega
      have e := h3 hf0
      have e2 : 2 * (N + 1) * (N + 1) = 2 * N * N + 4 * N + 2 := by ring
      rw [e2]; omega

theorem rnd_sq (M : ℕ) : ∀ j : ℕ, j ≤ M → rnd^[j] (0, 2 * M * M, 0) = (j, 2 * M * M - 2 * j * j, 0) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Function.iterate_succ_apply', ih (by omega)]
    unfold rnd
    have h1 : 2 * (j + 1) * (j + 1) ≤ 2 * M * M := by
      have := Nat.mul_le_mul hj hj; nlinarith
    have e2 : 2 * (j + 1) * (j + 1) = 2 * j * j + 4 * j + 2 := by ring
    simp only
    rw [if_neg (by omega)]
    ext <;> simp <;> omega

theorem rnd_sq_after (M : ℕ) : ∀ j : ℕ, M ≤ j → rnd^[j] (0, 2 * M * M, 0) = (M, 0, 0) := by
  intro j hj
  obtain ⟨d, rfl⟩ : ∃ d, j = M + d := ⟨j - M, by omega⟩
  induction d with
  | zero =>
    rw [Nat.add_zero, rnd_sq M M le_rfl, Nat.sub_self]
  | succ d ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih (by omega)]
    simp [rnd]

/-- **Characterization of `N`.** After `n` rounds on `n` units: no flag and nothing left iff
`n = 2 N²` for the computed `N`; and `n = 2 M²` gives `N = M`. -/
theorem rnd_final (n : ℕ) :
    ((rnd^[n] (0, n, 0)).2.2 = 0 ∧ (rnd^[n] (0, n, 0)).2.1 = 0 ↔
      ∃ M, n = 2 * M * M) ∧
    ∀ M, n = 2 * M * M → (rnd^[n] (0, n, 0)) = (M, 0, 0) := by
  have key : ∀ M, n = 2 * M * M → (rnd^[n] (0, n, 0)) = (M, 0, 0) := by
    intro M hM
    have hle : M ≤ n := by
      rcases Nat.eq_zero_or_pos M with h | h
      · omega
      · rw [hM]; nlinarith
    rw [hM] at hle ⊢
    exact rnd_sq_after M _ hle
  refine ⟨⟨fun ⟨hf, hr⟩ => ⟨(rnd^[n] (0, n, 0)).1, by have := (rnd_inv n n).2.2 hf; omega⟩, fun ⟨M, hM⟩ => ?_⟩, key⟩
  rw [key M hM]; simp

/-! ## Copies -/

theorem xferF_src (src : ℕ) (outs extras : List ℕ) (r : Rg) : xferF src outs extras r src = [] := by
  simp [xferF]

theorem xferF_other (src : ℕ) (outs extras : List ℕ) (r : Rg) {j : ℕ} (hj : j ≠ src)
    (ho : j ∉ outs) (he : j ∉ extras) : xferF src outs extras r j = r j := by
  simp [xferF, hj, List.count_eq_zero_of_not_mem ho, List.count_eq_zero_of_not_mem he, flatMap_nil']

theorem xferF_extra1 (src : ℕ) (outs extras : List ℕ) (r : Rg) {j : ℕ} (hj : j ≠ src)
    (ho : j ∉ outs) (he : extras.count j = 1) :
    xferF src outs extras r j = List.replicate (r src).length true ++ r j := by
  simp only [xferF, hj, if_false, List.count_eq_zero_of_not_mem ho, he, List.replicate_zero,
    List.append_nil, List.replicate_one, flatMap_true, List.length_reverse]

theorem xferF_out1 (src : ℕ) (outs extras : List ℕ) (r : Rg) {j : ℕ} (hj : j ≠ src)
    (ho : outs.count j = 1) (he : j ∉ extras) :
    xferF src outs extras r j = (r src).reverse ++ r j := by
  simp only [xferF, hj, if_false, List.count_eq_zero_of_not_mem he, ho, List.replicate_zero,
    List.nil_append, List.replicate_one, flatMap_single]

/-- Copy `x` (register 0) to register 9 and its length to registers 10 and 13 (unary). -/
def copyX : Pg := .join (xfer 0 [7] []) (xfer 7 [0, 9] [10, 13])

/-- Copy the unary register `R` to each register of `Ds` (through 7). -/
def copyU (R : ℕ) (Ds : List ℕ) : Pg := .join (xfer R [] [7]) (xfer 7 [] (R :: Ds))

/-- Read the top of `X` into `D` (flag if `X` is empty). -/
def readTo (X D : ℕ) : Pg := .look X fun o => match o with
  | none => flag
  | some a => .push D a

theorem runs_readTo {Γ : Sc} (X D : ℕ) (r : Rg) {a : Bool} {l : List Bool} (h : r X = a :: l) :
    Runs Γ (readTo X D) r (Function.update r D (a :: r D)) 2 := by
  have hl : Runs Γ (readTo X D) r (Function.update r D (a :: r D)) (1 + 1) := by
    refine Runs.look (c := fun o => match o with | none => flag | some a => .push D a) ?_
    rw [h]; exact Runs.push D a
  exact hl

/-- The two lookups, run only when `|x| = 2N²`, `i < N`, `k < N`. -/
def lookups : Pg := .join (repSkip 15 0) (.join (popLoop 17 0 13) (.join (readTo 0 11)
  (.join (repSkip 18 9) (.join (repSkip 16 9) (.join (popLoop 14 9 13) (readTo 9 12))))))

theorem getD_eq_head (x : List Bool) (p : ℕ) (hp : p < x.length) :
    x.drop p = x.getD p false :: x.drop (p + 1) := by
  rw [List.getD_eq_getElem _ _ hp]
  exact List.drop_eq_getElem_cons hp

theorem repF_other (S X m v : ℕ) (r : Rg) {j : ℕ} (h1 : j ≠ S) (h2 : j ≠ X) (h3 : j ≠ 8) :
    repF S X m v r j = r j := by simp [repF, h1, h2, h3]

theorem popLoopF_other (S X P m : ℕ) (r : Rg) {j : ℕ} (h1 : j ≠ S) (h2 : j ≠ X) (h3 : j ≠ 8)
    (h4 : j ≠ P) : popLoopF S X P m r j = r j := by simp [popLoopF, h1, h2, h3, h4]

theorem runs_lookups {Γ : Sc} (r : Rg) (x : List Bool) (N i k : ℕ) (hi : i < N) (hk : k < N)
    (hn : x.length = 2 * N * N)
    (h0 : r 0 = x) (h9 : r 9 = x) (h4 : r 4 = List.replicate N true) (h7 : r 7 = [])
    (h8 : r 8 = []) (h11 : r 11 = []) (h12 : r 12 = []) (h14 : r 14 = List.replicate i true)
    (h15 : r 15 = List.replicate i true) (h16 : r 16 = List.replicate k true)
    (h17 : r 17 = List.replicate k true) (h18 : r 18 = List.replicate N true) :
    ∃ r', Runs Γ lookups r r' (100 * (x.length + 1)) ∧ r' 8 = [] ∧
      r' 11 = [x.getD (N * i + k) false] ∧ r' 12 = [x.getD (N * N + N * k + i) false] ∧
      r' 10 = r 10 := by
  have hiN : i * N + k < x.length := by rw [hn]; nlinarith
  have hq : N * N + k * N + i < x.length := by rw [hn]; nlinarith
  -- lookup 1: skip i rows, then k entries, read
  have R1 := runs_repSkip (S := 15) (X := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) N Γ r h4 h7
  rw [h15, List.length_replicate] at R1
  set s1 := repF 15 0 i N r with hs1
  have s1_0 : s1 0 = x.drop (i * N) := by simp [hs1, repF, h0]
  have s1_8 : s1 8 = [] := by
    simp only [hs1, repF, h0, h8]; simp; omega
  have s1o : ∀ j, j ≠ 15 → j ≠ 0 → j ≠ 8 → s1 j = r j := fun j a b c => repF_other _ _ _ _ _ a b c
  have R2 := runs_popLoop (S := 17) (X := 0) (P := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Γ s1
  rw [s1o 17 (by decide) (by decide) (by decide), h17, List.length_replicate] at R2
  set s2 := popLoopF 17 0 13 k s1 with hs2
  have s2_0 : s2 0 = x.drop (i * N + k) := by
    simp only [hs2, popLoopF, s1_0]; simp [List.drop_drop, Nat.add_comm]
  have s2_8 : s2 8 = [] := by
    simp only [hs2, popLoopF, s1_0, s1_8]; simp; omega
  have s2o : ∀ j, j ≠ 17 → j ≠ 0 → j ≠ 8 → j ≠ 13 → s2 j = s1 j :=
    fun j a b c d => popLoopF_other _ _ _ _ _ a b c d
  have e1 : s2 0 = x.getD (N * i + k) false :: x.drop (i * N + k + 1) := by
    rw [s2_0, getD_eq_head x _ hiN, Nat.mul_comm i N]
  have R3 := runs_readTo (Γ := Γ) 0 11 s2 e1
  set s3 := Function.update s2 11 (x.getD (N * i + k) false :: s2 11) with hs3
  have s3o : ∀ j, j ≠ 11 → s3 j = s2 j := fun j a => by simp [hs3, a]
  have s3_11 : s3 11 = [x.getD (N * i + k) false] := by
    simp [hs3, s2o 11 (by decide) (by decide) (by decide) (by decide),
      s1o 11 (by decide) (by decide) (by decide), h11]
  -- lookup 2: skip N rows, k rows, i entries, read
  have s3_4 : s3 4 = List.replicate N true := by
    rw [s3o 4 (by decide), s2o 4 (by decide) (by decide) (by decide) (by decide),
      s1o 4 (by decide) (by decide) (by decide), h4]
  have s3_7 : s3 7 = [] := by
    rw [s3o 7 (by decide), s2o 7 (by decide) (by decide) (by decide) (by decide),
      s1o 7 (by decide) (by decide) (by decide), h7]
  have R4 := runs_repSkip (S := 18) (X := 9) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) N Γ s3 s3_4 s3_7
  rw [s3o 18 (by decide), s2o 18 (by decide) (by decide) (by decide) (by decide),
    s1o 18 (by decide) (by decide) (by decide), h18, List.length_replicate] at R4
  set s4 := repF 18 9 N N s3 with hs4
  have s3_9 : s3 9 = x := by
    rw [s3o 9 (by decide), s2o 9 (by decide) (by decide) (by decide) (by decide),
      s1o 9 (by decide) (by decide) (by decide), h9]
  have s3_8 : s3 8 = [] := by rw [s3o 8 (by decide), s2_8]
  have s4_9 : s4 9 = x.drop (N * N) := by simp [hs4, repF, s3_9]
  have s4_8 : s4 8 = [] := by
    simp only [hs4, repF, s3_9, s3_8]; simp; omega
  have s4o : ∀ j, j ≠ 18 → j ≠ 9 → j ≠ 8 → s4 j = s3 j := fun j a b c => repF_other _ _ _ _ _ a b c
  have s4_4 : s4 4 = List.replicate N true := by rw [s4o 4 (by decide) (by decide) (by decide), s3_4]
  have s4_7 : s4 7 = [] := by rw [s4o 7 (by decide) (by decide) (by decide), s3_7]
  have R5 := runs_repSkip (S := 16) (X := 9) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) N Γ s4 s4_4 s4_7
  rw [s4o 16 (by decide) (by decide) (by decide), s3o 16 (by decide),
    s2o 16 (by decide) (by decide) (by decide) (by decide),
    s1o 16 (by decide) (by decide) (by decide), h16, List.length_replicate] at R5
  set s5 := repF 16 9 k N s4 with hs5
  have s5_9 : s5 9 = x.drop (N * N + k * N) := by
    simp only [hs5, repF, s4_9]; simp [List.drop_drop, Nat.add_comm]
  have s5_8 : s5 8 = [] := by
    simp only [hs5, repF, s4_9, s4_8]; simp; omega
  have s5o : ∀ j, j ≠ 16 → j ≠ 9 → j ≠ 8 → s5 j = s4 j := fun j a b c => repF_other _ _ _ _ _ a b c
  have R6 := runs_popLoop (S := 14) (X := 9) (P := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Γ s5
  rw [s5o 14 (by decide) (by decide) (by decide), s4o 14 (by decide) (by decide) (by decide),
    s3o 14 (by decide), s2o 14 (by decide) (by decide) (by decide) (by decide),
    s1o 14 (by decide) (by decide) (by decide), h14, List.length_replicate] at R6
  set s6 := popLoopF 14 9 13 i s5 with hs6
  have s6_9 : s6 9 = x.drop (N * N + k * N + i) := by
    simp only [hs6, popLoopF, s5_9]; simp [List.drop_drop, Nat.add_comm]
  have s6_8 : s6 8 = [] := by
    simp only [hs6, popLoopF, s5_9, s5_8]; simp; omega
  have s6o : ∀ j, j ≠ 14 → j ≠ 9 → j ≠ 8 → j ≠ 13 → s6 j = s5 j :=
    fun j a b c d => popLoopF_other _ _ _ _ _ a b c d
  have e2 : s6 9 = x.getD (N * N + N * k + i) false :: x.drop (N * N + k * N + i + 1) := by
    rw [s6_9, getD_eq_head x _ hq, Nat.mul_comm k N]
  have R7 := runs_readTo (Γ := Γ) 9 12 s6 e2
  refine ⟨Function.update s6 12 (x.getD (N * N + N * k + i) false :: s6 12),
    (R1.join (R2.join (R3.join (R4.join (R5.join (R6.join R7)))))).mono ?_, ?_, ?_, ?_, ?_⟩
  · have hiN2 : i * (23 * N + 15) ≤ 23 * (N * N) + 15 * N := by nlinarith
    have hkN2 : k * (23 * N + 15) ≤ 23 * (N * N) + 15 * N := by nlinarith
    have hNN : N * (23 * N + 15) = 23 * (N * N) + 15 * N := by ring
    have hN1 : N ≤ N * N := Nat.le_mul_self N
    rw [hn]
    nlinarith
  · simp [s6_8]
  · simp only [Function.update_apply, show (11 : ℕ) ≠ 12 by decide, if_false]
    rw [s6o 11 (by decide) (by decide) (by decide) (by decide),
      s5o 11 (by decide) (by decide) (by decide), s4o 11 (by decide) (by decide) (by decide),
      s3_11]
  · simp only [Function.update_apply, if_true]
    rw [s6o 12 (by decide) (by decide) (by decide) (by decide),
      s5o 12 (by decide) (by decide) (by decide), s4o 12 (by decide) (by decide) (by decide),
      s3o 12 (by decide), s2o 12 (by decide) (by decide) (by decide) (by decide),
      s1o 12 (by decide) (by decide) (by decide), h12]
  · simp only [Function.update_apply, show (10 : ℕ) ≠ 12 by decide, if_false]
    rw [s6o 10 (by decide) (by decide) (by decide) (by decide),
      s5o 10 (by decide) (by decide) (by decide), s4o 10 (by decide) (by decide) (by decide),
      s3o 10 (by decide), s2o 10 (by decide) (by decide) (by decide) (by decide),
      s1o 10 (by decide) (by decide) (by decide)]

/-! ## Copy lemmas -/

def copyUF (R : ℕ) (Ds : List ℕ) (r : Rg) : Rg := fun j =>
  if j = 7 then [] else
  if j = R then List.replicate (r R).length true else
  if j ∈ Ds then List.replicate (r R).length true ++ r j else r j

theorem runs_copyU {Γ : Sc} (R : ℕ) (Ds : List ℕ) (hR7 : R ≠ 7) (hRD : R ∉ Ds) (h7D : (7 : ℕ) ∉ Ds)
    (hnd : Ds.Nodup) (r : Rg) (h7 : r 7 = []) :
    Runs Γ (copyU R Ds) r (copyUF R Ds r) ((r R).length * (3 * Ds.length + 22) + 8) := by
  have h1 := runs_xfer R [] [7] (by simp) (by simp [hR7]) Γ r
  have h2 := runs_xfer 7 [] (R :: Ds) (by simp) (by simp [hR7.symm, h7D]) Γ (xferF R [] [7] r)
  have e7 : xferF R [] [7] r 7 = List.replicate (r R).length true := by
    rw [xferF_extra1 _ _ _ _ hR7.symm (by simp) (by simp), h7, List.append_nil]
  rw [e7, List.length_replicate] at h2
  have eq : xferF 7 [] (R :: Ds) (xferF R [] [7] r) = copyUF R Ds r := by
    funext j
    unfold copyUF
    by_cases j7 : j = 7
    · subst j7; rw [xferF_src, if_pos rfl]
    · rw [if_neg j7]
      by_cases jR : j = R
      · subst jR
        rw [if_pos rfl, xferF_extra1 _ _ _ _ j7 (by simp) (by simp [List.count_cons, hRD,
          List.count_eq_zero_of_not_mem hRD]), e7, xferF_src, List.length_replicate,
          List.append_nil]
      · rw [if_neg jR]
        by_cases jD : j ∈ Ds
        · rw [if_pos jD, xferF_extra1 _ _ _ _ j7 (by simp) (by
              simp [List.count_cons, List.count_eq_one_of_mem hnd jD, Ne.symm jR]),
            e7, List.length_replicate, xferF_other _ _ _ _ jR (by simp) (by simp [j7])]
        · rw [if_neg jD, xferF_other _ _ _ _ j7 (by simp) (by simp [jR, jD]),
            xferF_other _ _ _ _ jR (by simp) (by simp [j7])]
  rw [eq] at h2
  refine (h1.join h2).mono ?_
  simp only [List.length_nil, List.length_cons, List.length_singleton]
  ring_nf
  omega

theorem pof_rep (X : ℕ) (r : Rg) {m : ℕ} (hX8 : X ≠ 8) (h : r X = List.replicate m true) :
    popOrFlagF X r X = List.replicate (m - 1) true ∧
      popOrFlagF X r 8 = List.replicate (1 - m) true ++ r 8 := by
  unfold popOrFlagF flagF
  cases m with
  | zero => rw [h]; simp [Function.update_apply, hX8, h, List.replicate_succ]
  | succ m => rw [h, List.replicate_succ]; simp [Function.update_apply, hX8.symm]

/-! ## The program after the guess is read -/

/-- `i < N` (flags otherwise); `i` in register 5, a copy of `N` in register 19. -/
def ltI : Pg := .join (popLoop 5 19 13) (popOrFlag 19)
def ltK : Pg := .join (popLoop 6 20 13) (popOrFlag 20)

def guard : Pg := .look 8 fun o => match o with
  | none => .look 10 fun o => match o with
    | none => lookups
    | some _ => .pass
  | some _ => .pass

def finalP : Pg := .look 8 fun o => match o with
  | some _ => .push 0 false
  | none => .look 10 fun o => match o with
    | some _ => .push 0 false
    | none => .look 11 fun o => match o with
      | none => .push 0 false
      | some a => .look 12 fun o => match o with
        | none => .push 0 false
        | some b => .push 0 (a != b)

/-- **The verifier after the guess**: `x` in register 0, `i`, `k` unary in registers 5, 6. -/
def rest : Pg := .join copyX (.join nLoop (.join (copyU 4 [18, 19, 20]) (.join (copyU 5 [14, 15])
  (.join (copyU 6 [16, 17]) (.join ltI (.join ltK (.join guard finalP)))))))

theorem runs_finalP_false {Γ : Sc} (r : Rg) (h : r 8 ≠ [] ∨ r 10 ≠ []) :
    ∃ r', Runs Γ finalP r r' 5 ∧ (r' 0).head? = some false := by
  rcases h8 : r 8 with _ | ⟨a, l⟩
  · rw [h8] at h
    have h10 : r 10 ≠ [] := by simpa using h
    obtain ⟨c, l', hc⟩ := List.exists_cons_of_ne_nil h10
    refine ⟨Function.update r 0 (false :: r 0), ?_, by simp⟩
    have hl : Runs Γ finalP r (Function.update r 0 (false :: r 0)) (1 + 1 + 1) := by
      refine Runs.look (c := fun o => match o with
        | some _ => .push 0 false
        | none => .look 10 fun o => match o with
          | some _ => .push 0 false
          | none => .look 11 fun o => match o with
            | none => .push 0 false
            | some a => .look 12 fun o => match o with
              | none => .push 0 false
              | some b => .push 0 (a != b)) ?_
      rw [h8]
      refine Runs.look (c := fun o => match o with
          | some _ => .push 0 false
          | none => .look 11 fun o => match o with
            | none => .push 0 false
            | some a => .look 12 fun o => match o with
              | none => .push 0 false
              | some b => .push 0 (a != b)) ?_
      rw [hc]; exact Runs.push 0 false
    exact hl.mono (by omega)
  · refine ⟨Function.update r 0 (false :: r 0), ?_, by simp⟩
    have hl : Runs Γ finalP r (Function.update r 0 (false :: r 0)) (1 + 1) := by
      refine Runs.look (c := fun o => match o with
        | some _ => .push 0 false
        | none => .look 10 fun o => match o with
          | some _ => .push 0 false
          | none => .look 11 fun o => match o with
            | none => .push 0 false
            | some a => .look 12 fun o => match o with
              | none => .push 0 false
              | some b => .push 0 (a != b)) ?_
      rw [h8]; exact Runs.push 0 false
    exact hl.mono (by omega)

theorem runs_finalP_ab {Γ : Sc} (r : Rg) {a b : Bool} (h8 : r 8 = []) (h10 : r 10 = [])
    (h11 : r 11 = [a]) (h12 : r 12 = [b]) :
    ∃ r', Runs Γ finalP r r' 5 ∧ (r' 0).head? = some (a != b) := by
  refine ⟨Function.update r 0 ((a != b) :: r 0), ?_, by simp⟩
  have hl : Runs Γ finalP r (Function.update r 0 ((a != b) :: r 0)) (1 + 1 + 1 + 1 + 1) := by
    refine Runs.look (c := fun o => match o with
      | some _ => .push 0 false
      | none => .look 10 fun o => match o with
        | some _ => .push 0 false
        | none => .look 11 fun o => match o with
          | none => .push 0 false
          | some a => .look 12 fun o => match o with
            | none => .push 0 false
            | some b => .push 0 (a != b)) ?_
    rw [h8]
    refine Runs.look (c := fun o => match o with
        | some _ => .push 0 false
        | none => .look 11 fun o => match o with
          | none => .push 0 false
          | some a => .look 12 fun o => match o with
            | none => .push 0 false
            | some b => .push 0 (a != b)) ?_
    rw [h10]
    refine Runs.look (c := fun o => match o with
          | none => .push 0 false
          | some a => .look 12 fun o => match o with
            | none => .push 0 false
            | some b => .push 0 (a != b)) ?_
    rw [h11]
    refine Runs.look (c := fun o => match o with
            | none => .push 0 false
            | some b => .push 0 (a != b)) ?_
    rw [h12]
    exact Runs.push 0 (a != b)
  exact hl

theorem runs_guard_skip {Γ : Sc} (r : Rg) (h : r 8 ≠ [] ∨ r 10 ≠ []) : Runs Γ guard r r 3 := by
  rcases h8 : r 8 with _ | ⟨a, l⟩
  · rw [h8] at h
    have h10 : r 10 ≠ [] := by simpa using h
    obtain ⟨c, l', hc⟩ := List.exists_cons_of_ne_nil h10
    have hl : Runs Γ guard r r (1 + 1 + 1) := by
      refine Runs.look (c := fun o => match o with
        | none => .look 10 fun o => match o with
          | none => lookups
          | some _ => .pass
        | some _ => .pass) ?_
      rw [h8]
      refine Runs.look (c := fun o => match o with
          | none => lookups
          | some _ => .pass) ?_
      rw [hc]; exact Runs.pass
    exact hl
  · have hl : Runs Γ guard r r (1 + 1) := by
      refine Runs.look (c := fun o => match o with
        | none => .look 10 fun o => match o with
          | none => lookups
          | some _ => .pass
        | some _ => .pass) ?_
      rw [h8]; exact Runs.pass
    exact hl.mono (by omega)

theorem runs_guard_go {Γ : Sc} (r u : Rg) {B : ℕ} (h8 : r 8 = []) (h10 : r 10 = [])
    (hl : Runs Γ lookups r u B) : Runs Γ guard r u (B + 2) := by
  have h : Runs Γ guard r u (B + 1 + 1) := by
    refine Runs.look (c := fun o => match o with
      | none => .look 10 fun o => match o with
        | none => lookups
        | some _ => .pass
      | some _ => .pass) ?_
    rw [h8]
    refine Runs.look (c := fun o => match o with
        | none => lookups
        | some _ => .pass) ?_
    rw [h10]; exact hl
  exact h

/-- The verdict computed by `rest`. -/
def VerdictIK (x : List Bool) (i k : ℕ) : Prop :=
  ∃ N : ℕ, x.length = 2 * N * N ∧ i < N ∧ k < N ∧
    x.getD (N * i + k) false ≠ x.getD (N * N + N * k + i) false

theorem verdictIK_good (x : List Bool) (i k Nf : ℕ) (hn2 : x.length = 2 * Nf * Nf)
    (hiN : i < Nf) (hkN : k < Nf) :
    VerdictIK x i k ↔ x.getD (Nf * i + k) false ≠ x.getD (Nf * Nf + Nf * k + i) false := by
  constructor
  · rintro ⟨N, hN, -, -, hne⟩
    have h1 : N * N = Nf * Nf := by
      have : 2 * (N * N) = 2 * (Nf * Nf) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hN, hn2]
      omega
    have h2 : N = Nf := Nat.mul_self_inj.mp h1
    subst h2; exact hne
  · intro h; exact ⟨Nf, hn2, hiN, hkN, h⟩

theorem verdictIK_bad (x : List Bool) (i k Nf rem fl : ℕ)
    (hst : rnd^[x.length] (0, x.length, 0) = (Nf, rem, fl))
    (hbad : ¬ ((1 - (Nf - k)) + (k - Nf) + ((1 - (Nf - i)) + (i - Nf) + fl) = 0 ∧ rem = 0)) :
    ¬ VerdictIK x i k := by
  rintro ⟨N, hN, hi, hk, -⟩
  have hM := (rnd_final x.length).2 N hN
  rw [hst] at hM
  simp only [Prod.mk.injEq] at hM
  obtain ⟨rfl, rfl, rfl⟩ := hM
  apply hbad
  omega

theorem bool_bne_decide (a b : Bool) (P : Prop) [Decidable P] (h : P ↔ a ≠ b) :
    (a != b) = decide P := by
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, decide_eq_true_iff, h]

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Run lemma of the verifier after the guess.** -/
theorem run_rest (Γ : Sc) (x : List Bool) (i k : ℕ) (r : Rg) (h0 : r 0 = x)
    (h5 : r 5 = List.replicate i true) (h6 : r 6 = List.replicate k true)
    (hz : ∀ j, j ≠ 0 → j ≠ 5 → j ≠ 6 → r j = []) :
    ∃ r', Runs Γ rest r r' (300 * (x.length + i + k + 1)) ∧
      (r' 0).head? = some (decide (VerdictIK x i k)) := by
  classical
  set n := x.length with hnx
  -- copyX
  have A1 := runs_xfer 0 [7] [] (by simp) (by simp) Γ r
  set q1 := xferF 0 [7] [] r with hq1
  have A2 := runs_xfer 7 [0, 9] [10, 13] (by simp) (by simp) Γ q1
  have q1_7 : q1 7 = x.reverse := by
    rw [hq1, xferF_out1 _ _ _ _ (by decide) (by simp) (by simp), h0, hz 7 (by decide) (by decide)
      (by decide), List.append_nil]
  rw [q1_7, List.length_reverse] at A2
  set r1 := xferF 7 [0, 9] [10, 13] q1 with hr1
  have r1_0 : r1 0 = x := by
    rw [hr1, xferF_out1 _ _ _ _ (by decide) (by simp) (by simp), q1_7, List.reverse_reverse, hq1,
      xferF_src, List.append_nil]
  have r1_9 : r1 9 = x := by
    rw [hr1, xferF_out1 _ _ _ _ (by decide) (by simp) (by simp), q1_7, List.reverse_reverse, hq1,
      xferF_other _ _ _ _ (by decide) (by simp) (by simp), hz 9 (by decide) (by decide) (by decide),
      List.append_nil]
  have r1_10 : r1 10 = List.replicate n true := by
    rw [hr1, xferF_extra1 _ _ _ _ (by decide) (by simp) (by simp), q1_7, List.length_reverse, hq1,
      xferF_other _ _ _ _ (by decide) (by simp) (by simp), hz 10 (by decide) (by decide)
      (by decide), List.append_nil]
  have r1_13 : r1 13 = List.replicate n true := by
    rw [hr1, xferF_extra1 _ _ _ _ (by decide) (by simp) (by simp), q1_7, List.length_reverse, hq1,
      xferF_other _ _ _ _ (by decide) (by simp) (by simp), hz 13 (by decide) (by decide)
      (by decide), List.append_nil]
  have r1_7 : r1 7 = [] := by rw [hr1, xferF_src]
  have r1o : ∀ j, j ≠ 0 → j ≠ 7 → j ≠ 9 → j ≠ 10 → j ≠ 13 → r1 j = r j := by
    intro j a b c d e
    rw [hr1, xferF_other _ _ _ _ b (by simp [a, c]) (by simp [d, e]), hq1,
      xferF_other _ _ _ _ a (by simp [b]) (by simp)]
  -- nLoop
  have U1 : U r1 0 n 0 [] r1 := ⟨by rw [r1o 4 (by decide) (by decide) (by decide) (by decide)
      (by decide), hz 4 (by decide) (by decide) (by decide)]; rfl, r1_7, r1_10,
    by rw [r1o 8 (by decide) (by decide) (by decide) (by decide) (by decide),
      hz 8 (by decide) (by decide) (by decide)]; rfl, fun j _ _ _ _ _ => rfl⟩
  have A3 := runs_nLoop Γ r1 U1
  rw [r1_13, List.length_replicate] at A3
  set r2 := (eachStep 13 (fun _ => nActF))^[n] r1 with hr2
  set st := rnd^[n] (0, n, 0) with hst
  have U2 : U r2 st.1 st.2.1 st.2.2 [] r1 := by
    have := n_iterate [] r1 (List.replicate n true) r1 (0, n, 0) r1_13 U1
    rwa [List.length_replicate] at this
  have r2_13 : r2 13 = [] := by
    have := eachStep_iterate_src 13 (fun _ => nActF) (fun a r => nActF_13 r)
      (List.replicate n true) r1 r1_13
    rwa [List.length_replicate] at this
  obtain ⟨u4, u7, u10, u8, uo⟩ := U2
  have inv := rnd_inv n n
  rw [← hst] at inv
  set Nf := st.1 with hNf
  set rem := st.2.1 with hrem
  set fl := st.2.2 with hfl
  have r2o : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 7 → j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 13 → r2 j = r j :=
    fun j a b c d e f g => by rw [uo j b c d f g, r1o j a c e f g]
  have r2_0 : r2 0 = x := by rw [uo 0 (by decide) (by decide) (by decide) (by decide) (by decide), r1_0]
  have r2_9 : r2 9 = x := by rw [uo 9 (by decide) (by decide) (by decide) (by decide) (by decide), r1_9]
  have r2e : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 13 →
      r2 j = [] := fun j a b c d e f g h l => by rw [r2o j a b e f g h l, hz j a c d]
  -- copies of N, i, k
  have B1 := runs_copyU (Γ := Γ) 4 [18, 19, 20] (by decide) (by decide) (by decide) (by decide) r2 u7
  set r3 := copyUF 4 [18, 19, 20] r2 with hr3
  have B2 := runs_copyU (Γ := Γ) 5 [14, 15] (by decide) (by decide) (by decide) (by decide) r3
    (by simp [hr3, copyUF])
  set r4 := copyUF 5 [14, 15] r3 with hr4
  have B3 := runs_copyU (Γ := Γ) 6 [16, 17] (by decide) (by decide) (by decide) (by decide) r4
    (by simp [hr4, copyUF])
  set r5 := copyUF 6 [16, 17] r4 with hr5
  have r5v : ∀ j, r5 j = if j = 7 then [] else if j = 4 ∨ j = 18 ∨ j = 19 ∨ j = 20 then
      List.replicate Nf true else if j = 5 ∨ j = 14 ∨ j = 15 then List.replicate i true else
      if j = 6 ∨ j = 16 ∨ j = 17 then List.replicate k true else r2 j := by
    intro j
    have e5 : r3 5 = List.replicate i true := by
      simp [hr3, copyUF, r2o 5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h5]
    have e6 : r4 6 = List.replicate k true := by
      simp [hr4, hr3, copyUF, r2o 6 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h6]
    have e4 : r2 4 = List.replicate Nf true := u4
    by_cases j7 : j = 7
    · subst j7; simp [hr5, copyUF]
    · rcases Nat.lt_or_ge j 21 with hj | hj
      · interval_cases j <;> simp_all [hr5, hr4, hr3, copyUF]
      · have : j ∉ [18, 19, 20] := by simp; omega
        have : j ∉ [14, 15] := by simp; omega
        have : j ∉ [16, 17] := by simp; omega
        simp [hr5, hr4, hr3, copyUF, j7, show j ≠ 4 by omega, show j ≠ 5 by omega,
          show j ≠ 6 by omega, show j ≠ 18 by omega, show j ≠ 19 by omega, show j ≠ 20 by omega,
          show j ≠ 14 by omega, show j ≠ 15 by omega, show j ≠ 16 by omega, show j ≠ 17 by omega]
  -- i < N and k < N
  have r5_5 : r5 5 = List.replicate i true := by rw [r5v]; simp
  have r5_6 : r5 6 = List.replicate k true := by rw [r5v]; simp
  have r5_19 : r5 19 = List.replicate Nf true := by rw [r5v]; simp
  have r5_20 : r5 20 = List.replicate Nf true := by rw [r5v]; simp
  have r5_8 : r5 8 = List.replicate fl true := by rw [r5v]; simp [u8]
  have C1 := runs_popLoop (S := 5) (X := 19) (P := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Γ r5
  rw [r5_5, List.length_replicate] at C1
  set r6a := popLoopF 5 19 13 i r5 with hr6a
  have r6a_19 : r6a 19 = List.replicate (Nf - i) true := by
    simp [hr6a, popLoopF, r5_19, List.drop_replicate]
  have C2 := runs_popOrFlag (Γ := Γ) 19 r6a
  set r6 := popOrFlagF 19 r6a with hr6
  obtain ⟨-, r6_8⟩ := pof_rep 19 r6a (by decide) r6a_19
  have r6o : ∀ j, j ≠ 5 → j ≠ 19 → j ≠ 8 → j ≠ 13 → r6 j = r5 j := fun j a b c d => by
    rw [hr6, pof_other 19 _ b c, hr6a, popLoopF_other _ _ _ _ _ a b c d]
  have r6_6 : r6 6 = List.replicate k true := by
    rw [r6o 6 (by decide) (by decide) (by decide) (by decide), r5_6]
  have C3 := runs_popLoop (S := 6) (X := 20) (P := 13) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Γ r6
  rw [r6_6, List.length_replicate] at C3
  set r7a := popLoopF 6 20 13 k r6 with hr7a
  have r7a_20 : r7a 20 = List.replicate (Nf - k) true := by
    simp [hr7a, popLoopF, r6o 20 (by decide) (by decide) (by decide) (by decide), r5_20,
      List.drop_replicate]
  have C4 := runs_popOrFlag (Γ := Γ) 20 r7a
  set r7 := popOrFlagF 20 r7a with hr7
  obtain ⟨-, r7_8⟩ := pof_rep 20 r7a (by decide) r7a_20
  have r7o : ∀ j, j ≠ 5 → j ≠ 6 → j ≠ 19 → j ≠ 20 → j ≠ 8 → j ≠ 13 → r7 j = r5 j :=
    fun j a b c d e f => by
      rw [hr7, pof_other 20 _ d e, hr7a, popLoopF_other _ _ _ _ _ b d e f, r6o j a c e f]
  set F := (1 - (Nf - k)) + (k - Nf) + ((1 - (Nf - i)) + (i - Nf) + fl) with hF
  have r6_20 : r6 20 = List.replicate Nf true := by
    rw [r6o 20 (by decide) (by decide) (by decide) (by decide), r5_20]
  have r6_8' : r6 8 = List.replicate ((1 - (Nf - i)) + (i - Nf) + fl) true := by
    rw [hr6, r6_8, hr6a]
    simp only [popLoopF, show (8 : ℕ) ≠ 5 by decide, show (8 : ℕ) ≠ 19 by decide, if_false,
      if_true, r5_19, r5_8, List.length_replicate, ← List.append_assoc, ← List.replicate_add]
    rw [Nat.add_assoc]
  have r7a_8 : r7a 8 = List.replicate (k - Nf) true ++ r6 8 := by
    simp only [hr7a, popLoopF, show (8 : ℕ) ≠ 6 by decide, show (8 : ℕ) ≠ 20 by decide, if_false,
      if_true, r6_20, List.length_replicate]
  have r7_8' : r7 8 = List.replicate F true := by
    rw [hr7, r7_8, r7a_8, r6_8', ← List.append_assoc, ← List.replicate_add, ← List.replicate_add]
    try rw [Nat.add_assoc]
  have r7_10 : r7 10 = List.replicate rem true := by
    rw [r7o 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]
    simp [u10]
  have r7v : ∀ j, j = 0 ∨ j = 9 → r7 j = x := by
    rintro j (rfl | rfl)
    · rw [r7o 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]
      simp [r2_0]
    · rw [r7o 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]
      simp [r2_9]
  have hNfn : Nf ≤ n := inv.1
  have r7e : ∀ j, j ≠ 5 → j ≠ 6 → j ≠ 19 → j ≠ 20 → j ≠ 8 → j ≠ 13 → j ≠ 7 → r7 j = r5 j := by
    intro j a b c d e f _; exact r7o j a b c d e f
  have r7_4 : r7 4 = List.replicate Nf true := by
    rw [r7o 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_18 : r7 18 = List.replicate Nf true := by
    rw [r7o 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_14 : r7 14 = List.replicate i true := by
    rw [r7o 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_15 : r7 15 = List.replicate i true := by
    rw [r7o 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_16 : r7 16 = List.replicate k true := by
    rw [r7o 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_17 : r7 17 = List.replicate k true := by
    rw [r7o 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_7 : r7 7 = [] := by
    rw [r7o 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]; simp
  have r7_11 : r7 11 = [] := by
    rw [r7o 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]
    simp [r2e 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have r7_12 : r7 12 = [] := by
    rw [r7o 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r5v]
    simp [r2e 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  have l0 : (r 0).length = n := by rw [h0]
  have l2 : (r2 4).length = Nf := by rw [u4, List.length_replicate]
  have l3 : (r3 5).length = i := by
    simp [hr3, copyUF, r2o 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h5]
  have l4 : (r4 6).length = k := by
    simp [hr4, hr3, copyUF, r2o 6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h6]
  rw [l0] at A1
  rw [l2] at B1
  rw [l3] at B2
  rw [l4] at B3
  simp only [List.length_cons, List.length_nil] at A1 A2 B1 B2 B3
  have hpot : nPot r1 ≤ 100 * n + 50 := by
    rw [nPot_U U1]; split_ifs <;> omega
  have hst3 : rnd^[x.length] (0, x.length, 0) = (Nf, rem, fl) := by
    rw [← hnx, ← hst]
  clear_value r7 r7a r6 r6a r5 r4 r3 r2 r1 q1 F Nf rem fl st
  by_cases good : F = 0 ∧ rem = 0
  · obtain ⟨hF0, hr0⟩ := good
    have hfl0 : fl = 0 := by omega
    have hiN : i < Nf := by omega
    have hkN : k < Nf := by omega
    have hn2 : x.length = 2 * Nf * Nf := by have := inv.2.2 hfl0; omega
    have e8 : r7 8 = [] := by rw [r7_8', hF0]; rfl
    have e10 : r7 10 = [] := by rw [r7_10, hr0]; rfl
    obtain ⟨u, L1, u8', u11, u12, u10'⟩ := runs_lookups (Γ := Γ) r7 x Nf i k hiN hkN hn2
      (r7v 0 (Or.inl rfl)) (r7v 9 (Or.inr rfl)) r7_4 r7_7 e8 r7_11 r7_12 r7_14 r7_15 r7_16
      r7_17 r7_18
    have G := runs_guard_go (Γ := Γ) r7 u e8 e10 L1
    obtain ⟨w, W, hw⟩ := runs_finalP_ab (Γ := Γ) u u8' (by rw [u10', e10]) u11 u12
    refine ⟨w, ((A1.join A2).join (A3.join (B1.join (B2.join (B3.join ((C1.join C2).join
      ((C3.join C4).join (G.join W)))))))).mono ?_, ?_⟩
    · omega
    · rw [hw, bool_bne_decide _ _ _ (verdictIK_good x i k Nf hn2 hiN hkN)]
  · have hbad : r7 8 ≠ [] ∨ r7 10 ≠ [] := by
      rw [r7_8', r7_10]
      by_cases hF0 : F = 0
      · right; have : rem ≠ 0 := fun h => good ⟨hF0, h⟩
        simpa using this
      · left; simpa using hF0
    have G := runs_guard_skip (Γ := Γ) r7 hbad
    obtain ⟨w, W, hw⟩ := runs_finalP_false (Γ := Γ) r7 hbad
    refine ⟨w, ((A1.join A2).join (A3.join (B1.join (B2.join (B3.join ((C1.join C2).join
      ((C3.join C4).join (G.join W)))))))).mono ?_, ?_⟩
    · omega
    · rw [hw]
      have hnot := verdictIK_bad x i k Nf rem fl hst3 (by rw [hF] at good; exact good)
      simp [hnot]

end P1Case1.CoTrans
#print axioms P1Case1.CoTrans.run_rest
