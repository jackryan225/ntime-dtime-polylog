import P1Wrap.InnerParse
import P1Wrap.InnerUnpack
import P1Wrap.TaskProg

/-!
# Piece B of W3: `InnerImpl` (the inner verifier as a stack program)

`innerImpl_of (hUG : Easy unG) : InnerImpl j a b`. The program `innerP` over `Bt A = Ltr ⊕ A`:
1. the parser task `pF` (OpenAI task framework, `task_prog`, letters mapped by `inl`);
2. `unpack`: flag to register 1, `x, u, γ` raw to registers 3, 4, 5;
3. `finalProg`: if the flag is `true`, run `R` on registers `3, 4, 5, …` (`Prog.rename (· + 3)`, letters `inr`)
   and write `!answer` to register 0; else write `true`.
Cost: linear in the input (`R` costs at most `c ν = c |y|`, `lpCost2_le_nu`).
-/

namespace P1Wrap.W3.Inner

open P1Int C1Challenge P1Wrap.W3 P1Wrap.W3.PT
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

variable {A : Type}

def decL : Bt A → Option Ltr
  | .inl l => some l
  | .inr _ => none

def decR : Bt A → Option A
  | .inl _ => none
  | .inr a => some a

def letB (b : Bool) : Bt A := .inl (.bit b)

def ansB : Option (Bt A) → Bool
  | some (.inl (.bit v)) => v
  | _ => false

/-- Run `R` on registers `3, 4, 5, …` if the flag in register 1 is `true`, then write the verdict. -/
def finalProg (R : Prog A) (answer : Option A → Bool) : Prog (Bt A) :=
  .look 1 fun o => match o with
    | some (.inl (.bit true)) => .join (Prog.rename (· + 3) (mapA Sum.inr decR R))
        (.look 3 fun o' => .push 0 (.inl (.bit (!(answer (o'.bind decR))))))
    | _ => .push 0 (.inl (.bit true))

/-- The inner verifier. -/
def innerP (p : Cmd) (R : Prog A) (letter : Bool → A) (answer : Option A → Bool) : Prog (Bt A) :=
  .join (mapA Sum.inl decL p) (.join (unpack letter) (finalProg R answer))

theorem e_init (z : List Bool) : mapR Sum.inl (initRegs Ltr.bit z) = initRegs (letB (A := A)) z := by
  funext k
  by_cases hk : k = 0
  · subst hk; simp [mapR, initRegs, letB]
  · simp [mapR, initRegs, hk]

theorem e_mid (l : List Ltr) :
    mapR Sum.inl (fun k : ℕ => if k = 0 then l else ([] : List Ltr)) =
      R6 (A := A) (l.map Sum.inl) [] [] [] [] [] := by
  apply R6_ext <;> simp [mapR]
  intro k hk
  simp [show k ≠ 0 by omega]

theorem ofFn_getElem_of_len {l : List Bool} {m : ℕ} (h : l.length = m) :
    List.ofFn (fun i : Fin m => l[i.1]'(by rw [h]; exact i.2)) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro k h1 h2; simp

theorem size_quad (ok : Bool) (x u γ : List Bool) :
    x.length + u.length + γ.length ≤ size (ok, x, u, γ) := by
  simp only [size_prod, Bits.size_word, size_bit]
  omega

theorem innerImpl_of (hUG : Easy unG) (j a b : ℕ) : InnerImpl j a b := by
  classical
  intro A hA R letter hlet answer c n₁ hR
  obtain ⟨p, C, hp⟩ := task_prog (fun z : List Bool => size z) (fun z => z)
    (fun z => send (pF j a b n₁ z)) (easy_pF hUG j a b n₁)
  obtain ⟨CF, hCF⟩ := (easy_pF hUG j a b n₁).length
  refine ⟨Bt A, inferInstance, innerP p R letter answer, letB, ?_, ansB, 3 * C + 40 * CF + c + 100, ?_⟩
  · intro v v' h
    simpa [letB] using h
  intro y w hw
  set z := withGuess w y with hz
  obtain ⟨t1, hrun1, ht1⟩ := hp z
  have hdL : ∀ l : Ltr, decL (A := A) (Sum.inl l) = some l := fun _ => rfl
  have hdR : ∀ a : A, decR (Sum.inr a) = some a := fun _ => rfl
  have r1 : Runs [] (mapA Sum.inl (decL (A := A)) p) (initRegs letB z)
      (R6 (A := A) ((send (pF j a b n₁ z)).spell.map Sum.inl) [] [] [] [] []) t1 := by
    refine ⟨t1, ?_, le_rfl⟩
    rw [← e_init, ← e_mid]
    exact run_mapA hdL hrun1
  have hsz : size (pF j a b n₁ z) ≤ CF * size z := hCF z
  have hzs : size z = 2 * z.length + 1 := Bits.size_word z
  have ht1' : t1 ≤ C * (z.length + size z + 1) := ht1
  generalize hFz : pF j a b n₁ z = F at r1 hsz
  obtain ⟨ok, x, u, γ⟩ := F
  have r2 := unpack_runs letter [] ok x u γ
  have hq := size_quad ok x u γ
  have e1 : C * (z.length + size z + 1) ≤ 3 * C * (z.length + 1) := by
    rw [hzs]; nlinarith
  have e2 : CF * size z ≤ 2 * CF * (z.length + 1) := by rw [hzs]; nlinarith
  have eK : (3 * C + 40 * CF + c + 100) * (z.length + 1) =
      3 * C * (z.length + 1) + 20 * (2 * CF * (z.length + 1)) + c * (z.length + 1) +
        100 * (z.length + 1) := by ring
  cases ok with
  | false =>
    have hh : (R6 (A := A) [] [.inl (.bit false)] [] (x.map fun b => Sum.inr (letter b))
        (u.map fun b => Sum.inr (letter b)) (γ.map fun b => Sum.inr (letter b)) 1).head? =
        some (.inl (.bit false)) := by simp [R6]
    set S := R6 (A := A) [] [.inl (.bit false)] [] (x.map fun b => Sum.inr (letter b))
        (u.map fun b => Sum.inr (letter b)) (γ.map fun b => Sum.inr (letter b)) with hS
    have r3 : Runs [] (finalProg R answer) S
        (Function.update S 0 (Sum.inl (Ltr.bit true) :: S 0)) 2 :=
      Runs.look hh (Runs.push 0 (Sum.inl (Ltr.bit true)))
    obtain ⟨n, hrun, hn⟩ := Runs.join r1 (Runs.join r2 r3)
    refine ⟨n, _, hrun, ?_, ?_⟩
    · have : c * 0 ≤ c * (z.length + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · simp only [Function.update_self, List.head?_cons, ansB]
      symm
      unfold innerVerdict
      rw [decide_eq_true_iff]
      rintro ⟨x', u', hx', hu', hy', -⟩
      have hv := pF_valid j a b n₁ hx' hu' w
      rw [← hy', ← hz, hFz] at hv
      simp at hv
  | true =>
    have hok : pOk j a b n₁ z = true := by
      have := congrArg Prod.fst hFz
      simpa [pF] using this
    obtain ⟨x', u', hx', hu', hy'⟩ := pF_ok j a b n₁ z hok
    have hyz : pY z = y := by simp [pY, hz, unG_withGuess]
    rw [hyz] at hy'
    have hv := pF_valid j a b n₁ hx' hu' w
    rw [← hy', ← hz, hFz] at hv
    simp only [Prod.mk.injEq, true_and] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    have hylen : y.length = nuOf j a b x.length := by rw [hy']; exact length_padIn j a b x u hu'
    have hkw : lpK2 a b x.length ≤ w.length := by
      rw [hw, hylen]; exact lpK2_le_guessLen j a b x.length
    have hγl : (w.take (lpK2 a b x.length)).length = lpK2 a b x.length := by
      simp [List.length_take]; omega
    obtain ⟨v, nR, hnR, rR, hrunR, hvR⟩ := hR x hx' (fun i => u[i.1]'(by rw [hu']; exact i.2))
      (fun i => (w.take (lpK2 a b x.length))[i.1]'(by rw [hγl]; exact i.2))
    rw [ofFn_getElem_of_len hu', ofFn_getElem_of_len hγl] at hrunR
    set γ := w.take (lpK2 a b x.length) with hγ
    set S6 := R6 (A := A) [] [.inl (.bit true)] [] (x.map fun b => Sum.inr (letter b))
      (u.map fun b => Sum.inr (letter b)) (γ.map fun b => Sum.inr (letter b)) with hS6
    have hj3 : Function.Injective (fun i : ℕ => i + 3) := fun i i' h => by simpa using h
    have hmap := run_mapA hdR hrunR
    have hpaint : Prog.paint (fun i : ℕ => i + 3) (mapR Sum.inr (inputRegs letter x u γ)) S6 = S6 := by
      apply paint_self hj3
      intro l
      rcases l with _ | _ | _ | l
      · simp [hS6, R6, mapR, inputRegs, List.map_map, Function.comp_def]
      · simp [hS6, R6, mapR, inputRegs, List.map_map, Function.comp_def]
      · simp [hS6, R6, mapR, inputRegs, List.map_map, Function.comp_def]
      · simp only [hS6, R6, mapR, inputRegs, show l + 1 + 1 + 1 + 3 ≠ 0 by omega,
          show l + 1 + 1 + 1 + 3 ≠ 1 by omega, show l + 1 + 1 + 1 + 3 ≠ 2 by omega,
          show l + 1 + 1 + 1 + 3 ≠ 3 by omega, show l + 1 + 1 + 1 + 3 ≠ 4 by omega,
          show l + 1 + 1 + 1 + 3 ≠ 5 by omega, show l + 1 + 1 + 1 ≠ 0 by omega,
          show l + 1 + 1 + 1 ≠ 1 by omega, show l + 1 + 1 + 1 ≠ 2 by omega, if_false, List.map_nil]
    have hren := Prog.Run.rename hj3 hmap S6
    rw [hpaint] at hren
    set T := Prog.paint (fun i : ℕ => i + 3) (mapR Sum.inr rR) S6 with hT
    have hT0 : T 0 = [] := by
      rw [hT, Prog.paint_else _ _ _ (fun l => by omega)]
      simp [hS6, R6]
    have hT3 : T 3 = mapR Sum.inr rR 0 := Prog.paint_at hj3 _ _ 0
    have hh3 : (T 3).head?.bind decR = (rR 0).head? := by rw [hT3]; exact head_mapR hdR rR 0
    have rRun : Runs [] (Prog.rename (· + 3) (mapA Sum.inr decR R)) S6 T nR := ⟨nR, hren, le_rfl⟩
    have rLook : Runs [] (.look 3 fun o' => .push 0 (.inl (.bit (!(answer (o'.bind decR))))))
        T (Function.update T 0 (.inl (.bit (!(answer ((T 3).head?.bind decR)))) :: T 0)) 2 :=
      Runs.look rfl (Runs.push 0 _)
    have hh1 : (S6 1).head? = some (.inl (.bit true)) := by simp [hS6, R6]
    have r3 : Runs [] (finalProg R answer) S6
        (Function.update T 0 (.inl (.bit (!(answer ((T 3).head?.bind decR)))) :: T 0)) (nR + 2 + 2 + 1) :=
      Runs.look hh1 (Runs.join rRun rLook)
    obtain ⟨n, hrun, hn⟩ := Runs.join r1 (Runs.join r2 r3)
    refine ⟨n, _, hrun, ?_, ?_⟩
    · have hc : nR ≤ c * z.length := by
        have h1 : nR ≤ c * nuOf j a b x.length := le_trans hnR (lpCost2_le_nu c j a b x.length)
        have h2 : nuOf j a b x.length ≤ z.length := by
          rw [← hylen, hz, length_withGuess']; omega
        exact le_trans h1 (Nat.mul_le_mul_left _ h2)
      have : c * z.length ≤ c * (z.length + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · simp only [Function.update_self, List.head?_cons, ansB]
      rw [hh3, hvR]
      unfold innerVerdict
      have key : (∃ x'' u'' : List Bool, n₁ ≤ x''.length ∧
          u''.length = lpM2 (sOf j) a b x''.length ∧ y = padIn j a b x'' u'' ∧
          ProgAnswers R answer (inputRegs letter x'' u'' (w.take (lpK2 a b x''.length))) true
            (lpCost2 c (sOf j) a b x''.length)) ↔ v = true := by
        constructor
        · rintro ⟨x'', u'', -, hu'', hy'', hacc⟩
          rw [hy'] at hy''
          obtain ⟨rfl, rfl⟩ := padIn_inj hu' hu'' hy''
          exact (progAnswers_unique ⟨nR, hnR, rR, hrunR, hvR⟩ hacc)
        · intro hvt
          subst hvt
          exact ⟨x, u, hx', hu', hy', nR, hnR, rR, hrunR, hvR⟩
      simp only [key]
      cases v <;> simp

end P1Wrap.W3.Inner
