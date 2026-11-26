import P1Wrap.ProgMap
import OAI.Computability.IntegerMultiplication.Code.Task

/-!
# Piece B of W3: unpacking a tree-coded tuple into raw registers

The inner verifier computes `F (withGuess w y) = (ok, x, u, γ)` as an OpenAI task; the answer tree sits spelled in
register 0. `unpack f` moves it into raw registers over the alphabet `Bt A = Ltr ⊕ A`:
register 1 = the flag `inl (bit ok)`, registers 3, 4, 5 = `x`, `u`, `γ` letter by letter (`inr (f b)`, first bit on
top), all others empty (`unpack_runs`). Register 2 is scratch.
-/

namespace P1Wrap.W3.Inner

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## Runs with a cost bound -/

section Runs
variable {B : Type}

def Runs (Γ : Scope B) (p : Prog B) (r s : Reg B) (N : ℕ) : Prop := ∃ n, Prog.Run Γ p r n s ∧ n ≤ N

namespace Runs
variable {Γ : Scope B} {p q : Prog B} {r s t : Reg B} {N N' : ℕ}

theorem mono (h : Runs Γ p r s N) (hN : N ≤ N') : Runs Γ p r s N' := by
  obtain ⟨n, h, hn⟩ := h; exact ⟨n, h, le_trans hn hN⟩

theorem pass : Runs Γ .pass r r 1 := ⟨1, .pass, le_rfl⟩

theorem push (i : ℕ) (x : B) : Runs Γ (.push i x) r (Function.update r i (x :: r i)) 1 :=
  ⟨1, .push, le_rfl⟩

theorem pop (i : ℕ) : Runs Γ (.pop i) r (Function.update r i (r i).tail) 1 := ⟨1, .pop, le_rfl⟩

theorem look {i : ℕ} {c : Option B → Prog B} {o : Option B} (ho : (r i).head? = o)
    (h : Runs Γ (c o) r s N) : Runs Γ (.look i c) r s (N + 1) := by
  obtain ⟨n, h, hn⟩ := h
  subst ho
  exact ⟨1 + n, .look h, by omega⟩

theorem join (h1 : Runs Γ p r s N) (h2 : Runs Γ q s t N') : Runs Γ (.join p q) r t (N + N' + 2) := by
  obtain ⟨n, h1, hn⟩ := h1
  obtain ⟨n', h2, hn'⟩ := h2
  exact ⟨1 + n + 1 + n', .join h1 h2, by omega⟩

theorem tie {c : Prog B} (h : Runs (c :: Γ) c r s N) : Runs Γ (.tie c) r s (N + 1) := by
  obtain ⟨n, h, hn⟩ := h
  exact ⟨1 + n, .tie h, by omega⟩

theorem again0 {c : Prog B} (h : Runs (c :: Γ) c r s N) : Runs (c :: Γ) (.again 0) r s (N + 1) := by
  obtain ⟨n, h, hn⟩ := h
  exact ⟨1 + n, .again (i := 0) rfl h, by omega⟩

end Runs
end Runs

/-! ## The two loops -/

variable {A : Type}

/-- The program alphabet of the inner verifier. -/
abbrev Bt (A : Type) := Ltr ⊕ A

/-- The tree of a bit list, spelled. -/
def spellL (l : List Bool) : List Ltr := (send l).spell

theorem spellL_nil : spellL [] = [Ltr.bit false] := rfl

theorem spellL_cons (b : Bool) (l : List Bool) :
    spellL (b :: l) = Ltr.node :: Ltr.bit b :: spellL l := rfl

/-- One round of the list reader: `node, bit b` becomes `inr (f b)` on `dst`; anything else ends the list. -/
def readBody (f : Bool → A) (dst : ℕ) : Prog (Bt A) :=
  .look 0 fun o => match o with
    | some (.inl .node) => .join (.pop 0) (.look 0 fun o' => match o' with
        | some (.inl (.bit b)) => .join (.pop 0) (.join (.push dst (.inr (f b))) (.again 0))
        | _ => .pass)
    | _ => .pop 0

def readList (f : Bool → A) (dst : ℕ) : Prog (Bt A) := .tie (readBody f dst)

theorem readBody_runs (f : Bool → A) {dst : ℕ} (hd : dst ≠ 0) (Γ : Scope (Bt A)) :
    ∀ (l : List Bool) (ρ : Reg (Bt A)) (rest : List (Bt A)), ρ 0 = (spellL l).map Sum.inl ++ rest →
    ∃ s, Runs (readBody f dst :: Γ) (readBody f dst) ρ s (12 * l.length + 2) ∧
      s 0 = rest ∧ s dst = (l.reverse.map fun b => Sum.inr (f b)) ++ ρ dst ∧
      ∀ k, k ≠ 0 → k ≠ dst → s k = ρ k
  | [], ρ, rest, h => by
      have hh : (ρ 0).head? = some (Sum.inl (Ltr.bit false)) := by rw [h]; rfl
      refine ⟨_, (Runs.look hh (Runs.pop 0)).mono (by simp), ?_, ?_, ?_⟩
      · simp [h, spellL_nil]
      · simp [Function.update_of_ne hd]
      · intro k hk _
        simp [Function.update_of_ne hk]
  | b :: l, ρ, rest, h => by
      have h0 : ρ 0 = Sum.inl Ltr.node :: Sum.inl (Ltr.bit b) :: ((spellL l).map Sum.inl ++ rest) := by
        rw [h, spellL_cons]; rfl
      set ρ1 := Function.update ρ 0 (ρ 0).tail with hρ1
      set ρ2 := Function.update ρ1 0 (ρ1 0).tail with hρ2
      set ρ3 := Function.update ρ2 dst (Sum.inr (f b) :: ρ2 dst) with hρ3
      have h10 : ρ1 0 = Sum.inl (Ltr.bit b) :: ((spellL l).map Sum.inl ++ rest) := by
        rw [hρ1, Function.update_self, h0]; rfl
      have h20 : ρ2 0 = (spellL l).map Sum.inl ++ rest := by
        rw [hρ2, Function.update_self, h10]; rfl
      have h30 : ρ3 0 = (spellL l).map Sum.inl ++ rest := by
        rw [hρ3, Function.update_of_ne (Ne.symm hd)]; exact h20
      obtain ⟨s, hrun, hs0, hsd, hso⟩ := readBody_runs f hd Γ l ρ3 rest h30
      have hh1 : (ρ 0).head? = some (Sum.inl Ltr.node) := by rw [h0]; rfl
      have hh2 : (ρ1 0).head? = some (Sum.inl (Ltr.bit b)) := by rw [h10]; rfl
      refine ⟨s, (Runs.look hh1 (Runs.join (Runs.pop 0) (Runs.look hh2 (Runs.join (Runs.pop 0)
        (Runs.join (Runs.push dst (Sum.inr (f b))) (Runs.again0 hrun)))))).mono ?_, hs0, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [hsd, hρ3, Function.update_self, hρ2, Function.update_of_ne hd, hρ1,
          Function.update_of_ne hd]
        simp
      · intro k hk1 hk2
        rw [hso k hk1 hk2, hρ3, Function.update_of_ne hk2, hρ2, Function.update_of_ne hk1, hρ1,
          Function.update_of_ne hk1]

theorem readList_runs (f : Bool → A) {dst : ℕ} (hd : dst ≠ 0) (Γ : Scope (Bt A)) (l : List Bool)
    (ρ : Reg (Bt A)) (rest : List (Bt A)) (h : ρ 0 = (spellL l).map Sum.inl ++ rest) :
    ∃ s, Runs Γ (readList f dst) ρ s (12 * l.length + 3) ∧
      s 0 = rest ∧ s dst = (l.reverse.map fun b => Sum.inr (f b)) ++ ρ dst ∧
      ∀ k, k ≠ 0 → k ≠ dst → s k = ρ k := by
  obtain ⟨s, hr, h1, h2, h3⟩ := readBody_runs f hd Γ l ρ rest h
  exact ⟨s, Runs.tie hr, h1, h2, h3⟩

/-- One round of the mover: top of `src` onto `dst`. -/
def moveBody (src dst : ℕ) : Prog (Bt A) :=
  .look src fun o => match o with
    | some v => .join (.pop src) (.join (.push dst v) (.again 0))
    | none => .pass

def moveRev (src dst : ℕ) : Prog (Bt A) := .tie (moveBody src dst)

theorem moveBody_runs {src dst : ℕ} (hsd : src ≠ dst) (Γ : Scope (Bt A)) :
    ∀ (l : List (Bt A)) (ρ : Reg (Bt A)), ρ src = l →
    ∃ s, Runs (moveBody src dst :: Γ) (moveBody src dst) ρ s (8 * l.length + 2) ∧
      s src = [] ∧ s dst = l.reverse ++ ρ dst ∧ ∀ k, k ≠ src → k ≠ dst → s k = ρ k
  | [], ρ, h => by
      have hh : (ρ src).head? = none := by rw [h]; rfl
      exact ⟨ρ, (Runs.look hh Runs.pass).mono (by simp), h, by simp, fun _ _ _ => rfl⟩
  | v :: l, ρ, h => by
      set ρ1 := Function.update ρ src (ρ src).tail with hρ1
      set ρ2 := Function.update ρ1 dst (v :: ρ1 dst) with hρ2
      have h20 : ρ2 src = l := by
        rw [hρ2, Function.update_of_ne hsd, hρ1, Function.update_self, h]; rfl
      obtain ⟨s, hrun, hs0, hsd', hso⟩ := moveBody_runs hsd Γ l ρ2 h20
      have hh : (ρ src).head? = some v := by rw [h]; rfl
      refine ⟨s, (Runs.look hh (Runs.join (Runs.pop src) (Runs.join (Runs.push dst v)
        (Runs.again0 hrun)))).mono ?_, hs0, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [hsd', hρ2, Function.update_self, hρ1, Function.update_of_ne (Ne.symm hsd)]
        simp
      · intro k hk1 hk2
        rw [hso k hk1 hk2, hρ2, Function.update_of_ne hk2, hρ1, Function.update_of_ne hk1]

theorem moveRev_runs {src dst : ℕ} (hsd : src ≠ dst) (Γ : Scope (Bt A)) (ρ : Reg (Bt A)) :
    ∃ s, Runs Γ (moveRev src dst) ρ s (8 * (ρ src).length + 3) ∧
      s src = [] ∧ s dst = (ρ src).reverse ++ ρ dst ∧ ∀ k, k ≠ src → k ≠ dst → s k = ρ k := by
  obtain ⟨s, hr, h1, h2, h3⟩ := moveBody_runs hsd Γ (ρ src) ρ rfl
  exact ⟨s, Runs.tie hr, h1, h2, h3⟩

/-! ## Six-register states -/

/-- The register file with contents `r0, …, r5` in registers `0, …, 5` and nothing else. -/
def R6 (r0 r1 r2 r3 r4 r5 : List (Bt A)) : Reg (Bt A) := fun k =>
  if k = 0 then r0 else if k = 1 then r1 else if k = 2 then r2 else if k = 3 then r3 else
    if k = 4 then r4 else if k = 5 then r5 else []

theorem R6_ext {s : Reg (Bt A)} {r0 r1 r2 r3 r4 r5 : List (Bt A)} (h0 : s 0 = r0) (h1 : s 1 = r1)
    (h2 : s 2 = r2) (h3 : s 3 = r3) (h4 : s 4 = r4) (h5 : s 5 = r5) (h : ∀ k, 6 ≤ k → s k = []) :
    s = R6 r0 r1 r2 r3 r4 r5 := by
  funext k
  rcases k with _ | _ | _ | _ | _ | _ | k
  · simpa [R6] using h0
  · simpa [R6] using h1
  · simpa [R6] using h2
  · simpa [R6] using h3
  · simpa [R6] using h4
  · simpa [R6] using h5
  · rw [h (k + 6) (by omega)]
    simp only [R6, show k + 6 ≠ 0 by omega, show k + 6 ≠ 1 by omega, show k + 6 ≠ 2 by omega,
      show k + 6 ≠ 3 by omega, show k + 6 ≠ 4 by omega, show k + 6 ≠ 5 by omega, if_false]

theorem R6_update0 (x r0 r1 r2 r3 r4 r5 : List (Bt A)) :
    Function.update (R6 r0 r1 r2 r3 r4 r5) 0 x = R6 x r1 r2 r3 r4 r5 := by
  funext k
  rcases k with _ | k <;> simp [R6]

theorem R6_update1 (x r0 r1 r2 r3 r4 r5 : List (Bt A)) :
    Function.update (R6 r0 r1 r2 r3 r4 r5) 1 x = R6 r0 x r2 r3 r4 r5 := by
  funext k
  rcases k with _ | _ | k <;> simp [R6]

theorem pop0_runs (Γ : Scope (Bt A)) (a : Bt A) (r0 r1 r2 r3 r4 r5 : List (Bt A)) :
    Runs Γ (.pop 0) (R6 (a :: r0) r1 r2 r3 r4 r5) (R6 r0 r1 r2 r3 r4 r5) 1 := by
  have e : Function.update (R6 (a :: r0) r1 r2 r3 r4 r5) 0 ((R6 (a :: r0) r1 r2 r3 r4 r5) 0).tail =
      R6 r0 r1 r2 r3 r4 r5 := by
    rw [R6_update0]; simp [R6]
  rw [← e]
  exact Runs.pop 0

/-- Copy the flag bit at the top of register 0 into register 1. -/
def flagProg : Prog (Bt A) := .look 0 fun o => match o with
  | some (.inl (.bit v)) => .push 1 (.inl (.bit v))
  | _ => .pass

theorem flag_runs (Γ : Scope (Bt A)) (v : Bool) (r0 r2 r3 r4 r5 : List (Bt A)) :
    Runs Γ flagProg (R6 (.inl (.bit v) :: r0) [] r2 r3 r4 r5)
      (R6 (.inl (.bit v) :: r0) [.inl (.bit v)] r2 r3 r4 r5) 2 := by
  have e : Function.update (R6 (.inl (.bit v) :: r0) [] r2 r3 r4 r5) 1
      (.inl (.bit v) :: (R6 (.inl (.bit v) :: r0) [] r2 r3 r4 r5) 1) =
      R6 (.inl (.bit v) :: r0) [.inl (.bit v)] r2 r3 r4 r5 := by
    rw [R6_update1]; simp [R6]
  have hh : ((R6 (A := A) (.inl (.bit v) :: r0) [] r2 r3 r4 r5) 0).head? = some (.inl (.bit v)) := by
    simp [R6]
  rw [← e]
  exact Runs.look hh (Runs.push 1 _)

theorem read2_runs (f : Bool → A) (Γ : Scope (Bt A)) (l : List Bool) (rest r1 r3 r4 r5 : List (Bt A)) :
    Runs Γ (readList f 2) (R6 ((spellL l).map Sum.inl ++ rest) r1 [] r3 r4 r5)
      (R6 rest r1 (l.reverse.map fun b => Sum.inr (f b)) r3 r4 r5) (12 * l.length + 3) := by
  obtain ⟨s, hr, h0, h2, ho⟩ := readList_runs f (dst := 2) (by norm_num) Γ l
    (R6 ((spellL l).map Sum.inl ++ rest) r1 [] r3 r4 r5) rest (by simp [R6])
  have e : s = R6 rest r1 (l.reverse.map fun b => Sum.inr (f b)) r3 r4 r5 := by
    apply R6_ext h0
    · rw [ho 1 (by norm_num) (by norm_num)]; simp [R6]
    · rw [h2]; simp [R6]
    · rw [ho 3 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 4 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 5 (by norm_num) (by norm_num)]; simp [R6]
    · intro k hk
      rw [ho k (by omega) (by omega)]
      simp [R6, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
        show k ≠ 4 by omega, show k ≠ 5 by omega]
  rw [← e]; exact hr

theorem move23_runs (Γ : Scope (Bt A)) (r0 r1 L r4 r5 : List (Bt A)) :
    Runs Γ (moveRev 2 3) (R6 r0 r1 L [] r4 r5) (R6 r0 r1 [] L.reverse r4 r5) (8 * L.length + 3) := by
  obtain ⟨s, hr, h2, h3, ho⟩ := moveRev_runs (A := A) (src := 2) (dst := 3) (by norm_num) Γ
    (R6 r0 r1 L [] r4 r5)
  have e : s = R6 r0 r1 [] L.reverse r4 r5 := by
    apply R6_ext
    · rw [ho 0 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 1 (by norm_num) (by norm_num)]; simp [R6]
    · exact h2
    · rw [h3]; simp [R6]
    · rw [ho 4 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 5 (by norm_num) (by norm_num)]; simp [R6]
    · intro k hk
      rw [ho k (by omega) (by omega)]
      simp [R6, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
        show k ≠ 4 by omega, show k ≠ 5 by omega]
  rw [← e]
  have hl : (R6 (A := A) r0 r1 L [] r4 r5 2).length = L.length := by simp [R6]
  rw [hl] at hr; exact hr

theorem move24_runs (Γ : Scope (Bt A)) (r0 r1 L r3 r5 : List (Bt A)) :
    Runs Γ (moveRev 2 4) (R6 r0 r1 L r3 [] r5) (R6 r0 r1 [] r3 L.reverse r5) (8 * L.length + 3) := by
  obtain ⟨s, hr, h2, h4, ho⟩ := moveRev_runs (A := A) (src := 2) (dst := 4) (by norm_num) Γ
    (R6 r0 r1 L r3 [] r5)
  have e : s = R6 r0 r1 [] r3 L.reverse r5 := by
    apply R6_ext
    · rw [ho 0 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 1 (by norm_num) (by norm_num)]; simp [R6]
    · exact h2
    · rw [ho 3 (by norm_num) (by norm_num)]; simp [R6]
    · rw [h4]; simp [R6]
    · rw [ho 5 (by norm_num) (by norm_num)]; simp [R6]
    · intro k hk
      rw [ho k (by omega) (by omega)]
      simp [R6, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
        show k ≠ 4 by omega, show k ≠ 5 by omega]
  rw [← e]
  have hl : (R6 (A := A) r0 r1 L r3 [] r5 2).length = L.length := by simp [R6]
  rw [hl] at hr; exact hr

theorem move25_runs (Γ : Scope (Bt A)) (r0 r1 L r3 r4 : List (Bt A)) :
    Runs Γ (moveRev 2 5) (R6 r0 r1 L r3 r4 []) (R6 r0 r1 [] r3 r4 L.reverse) (8 * L.length + 3) := by
  obtain ⟨s, hr, h2, h5, ho⟩ := moveRev_runs (A := A) (src := 2) (dst := 5) (by norm_num) Γ
    (R6 r0 r1 L r3 r4 [])
  have e : s = R6 r0 r1 [] r3 r4 L.reverse := by
    apply R6_ext
    · rw [ho 0 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 1 (by norm_num) (by norm_num)]; simp [R6]
    · exact h2
    · rw [ho 3 (by norm_num) (by norm_num)]; simp [R6]
    · rw [ho 4 (by norm_num) (by norm_num)]; simp [R6]
    · rw [h5]; simp [R6]
    · intro k hk
      rw [ho k (by omega) (by omega)]
      simp [R6, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
        show k ≠ 4 by omega, show k ≠ 5 by omega]
  rw [← e]
  have hl : (R6 (A := A) r0 r1 L r3 r4 [] 2).length = L.length := by simp [R6]
  rw [hl] at hr; exact hr

/-! ## Unpacking `(ok, x, u, γ)` -/

def unpack (f : Bool → A) : Prog (Bt A) :=
  .join (.pop 0) (.join flagProg (.join (.pop 0) (.join (.pop 0)
    (.join (readList f 2) (.join (moveRev 2 3) (.join (.pop 0)
    (.join (readList f 2) (.join (moveRev 2 4) (.join (readList f 2) (moveRev 2 5))))))))))

theorem spell_tuple (ok : Bool) (x u γ : List Bool) :
    (send (ok, x, u, γ)).spell =
      Ltr.node :: Ltr.bit ok :: Ltr.node :: (spellL x ++ Ltr.node :: (spellL u ++ spellL γ)) := by
  rfl

theorem unpack_runs (f : Bool → A) (Γ : Scope (Bt A)) (ok : Bool) (x u γ : List Bool) :
    Runs Γ (unpack f) (R6 ((send (ok, x, u, γ)).spell.map Sum.inl) [] [] [] [] [])
      (R6 [] [.inl (.bit ok)] [] (x.map fun b => Sum.inr (f b)) (u.map fun b => Sum.inr (f b))
        (γ.map fun b => Sum.inr (f b)))
      (20 * (x.length + u.length + γ.length) + 60) := by
  rw [spell_tuple]
  simp only [List.map_cons, List.map_append]
  have s1 := pop0_runs (A := A) Γ (.inl .node) (.inl (.bit ok) :: .inl .node ::
    ((spellL x).map Sum.inl ++ .inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl))) [] [] [] [] []
  have s2 := flag_runs (A := A) Γ ok (.inl .node ::
    ((spellL x).map Sum.inl ++ .inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl))) [] [] [] []
  have s3 := pop0_runs (A := A) Γ (.inl (.bit ok)) (.inl .node ::
    ((spellL x).map Sum.inl ++ .inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl)))
    [.inl (.bit ok)] [] [] [] []
  have s4 := pop0_runs (A := A) Γ (.inl .node)
    ((spellL x).map Sum.inl ++ .inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl))
    [.inl (.bit ok)] [] [] [] []
  have s5 := read2_runs f Γ x (.inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl))
    [.inl (.bit ok)] [] [] []
  have s6 := move23_runs Γ (.inl .node :: ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl))
    [.inl (.bit ok)] (x.reverse.map fun b => Sum.inr (f b)) [] []
  have s7 := pop0_runs (A := A) Γ (.inl .node) ((spellL u).map Sum.inl ++ (spellL γ).map Sum.inl)
    [.inl (.bit ok)] [] ((x.reverse.map fun b => Sum.inr (f b)).reverse) [] []
  have s8 := read2_runs f Γ u ((spellL γ).map Sum.inl) [.inl (.bit ok)]
    ((x.reverse.map fun b => Sum.inr (f b)).reverse) [] []
  have s9 := move24_runs Γ ((spellL γ).map Sum.inl) [.inl (.bit ok)] (u.reverse.map fun b => Sum.inr (f b))
    ((x.reverse.map fun b => Sum.inr (f b)).reverse) []
  have s10 := read2_runs f Γ γ [] [.inl (.bit ok)]
    ((x.reverse.map fun b => Sum.inr (f b)).reverse) ((u.reverse.map fun b => Sum.inr (f b)).reverse) []
  have s11 := move25_runs Γ [] [.inl (.bit ok)] (γ.reverse.map fun b => Sum.inr (f b))
    ((x.reverse.map fun b => Sum.inr (f b)).reverse) ((u.reverse.map fun b => Sum.inr (f b)).reverse)
  rw [List.append_nil] at s10
  have all := Runs.join s1 (Runs.join s2 (Runs.join s3 (Runs.join s4 (Runs.join s5 (Runs.join s6
    (Runs.join s7 (Runs.join s8 (Runs.join s9 (Runs.join s10 s11)))))))))
  simp only [List.map_reverse, List.reverse_reverse, List.length_reverse, List.length_map] at all
  refine all.mono ?_
  omega

end P1Wrap.W3.Inner
