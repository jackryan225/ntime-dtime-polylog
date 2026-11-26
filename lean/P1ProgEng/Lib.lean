import OAI.Computability.IntegerMultiplication.TMProgram

/-!
# P1ProgEng.Lib: a small run library for OpenAI's register programs `Prog`, over ANY alphabet

Owner: P1-lean-progeng. Pattern of `P1Case1/CoTransProg.lean` (alphabet `Bool`), here generic in the alphabet `A`.

`Runs Γ p r r' B`: the program `p` runs in scope `Γ` from registers `r` to `r'` with cost at most `B`
(OpenAI's `Prog.Run` with its exact cost, `IntegerMultiplication/TMProgram.lean`).
-/

namespace P1ProgEng

open OAI.Computability.IntegerMultiplication

section

variable {A : Type}

/-- `p` runs from `r` to `r'` in scope `Γ` with cost at most `B`. -/
def Runs (Γ : Scope A) (p : Prog A) (r r' : Reg A) (B : ℕ) : Prop := ∃ n, Prog.Run Γ p r n r' ∧ n ≤ B

namespace Runs

variable {Γ : Scope A} {p q : Prog A} {r s t : Reg A} {B B' : ℕ}

theorem mono (h : Runs Γ p r s B) (hB : B ≤ B') : Runs Γ p r s B' := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨n, hr, hn.trans hB⟩

theorem congr_out (h : Runs Γ p r s B) (hs : s = t) : Runs Γ p r t B := hs ▸ h

theorem of_prog {p' : Prog A} (hp : p = p') (h : Runs Γ p' r s B) : Runs Γ p r s B := hp ▸ h

theorem of_run {n : ℕ} (h : Prog.Run Γ p r n s) : Runs Γ p r s n := ⟨n, h, le_rfl⟩

theorem pass : Runs Γ .pass r r 1 := ⟨1, .pass, le_rfl⟩

theorem push (i : ℕ) (x : A) : Runs Γ (.push i x) r (Function.update r i (x :: r i)) 1 :=
  ⟨1, .push, le_rfl⟩

theorem pop (i : ℕ) : Runs Γ (.pop i) r (Function.update r i (r i).tail) 1 := ⟨1, .pop, le_rfl⟩

theorem look {i : ℕ} {c : Option A → Prog A} (h : Runs Γ (c (r i).head?) r s B) :
    Runs Γ (.look i c) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .look hr, by omega⟩

/-- `look` with the value of the head given. -/
theorem look' {i : ℕ} {c : Option A → Prog A} {o : Option A} (ho : (r i).head? = o)
    (h : Runs Γ (c o) r s B) : Runs Γ (.look i c) r s (B + 1) := by
  subst ho; exact look h

theorem join (h1 : Runs Γ p r s B) (h2 : Runs Γ q s t B') : Runs Γ (.join p q) r t (B + B' + 2) := by
  obtain ⟨n, hr, hn⟩ := h1
  obtain ⟨m, hm, hm'⟩ := h2
  exact ⟨1 + n + 1 + m, .join hr hm, by omega⟩

theorem tie {body : Prog A} (h : Runs (body :: Γ) body r s B) : Runs Γ (.tie body) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .tie hr, by omega⟩

theorem again0 {body : Prog A} (h : Runs (body :: Γ) body r s B) :
    Runs (body :: Γ) (.again 0) r s (B + 1) := by
  obtain ⟨n, hr, hn⟩ := h
  exact ⟨1 + n, .again rfl hr, by omega⟩

end Runs

end

end P1ProgEng
