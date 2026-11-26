import P1Int.LemmaP

/-!
# Change of alphabet for OpenAI's stack programs (piece B of W3)

* `mapA e d p`: the program `p : Prog A` over the alphabet `B`, letters sent by `e : A → B`; a branch reads a
  `B`-letter back through `d : B → Option A`.
* `run_mapA`: if `d (e x) = some x`, every run of `p` gives a run of `mapA e d p` on the mapped registers, with the
  same cost.
* `paint_self`: the register file `ρ` is its own paint when it agrees with `r` on the renamed registers
  (to start a renamed program, `Prog.Run.rename`, on a larger register file).
-/

namespace P1Wrap

open OAI.Computability.IntegerMultiplication

variable {A B : Type}

/-- Change of alphabet along `e`, with decoding `d` in the branches. -/
def mapA (e : A → B) (d : B → Option A) : Prog A → Prog B
  | .pass => .pass
  | .push i x => .push i (e x)
  | .pop i => .pop i
  | .look i c => .look i (fun o => mapA e d (c (o.bind d)))
  | .join c c' => .join (mapA e d c) (mapA e d c')
  | .tie c => .tie (mapA e d c)
  | .again i => .again i

/-- Registers mapped letter by letter. -/
def mapR (e : A → B) (r : Reg A) : Reg B := fun i => (r i).map e

theorem mapR_update (e : A → B) (r : Reg A) (i : ℕ) (l : List A) :
    mapR e (Function.update r i l) = Function.update (mapR e r) i (l.map e) := by
  funext k
  by_cases h : k = i
  · subst h; simp [mapR]
  · simp [mapR, Function.update_of_ne h]

theorem head_mapR {e : A → B} {d : B → Option A} (hd : ∀ x, d (e x) = some x) (r : Reg A) (i : ℕ) :
    ((mapR e r i).head?).bind d = (r i).head? := by
  unfold mapR
  cases r i with
  | nil => rfl
  | cons x l => simp [hd]

theorem run_mapA {e : A → B} {d : B → Option A} (hd : ∀ x, d (e x) = some x)
    {Γ : Scope A} {c : Prog A} {r : Reg A} {n : ℕ} {s : Reg A} (h : Prog.Run Γ c r n s) :
    Prog.Run (Γ.map (mapA e d)) (mapA e d c) (mapR e r) n (mapR e s) := by
  induction h with
  | @pass G r0 => exact .pass
  | @push G i x r0 =>
    rw [mapR_update]
    exact .push
  | @pop G i r0 =>
    rw [mapR_update]
    have e1 : ((r0 i).tail).map e = (mapR e r0 i).tail := by simp [mapR, List.map_tail]
    rw [e1]
    exact .pop
  | @look G i c0 r0 n0 r1 _ ih =>
    refine .look ?_
    show Prog.Run _ (mapA e d (c0 ((mapR e r0 i).head?.bind d))) _ _ _
    rw [head_mapR hd]
    exact ih
  | join _ _ ih1 ih2 => exact .join ih1 ih2
  | tie _ ih => exact .tie ih
  | @again G i c0 r0 n0 r1 he _ ih =>
    rw [List.map_drop] at ih
    exact .again (by rw [List.getElem?_map, he]; rfl) ih

theorem paint_self {j : ℕ → ℕ} (hj : Function.Injective j) (r ρ : Reg A) (h : ∀ l, ρ (j l) = r l) :
    Prog.paint j r ρ = ρ := by
  funext i
  by_cases hi : ∃ l, i = j l
  · obtain ⟨l, rfl⟩ := hi
    rw [Prog.paint_at hj, h]
  · push_neg at hi
    rw [Prog.paint_else _ _ _ hi]

end P1Wrap
