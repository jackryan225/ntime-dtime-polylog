import P1Hier.UTSplit
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Code.Iter

/-!
# P1Hier.UTCore (copy B of lane hier): stack-level helpers and unary squaring

* `regroup`: `fork (fork A B) C ↦ fork A (fork B C)` at cost `O(|A|)` (two moves of `A`).
* `leftCase`: a branch on the root-left child (an atom, or a fork) at constant cost.
* `sqT`: `n ↦ n²` on unary numbers with budget `n²` (OpenAI's `generate`, then `flatten`).
* `easy_le`: `decide (a ≤ b)` on unary numbers (OpenAI's `Iter.small_easy`).
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

section Stack
variable {X : Type*}

/-- Re-associate a pair: the left part `A` is moved twice (cost linear in `A` only). -/
theorem regroup (A B C : X → Tree) :
    Task (fun x => (A x).count) (fun x => Tree.fork (Tree.fork (A x) (B x)) (C x))
      (fun x => Tree.fork (A x) (Tree.fork (B x) (C x))) := by
  refine ⟨splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((pack 0).join ((move 1 0 2).join (pack 0))))), 110,
    fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (A x) env
    (pile 0 (B x) (pile 0 (C x) r))
  rw [pile_comm 1 (A x) (pile 0 (C x) r) 0 (B x) (by decide),
    pile_comm 1 (A x) r 0 (C x) (by decide)] at h₁
  have h₂ := fits_pack (B x) (C x) (pile 1 (A x) r) 0 env
  rw [pile_comm 0 (Tree.fork (B x) (C x)) r 1 (A x) (by decide)] at h₂
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (A x) env
    (pile 0 (Tree.fork (B x) (C x)) r)
  have h₄ := fits_pack (A x) (Tree.fork (B x) (C x)) r 0 env
  refine (fits_pair (fits_pair (h₁.join (h₂.join (h₃.join h₄))))).mono ?_
  show _ ≤ 110 * ((A x).count + 1)
  omega

/-- Branch on the root-left child of the query: an atom (its value is dropped and the
branch `ha` runs on the right child) or a fork (the branch `hf` runs on the whole query). -/
theorem leftCase (isA : X → Bool) {a : X → ℕ} (L R q : X → Tree)
    (hA : ∀ x, isA x = true → ∃ b, L x = Tree.atom b)
    (hF : ∀ x, isA x = false → ∃ l₁ l₂, L x = Tree.fork l₁ l₂)
    (ha : Task (fun x : {x // isA x = true} => a x.val) (fun x => R x.val) (fun x => q x.val))
    (hf : Task (fun x : {x // isA x = false} => a x.val)
      (fun x => Tree.fork (L x.val) (R x.val)) (fun x => q x.val)) :
    Task a (fun x => Tree.fork (L x) (R x)) q := by
  obtain ⟨c, C, hc⟩ := ha
  obtain ⟨d, D, hd⟩ := hf
  refine ⟨splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun _ => c) ((pack 0).join ((pack 0).join d))), C + D + 20,
    fun x env r => ?_⟩
  cases e : isA x with
  | false =>
    obtain ⟨l₁, l₂, hl⟩ := hF x e
    have h : Fits env d (pile 0 (Tree.fork (L x) (R x)) r) (pile 0 (q x) r) (D * (a x + 1)) :=
      hd ⟨x, e⟩ env r
    show Fits env _ (pile 0 (Tree.fork (L x) (R x)) r) (pile 0 (q x) r) ((C + D + 20) * (a x + 1))
    rw [hl] at h ⊢
    have h₁ := fits_pack l₁ l₂ (pile 0 (R x) r) 0 env
    have h₂ := fits_pack (Tree.fork l₁ l₂) (R x) r 0 env
    refine (fits_pair (fits_pair (h₁.join (h₂.join h)))).mono ?_
    rw [Nat.add_mul, Nat.add_mul]
    omega
  | true =>
    obtain ⟨b, hb⟩ := hA x e
    have h : Fits env c (pile 0 (R x) r) (pile 0 (q x) r) (C * (a x + 1)) := hc ⟨x, e⟩ env r
    show Fits env _ (pile 0 (Tree.fork (L x) (R x)) r) (pile 0 (q x) r) ((C + D + 20) * (a x + 1))
    rw [hb]
    refine (fits_pair (fits_bit (c := fun _ => c) h)).mono ?_
    rw [Nat.add_mul, Nat.add_mul]
    omega

end Stack

/-! ## Unary numbers -/

theorem send_nat (n : ℕ) : send n = send (tally n) := rfl

theorem size_replicate {α : Type*} [Codec α] (k : ℕ) (a : α) :
    size (List.replicate k a) = k * (size a + 1) + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, size_cons, ih]
    ring

theorem tally_eq (l : Tally) : l = tally l.length := by
  rw [tally, List.eq_replicate_iff]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- **Unary squaring** with budget `n²`. -/
theorem sqT : Computes (fun n : ℕ => n ^ 2) (fun n : ℕ => n ^ 2) := by
  have h1 : Easy (fun n : ℕ => (tally n, tally n)) := easy_tally.pair easy_tally
  have c1 := Computes.comp (generate (X := Tally)) h1
  have c2 := Computes.comp (Easy.flatten (X := Unit)) c1
  refine (Task.bound (b' := fun n : ℕ => n ^ 2) c2 20 (fun n => ?_)).conform (fun _ => rfl)
    (fun _ => rfl) (fun n => ?_)
  · show size n + ((tally n).length + 1) * size (tally n) +
        size (List.replicate (tally n).length (tally n)) + 1 ≤ 20 * (n ^ 2 + 1)
    rw [size_replicate, size_tally, tally_length, size_nat']
    have hn : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) _
    have e1 : (n + 1) * (2 * n + 1) = 2 * n ^ 2 + 3 * n + 1 := by ring
    have e2 : n * (2 * n + 1 + 1) = 2 * n ^ 2 + 2 * n := by ring
    omega
  · show send ((List.replicate (tally n).length (tally n)).flatten) = send (tally (n ^ 2))
    simp only [tally, List.length_replicate, List.flatten_replicate_replicate, sq]

/-- `decide (a ≤ b)` on unary numbers. -/
theorem easy_le : Easy (fun i : ℕ × ℕ => decide (i.1 ≤ i.2)) := by
  have hs : Easy (fun i : ℕ × ℕ => tally i.2) := (Easy.snd (X := ℕ) (Y := ℕ)).compose easy_tally
  have hf : Easy (fun i : ℕ × ℕ => tally i.1) := (Easy.fst (X := ℕ) (Y := ℕ)).compose easy_tally
  have h : Easy (fun i : ℕ × ℕ => !Iter.small (tally i.2, tally i.1)) :=
    ((hs.pair hf).compose Iter.small_easy).compose Iter.negate
  refine easy_congr h (fun i => congrArg send ?_)
  rw [Bool.eq_iff_iff]
  simp [Iter.small, tally_length]

end P1Hier.UM
