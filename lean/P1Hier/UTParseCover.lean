import P1Hier.UTParseRead

/-! Finite zero completion. A word either already contains a whole code or can
itself be finished with a bounded number of zeros. A list reserves one extra zero
to terminate the list when its last item was incomplete. -/

namespace P1Hier.AstraParse

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

def zeros (n : ℕ) : Bits := List.replicate n false

theorem zeros_add (m n : ℕ) : zeros (m + n) = zeros m ++ zeros n :=
  List.replicate_append_replicate.symm

theorem zeros_succ (n : ℕ) : zeros (n + 1) = false :: zeros n :=
  List.replicate_succ

theorem zeros_length (n : ℕ) : (zeros n).length = n := List.length_replicate

def CompleteAt {α : Type} (s : α → Bits) (K : ℕ) (x : Bits) : Prop :=
  (∃ a z, x = s a ++ z) ∨ (∃ a n, n ≤ K ∧ x ++ zeros n = s a)

def Complete {α : Type} (s : α → Bits) (K : ℕ) : Prop := ∀ x, CompleteAt s K x

namespace CompleteAt

variable {α β : Type} {s : α → Bits} {t : β → Bits} {K L : ℕ} {x : Bits}

theorem weaken (h : CompleteAt s K x) (hl : K ≤ L) : CompleteAt s L x := by
  rcases h with h | ⟨a, n, hn, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, n, hn.trans hl, he⟩

theorem prefixed (h : CompleteAt s K x) (u : Bits) (f : α → β)
    (he : ∀ a, t (f a) = u ++ s a) : CompleteAt t K (u ++ x) := by
  rcases h with ⟨a, z, h⟩ | ⟨a, n, hn, h⟩
  · exact Or.inl ⟨f a, z, by simp only [he, h, List.append_assoc]⟩
  · exact Or.inr ⟨f a, n, hn, by simp only [he, List.append_assoc, h]⟩

end CompleteAt

namespace Complete

variable {α β : Type} {s : α → Bits} {t : β → Bits} {A B : ℕ}

theorem via (hs : Complete s A) (f : α → β) (he : ∀ a, t (f a) = s a) :
    Complete t A := by
  intro x
  rcases hs x with ⟨a, z, h⟩ | ⟨a, n, hn, h⟩
  · exact Or.inl ⟨f a, z, by simpa only [he] using h⟩
  · exact Or.inr ⟨f a, n, hn, h.trans (he a).symm⟩

theorem from_empty (hs : Complete s A) : ∃ a n, n ≤ A ∧ zeros n = s a := by
  rcases hs [] with ⟨a, z, h⟩ | ⟨a, n, hn, h⟩
  · have hl := congrArg List.length h
    simp only [List.length_nil, List.length_append] at hl
    have he : s a = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨a, 0, Nat.zero_le _, he.symm⟩
  · exact ⟨a, n, hn, h⟩

theorem unit : Complete unitWord 0 :=
  fun x => Or.inl ⟨(), x, rfl⟩

theorem bit : Complete bitWord 1 := by
  intro w
  cases w with
  | nil => exact Or.inr ⟨false, 1, le_rfl, rfl⟩
  | cons b z => exact Or.inl ⟨b, z, rfl⟩

theorem prod (hs : Complete s A) (ht : Complete t B) : Complete (prodWord s t) (A + B) := by
  intro x
  rcases hs x with ⟨a, z, hx⟩ | ⟨a, m, hm, hx⟩
  · rw [hx]
    exact ((ht z).prefixed (t := prodWord s t) (s a) (Prod.mk a) (fun _ => rfl)).weaken
      (by omega)
  · obtain ⟨b, n, hn, hb⟩ := ht.from_empty
    refine Or.inr ⟨(a, b), m + n, by omega, ?_⟩
    change x ++ zeros (m + n) = s a ++ t b
    rw [zeros_add, ← List.append_assoc, hx, hb]

theorem sum (hs : Complete s A) (ht : Complete t B) :
    Complete (sumWord s t) (A + B + 1) := by
  intro w
  cases w with
  | nil =>
    obtain ⟨a, n, hn, he⟩ := hs.from_empty
    exact Or.inr ⟨Sum.inl a, n + 1, by omega, by
      simp only [List.nil_append, zeros_succ, he, sumWord]⟩
  | cons b w =>
    cases b with
    | false =>
      exact ((hs w).prefixed (t := sumWord s t) [false] Sum.inl (fun _ => rfl)).weaken (by omega)
    | true =>
      exact ((ht w).prefixed (t := sumWord s t) [true] Sum.inr (fun _ => rfl)).weaken (by omega)

theorem option (hs : Complete s A) : Complete (optionWord s) (A + 1) := by
  intro w
  cases w with
  | nil => exact Or.inr ⟨none, 1, by omega, rfl⟩
  | cons b w =>
    cases b with
    | false => exact Or.inl ⟨none, w, rfl⟩
    | true =>
      exact ((hs w).prefixed (t := optionWord s) [true] some (fun _ => rfl)).weaken (by omega)

theorem list (hs : Complete s A) : Complete (serL s) (A + 1) := by
  have aux : ∀ (n : ℕ) (x : Bits), x.length = n → CompleteAt (serL s) (A + 1) x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn
      cases x with
      | nil => exact Or.inr ⟨[], 1, by omega, rfl⟩
      | cons b w =>
        cases b with
        | false => exact Or.inl ⟨[], w, rfl⟩
        | true =>
          rcases hs w with ⟨a, z, hw⟩ | ⟨a, m, hm, hw⟩
          · have hz : z.length < n := by
              rw [← hn, hw, List.length_cons, List.length_append]
              omega
            rw [hw]
            exact (ih z.length hz z rfl).prefixed (true :: s a) (List.cons a)
              (fun as => serL_cons s a as)
          · refine Or.inr ⟨[a], m + 1, by omega, ?_⟩
            rw [serL_cons, serL_nil, List.cons_append, zeros_add, ← List.append_assoc, hw]
            <;> rfl
  exact fun x => aux x.length x rfl

theorem padded_exists (hs : Complete s A) (x : Bits) :
    ∃ p : α × Bits, x ++ zeros A = s p.1 ++ p.2 := by
  rcases hs x with ⟨a, z, h⟩ | ⟨a, n, hn, h⟩
  · exact ⟨(a, z ++ zeros A), by simp only [h, List.append_assoc]⟩
  · refine ⟨(a, zeros (A - n)), ?_⟩
    have hz : zeros A = zeros n ++ zeros (A - n) :=
      (congrArg zeros (show A = n + (A - n) by omega)).trans (zeros_add _ _)
    rw [hz, ← List.append_assoc, h]

end Complete

variable {α : Type} {s : α → Bits} {K : ℕ}

noncomputable def padded (hs : Complete s K) (x : Bits) : α × Bits :=
  Classical.choose (hs.padded_exists x)

theorem padded_spec (hs : Complete s K) (x : Bits) :
    x ++ zeros K = s (padded hs x).1 ++ (padded hs x).2 :=
  Classical.choose_spec (hs.padded_exists x)

theorem padded_valid (hs : Complete s K) (pf : PF s) (a : α) (z : Bits) :
    padded hs (s a ++ z) = (a, z ++ zeros K) := by
  have h := padded_spec hs (s a ++ z)
  rw [List.append_assoc] at h
  obtain ⟨ha, hz⟩ := pf _ _ _ _ h
  exact Prod.ext ha.symm hz.symm

/-- Cancel a prefix that finishes on the original side of an appended word. -/
private theorem split_prefix (y x u v : Bits) (he : x ++ u = y ++ v)
    (hl : y.length ≤ x.length) : ∃ z, x = y ++ z ∧ v = z ++ u := by
  induction y generalizing x with
  | nil => exact ⟨x, rfl, he.symm⟩
  | cons b y ih =>
    cases x with
    | nil => simp only [List.length_nil, List.length_cons] at hl; omega
    | cons a x =>
      simp only [List.cons_append, List.cons.injEq] at he
      simp only [List.length_cons] at hl
      obtain ⟨z, hx, hv⟩ := ih x he.2 (by omega)
      exact ⟨z, by rw [List.cons_append, he.1, hx], hv⟩

theorem padded_split (hs : Complete s K) (x : Bits) (hk : K ≤ (padded hs x).2.length) :
    ∃ z, x = s (padded hs x).1 ++ z ∧ (padded hs x).2 = z ++ zeros K := by
  have he := padded_spec hs x
  have hl := congrArg List.length he
  simp only [List.length_append, zeros_length] at hl
  exact split_prefix _ _ _ _ he (by omega)

theorem easy_padded [Codec α] (hr : Reads s) (hs : Complete s K) : Easy (padded hs) := by
  have ha : Easy (fun x : Bits => x ++ zeros K) := easy_append easy_id (Easy.const _)
  have hp : Task (fun x : Bits => size (x ++ zeros K)) (fun x => send (x ++ zeros K))
      (fun x => send (padded hs x)) :=
    (hr.task.on (padded hs)).conform (fun x => congrArg size (padded_spec hs x).symm)
      (fun x => congrArg send (padded_spec hs x).symm) (fun _ => rfl)
  obtain ⟨C, hc⟩ := ha.length
  apply Easy.of_bound (Task.compose ha hp) (1 + C)
  intro x
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left (hc x) _

end P1Hier.AstraParse
