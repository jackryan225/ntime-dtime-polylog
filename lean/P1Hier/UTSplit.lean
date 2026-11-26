import P1Hier.UMachine

/-!
# P1Hier.UTSplit (copy B of lane hier): inputs `h8` and `h1` of `UM.accU_machine_of`

* `size_code_le : ∀ c : MCode, size c ≤ 4 * csz c + 4` (input `h8`): the tree size of a machine
  code against the length of its bit code.
* `easy_unGuess : Easy unGuess` (input `h1`): two finite-state transducers (OpenAI's
  `Easy.machine`) read `withGuess u x` once; one emits the guess bits, the other the input bits.
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

/-! ## `h8`: tree size against bit length -/

theorem length_serN (k : ℕ) : (serN k).length = k + 1 := by
  simp [serN]

theorem length_serL_cons {α : Type*} (f : α → List Bool) (a : α) (l : List α) :
    (serL f (a :: l)).length = (f a).length + (serL f l).length + 1 := by
  rw [serL_cons, List.length_cons, List.length_append]

theorem size_list_le {α : Type*} [Codec α] (f : α → List Bool)
    (hf : ∀ a, size a ≤ 4 * (f a).length + 3) : ∀ l : List α, size l ≤ 4 * (serL f l).length
  | [] => by
    rw [serL_nil, size_nil]
    simp
  | a :: l => by
    rw [size_cons, length_serL_cons]
    have h1 := hf a
    have h2 := size_list_le f hf l
    omega

theorem size_cell_le (x : Cell) : size x ≤ 4 * (serCell x).length + 3 := by
  obtain ⟨a, b, m⟩ := x
  have hm : size m ≤ 3 := by cases m <;> simp
  have hm2 : 1 ≤ (serMv m).length := by cases m <;> simp [serMv]
  simp only [size_prod, size_nat', serCell, List.length_append, length_serN]
  omega

theorem size_res_le (r : ℕ ⊕ Bool) : size r ≤ 4 * (serRes r).length := by
  cases r with
  | inl q =>
    simp only [size_inl, size_nat', serRes, List.length_cons, length_serN]
    omega
  | inr b =>
    simp [serRes]

theorem size_entry_le (e : Entry) : size e ≤ 4 * (serEntry e).length + 3 := by
  obtain ⟨q, cs, r⟩ := e
  have h1 := size_list_le serCell size_cell_le cs
  have h2 := size_res_le r
  simp only [size_prod, size_nat', serEntry, List.length_append, length_serN]
  omega

/-- **Input `h8`.** -/
theorem size_code_le (c : MCode) : size c ≤ 4 * csz c + 4 := by
  have h := size_list_le serEntry size_entry_le c.table
  show size (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table) ≤ 4 * (serCode c).length + 4
  simp only [size_prod, size_nat', serCode, List.length_append, length_serN]
  omega

/-! ## `h1`: splitting `withGuess u x` -/

/-- States: `none` = a tag is next; `some true` = a guess bit is next; `some false` = in `x`.
This transducer emits the guess bits. -/
def stG : Bool → Option Bool → Option Bool × List Bool
  | true, none => (some true, [])
  | false, none => (some false, [])
  | b, some true => (none, [b])
  | _, some false => (some false, [])

/-- Same states; emits the bits of `x`. -/
def stX : Bool → Option Bool → Option Bool × List Bool
  | true, none => (some true, [])
  | false, none => (some false, [])
  | _, some true => (none, [])
  | b, some false => (some false, [b])

theorem machine_fst_cons {X S Y : Type*} (step : X → S → S × List Y) (s : S) (x : X)
    (l : List X) :
    (machine step (x :: l, s)).1 = (step x s).2 ++ (machine step (l, (step x s).1)).1 := by
  rw [machine_cons]

theorem mG_tail : ∀ r : List Bool, (machine stG (r, some false)).1 = []
  | [] => rfl
  | b :: r => by
    rw [machine_fst_cons]
    simp only [stG, List.nil_append]
    exact mG_tail r

theorem mX_tail : ∀ r : List Bool, (machine stX (r, some false)).1 = r
  | [] => rfl
  | b :: r => by
    rw [machine_fst_cons]
    simp only [stX, List.singleton_append]
    rw [mX_tail r]

theorem mG : ∀ y : List Bool, (machine stG (y, none)).1 = (unGuess y).1
  | [] => rfl
  | [true] => rfl
  | true :: b :: r => by
    rw [machine_fst_cons]
    simp only [stG, List.nil_append]
    rw [machine_fst_cons]
    simp only [stG, List.singleton_append, unGuess]
    rw [mG r]
  | false :: r => by
    rw [machine_fst_cons]
    simp only [stG, List.nil_append, unGuess]
    exact mG_tail r

theorem mX : ∀ y : List Bool, (machine stX (y, none)).1 = (unGuess y).2
  | [] => rfl
  | [true] => rfl
  | true :: b :: r => by
    rw [machine_fst_cons]
    simp only [stX, List.nil_append]
    rw [machine_fst_cons]
    simp only [stX, List.nil_append, unGuess]
    exact mX r
  | false :: r => by
    rw [machine_fst_cons]
    simp only [stX, List.nil_append, unGuess]
    exact mX_tail r

/-- **Input `h1`.** -/
theorem easy_unGuess : Easy unGuess := by
  have hg : Easy (fun y : List Bool => (y, (none : Option Bool))) :=
    easy_id.pair (Easy.const none)
  have hG := Easy.machine (step := stG) hg
  have hX := Easy.machine (step := stX) hg
  refine easy_congr ((Easy.fstCompose hG).pair (Easy.fstCompose hX)) (fun y => ?_)
  show send ((machine stG (y, none)).1, (machine stX (y, none)).1) = send (unGuess y)
  rw [mG, mX]

end P1Hier.UM
