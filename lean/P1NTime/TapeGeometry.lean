import P1NTime.Composite

namespace P1NTime.AstraNTime.Composite

open C1Challenge Turing

section Tape

variable {A : Type} [Inhabited A]

/-- The left list is in nearest-first order. The right list starts under the head. -/
def cursor (f : Bool → A) (L R : List Bool) : Tape A := Tape.mk₂ (L.map f) (R.map f)

def back (f : Bool → A) (L R : List Bool) : Tape A := (cursor f L R).move .left

theorem act_right (t : Tape A) : act t (t.head, .right) = t.move .right :=
  congrArg (Tape.move .right) (Tape.write_self t)

theorem act_left (t : Tape A) : act t (t.head, .left) = t.move .left :=
  congrArg (Tape.move .left) (Tape.write_self t)

variable (f : Bool → A)

theorem cursor_head (L R : List Bool) (b : Bool) : (cursor f L (b :: R)).head = f b := rfl

theorem cursor_head_nil (L : List Bool) : (cursor f L []).head = default := rfl

theorem cursor_right (L R : List Bool) (b : Bool) :
    (cursor f L (b :: R)).move .right = cursor f (b :: L) R := rfl

theorem back_cons (L R : List Bool) (b : Bool) : back f (b :: L) R = cursor f L (b :: R) :=
  Tape.move_left_mk' (ListBlank.mk (f b :: L.map f)) (ListBlank.mk (R.map f))

theorem back_nil (R : List Bool) : back f [] R = Tape.mk₂ [] (default :: R.map f) :=
  Tape.move_left_mk' (ListBlank.mk ([] : List A)) (ListBlank.mk (R.map f))

theorem back_head_nil (R : List Bool) : (back f [] R).head = default := rfl

theorem back_right (L R : List Bool) : (back f L R).move .right = cursor f L R :=
  Tape.move_left_right _

theorem back_left (L R : List Bool) (b : Bool) :
    (back f (b :: L) R).move .left = back f L (b :: R) :=
  congrArg (Tape.move .left) (back_cons f L R b)

theorem blank_list : ListBlank.mk ([default] : List A) = ListBlank.mk [] := by
  apply Quotient.sound'
  exact Or.inr ⟨1, rfl⟩

theorem back_empty : back f [] [] = Tape.mk₁ [] := by
  exact (back_nil f []).trans (congrArg (Tape.mk' (ListBlank.mk ([] : List A))) blank_list)

theorem back_push (b : Bool) (R : List Bool) :
    act (back f [] R) (f b, .left) = back f [] (b :: R) := by
  change ((back f [] R).write (f b)).move .left = (cursor f [] (b :: R)).move .left
  apply congrArg (Tape.move .left)
  exact (congrArg (fun t : Tape A => t.write (f b)) (back_nil f R)).trans rfl

/-- Erasing a consumed cell keeps the entire left side blank. -/
theorem erase_right (b : Bool) (R : List Bool) :
    act (cursor f [] (b :: R)) (default, .right) = cursor f [] R := by
  change Tape.mk₂ [default] (R.map f) = Tape.mk₂ [] (R.map f)
  exact congrArg (fun L => Tape.mk' L (ListBlank.mk (R.map f))) blank_list

end Tape

/-- During setup every tape other than the designated input of each machine is blank. -/
def bank (M : Machine) (t : Tape M.Γ) : Tapes M := fun k =>
  if k = M.inputTape then t else Tape.mk₁ []

def pending (M : Machine) (z : List Bool) : Tapes M := bank M (back M.inputSymbol [] z)

theorem update_atInput_bank (M : Machine) (t : Tape M.Γ) (a : Op M.Γ) :
    updateBank (bank M t) (atInput M (heads (bank M t)) a) = bank M (act t a) := by
  funext k
  by_cases hk : k = M.inputTape
  · simp only [updateBank, atInput, bank, ite_eq_left hk]
  · simp only [updateBank, atInput, ite_eq_right hk, heads, act_hold, bank]

theorem pending_nil (M : Machine) (k : M.K) : pending M [] k = Tape.mk₁ [] := by
  simp only [pending, bank, back_empty, ite_self]

theorem update_push (M : Machine) (b : Bool) (z : List Bool) :
    updateBank (pending M z)
        (atInput M (heads (pending M z)) (M.inputSymbol b, .left)) = pending M (b :: z) := by
  simp only [pending, update_atInput_bank, back_push]

theorem update_install (M : Machine) (z : List Bool) :
    updateBank (pending M z)
        (atInput M (heads (pending M z)) (heads (pending M z) M.inputTape, .right)) =
      (M.init z).tapes := by
  have h : heads (pending M z) M.inputTape = (back M.inputSymbol [] z).head := by
    simp [heads, pending, bank]
  rw [h]
  change updateBank (bank M _) (atInput M (heads (bank M _)) _) =
    bank M (cursor M.inputSymbol [] z)
  rw [update_atInput_bank, act_right, back_right]

end P1NTime.AstraNTime.Composite
