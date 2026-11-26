import P1C1U.Resolve
import P1Hier.Spec

namespace P1C1U.AstraC1U.Rows

open C1Challenge P1Hier
noncomputable section

abbrev base (M : NMachine) := resolve M none

local instance (M : NMachine) : Fintype (Choice M) := Fintype.ofFinite _

/-- Combine the rows of all deterministic resolutions. The checker tests membership in this table. -/
def ncode (M : NMachine) : MCode :=
  { P1Hier.code (base M) with
    table := (Finset.univ : Finset (Choice M)).toList.flatMap fun p =>
      (P1Hier.code (resolve M p)).table }

theorem table_mem (M : NMachine) (e : Entry) :
    e ∈ (ncode M).table ↔ ∃ p : Choice M, e ∈ (P1Hier.code (resolve M p)).table := by
  simp only [ncode, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]

def row (M : NMachine) (c : Conf M) (o : Choice M) : Entry :=
  (encQ (base M) c.q, cellsOf (base M) (M.scanned c) o, match o with
   | none => Sum.inr (M.accept c.q)
   | some v => Sum.inl (encQ (base M) v.1))

theorem row_resolve (M : NMachine) (p : Choice M) (c : Conf M) :
    rowOf (resolve M p) c = row M c (pick (M.code c.q (M.scanned c)) p) := by
  unfold NMachine.scanned
  cases hv : pick (M.code c.q (fun k : M.K => (c.tapes k).head)) p <;>
    simp only [rowOf, entry, row, base, resolve, NMachine.scanned, hv] <;> rfl

theorem row_mem_some {M : NMachine} {c : Conf M} {o : Out M}
    (h : o ∈ M.code c.q (M.scanned c)) : row M c (some o) ∈ (ncode M).table := by
  apply (table_mem M _).mpr
  refine ⟨some o, ?_⟩
  have hm := rowOf_mem (resolve M (some o)) c
  rwa [row_resolve, pick_of_mem h] at hm

theorem row_mem_halt {M : NMachine} {c : Conf M} (h : M.Halted c) :
    row M c none ∈ (ncode M).table := by
  apply (table_mem M _).mpr
  refine ⟨none, ?_⟩
  have hm := rowOf_mem (base M) c
  have hp := (pick_none_iff (M.code c.q (M.scanned c)) (none : Choice M)).mpr h
  change rowOf (resolve M none) c ∈ _ at hm
  rwa [row_resolve, hp] at hm

private theorem encMv_injective : Function.Injective encMv := by
  intro a b h
  cases a <;> cases b <;> simp_all [encMv]

/-- The successor state and all write and move fields recover the transition at a fixed source. -/
theorem row_some_inj (M : NMachine) (c : Conf M) {o v : Out M}
    (h : row M c (some o) = row M c (some v)) : o = v := by
  have hstate : (Sum.inl (encQ (base M) o.1) : ℕ ⊕ Bool) = Sum.inl (encQ (base M) v.1) :=
    congrArg (fun e : Entry => e.2.2) h
  have hs : cellsOf (base M) (M.scanned c) (some o) =
      cellsOf (base M) (M.scanned c) (some v) := congrArg (fun e : Entry => e.2.1) h
  have hc (k : M.K) : cellOf (base M) (M.scanned c) (some o) k =
      cellOf (base M) (M.scanned c) (some v) k := by
    have hh := congrArg (fun es : List Cell => es.getD (eK (base M) k) (0, 0, none)) hs
    exact (cellsOf_getD (base M) (M.scanned c) (some o) k (0, 0, none)).symm.trans
      (hh.trans (cellsOf_getD (base M) (M.scanned c) (some v) k (0, 0, none)))
  apply Prod.ext
  · exact encQ_injective (base M) (Sum.inl.inj hstate)
  · apply Prod.ext
    · funext k
      exact encG_injective (base M) (congrArg (fun z : Cell => z.2.1) (hc k))
    · funext k
      exact encMv_injective (congrArg (fun z : Cell => z.2.2) (hc k))

/-- The final row records the halting answer. The earlier rows record the ordered transitions. -/
def rows (M : NMachine) : Conf M → List (Out M) → List Entry
  | c, [] => [row M c none]
  | c, o :: os => row M c (some o) :: rows M (M.apply c o) os

theorem rows_mem (M : NMachine) : ∀ (os : List (Out M)) (c : Conf M),
    M.Run c os → M.Halted (M.after c os) → ∀ e ∈ rows M c os, e ∈ (ncode M).table
  | [], c, _, hh, e, he => by
    have he' : e = row M c none := List.mem_singleton.mp he
    rw [he']
    exact row_mem_halt hh
  | o :: os, c, hr, hh, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact row_mem_some hr.1
    · exact rows_mem M os (M.apply c o) hr.2 hh e he

theorem length_rows (M : NMachine) : ∀ (os : List (Out M)) (c : Conf M),
    (rows M c os).length = os.length + 1
  | [], _ => rfl
  | o :: os, c => by
    rw [rows, List.length_cons, length_rows M os (M.apply c o), List.length_cons]

theorem eq_of_rows_eq (M : NMachine) : ∀ (os vs : List (Out M)) (c : Conf M),
    rows M c os = rows M c vs → os = vs
  | [], [], _, _ => rfl
  | [], v :: vs, c, h => by
    have hl := congrArg List.length h
    simp only [length_rows, List.length_nil, List.length_cons] at hl
    omega
  | o :: os, [], c, h => by
    have hl := congrArg List.length h
    simp only [length_rows, List.length_nil, List.length_cons] at hl
    omega
  | o :: os, v :: vs, c, h => by
    obtain ⟨hh, ht⟩ := List.cons.inj h
    obtain rfl := row_some_inj M c hh
    exact congrArg (List.cons o) (eq_of_rows_eq M os vs (M.apply c o) ht)

/-- A row that passes the head and state checks belongs to a resolution at the actual configuration. -/
theorem checked_head (M : NMachine) (c : Conf M) (ts : ℕ → Tp) (e : Entry) (rest : List Entry)
    (rep : ∀ k : M.K, absT (base M) (ts (eK (base M) k)) = c.tapes k)
    (good : ∀ k : M.K, Good (base M) (ts (eK (base M) k)))
    (he : e ∈ (ncode M).table)
    (chain : chainOK (encQ (base M) c.q) (e :: rest) = true)
    (cols : ∀ k < Fintype.card M.K, colOK (ts k) (col k (e :: rest)) = true) :
    ∃ p : Choice M, e = row M c (pick (M.code c.q (M.scanned c)) p) := by
  obtain ⟨p, hp⟩ := (table_mem M e).mp he
  exact ⟨p, (P1Hier.head_row (resolve M p) c ts rep good e rest hp chain cols).trans
    (row_resolve M p c)⟩

end
end P1C1U.AstraC1U.Rows

#print axioms P1C1U.AstraC1U.Rows.checked_head
#print axioms P1C1U.AstraC1U.Rows.eq_of_rows_eq
