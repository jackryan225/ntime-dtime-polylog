import P1Wit.WitTuple
import OAI.Computability.VPVNP.CompressionState

namespace P1Wit.SolWitfill

open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression

abbrev TermTable (D : Dims) (ℓ : Fin (D.top + 1)) :=
  Fin ((D.lv ℓ.val).bases * (D.lv ℓ.val).termKeys) → TermSlot D (D.lv ℓ.val)

/-- One level's admitted term table in base and key order. A key with no
admitted term has a zero presence flag. -/
noncomputable def termTableOfKeys {D : Dims} {ℓ : Fin (D.top + 1)} {A K : Type*}
    (key : K ↪ Fin ((D.lv ℓ.val).bases * (D.lv ℓ.val).termKeys))
    (localTerms : A ↪ (K → TermSlot D (D.lv ℓ.val))) : A ↪ TermTable D ℓ where
  toFun a := Function.extend key (localTerms a) (fun _ => none)
  inj' := by
    intro a b h
    apply localTerms.injective
    funext k
    have e := congrFun h (key k)
    change Function.extend key (localTerms a) (fun _ => none) (key k) =
      Function.extend key (localTerms b) (fun _ => none) (key k) at e
    simpa only [key.injective.extend_apply] using e

/-- An admitted choice at each local key, represented by the coordinates of
its outer index. The same constructor applies to shrink motifs and refresh
blocks. -/
noncomputable def admittedTermTable {D : Dims} {ℓ : Fin (D.top + 1)} {A K : Type*}
    (key : K ↪ Fin ((D.lv ℓ.val).bases * (D.lv ℓ.val).termKeys))
    (coord : A ≃ Fin (D.lv ℓ.val).termArity) (P : K → (A → ℕ) → Prop)
    (fits : ∀ k f, P k f → ∀ a, f a < 2 ^ D.wW) :
    ((k : K) → {f : A → ℕ // P k f}) ↪ TermTable D ℓ :=
  termTableOfKeys key
    { toFun := fun choices k => some fun j =>
        ⟨(choices k).val (coord.symm j), fits k _ (choices k).property _⟩
      inj' := by
        intro c c' h
        funext k
        apply Subtype.ext
        funext a
        have e := Option.some.inj (congrFun h k)
        have ea := congrArg Fin.val (congrFun e (coord a))
        simpa only [Equiv.symm_apply_apply] using ea }

/-- At each execution node, the current term choices are stored at the
current level. Which later stages are reached depends on those choices. -/
structure HeadTerms (D : Dims) (start : ℕ) (A : Type) where
  in_range : start < D.top + 1
  encode : A ↪ TermTable D ⟨start, in_range⟩

variable {R : Type*} [CommSemiring R] {b n : ℕ}

def ExecutionTerms (D : Dims) {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) (start : ℕ) : Type :=
  match E with
  | .done _ => Unit
  | .more p tail => HeadTerms D start p.step.Choice ×
    ((i : p.step.Choice) → ExecutionTerms D (tail i) (start + 1))

def ExecutionTerms.table {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (T : ExecutionTerms D E start)
    (ι : E.Choices) (ℓ : Fin (D.top + 1)) : TermTable D ℓ :=
  match E with
  | .done _ => fun _ => none
  | .more _ tail =>
    if h : (⟨start, T.1.in_range⟩ : Fin (D.top + 1)) = ℓ then
      h ▸ T.1.encode ι.1
    else
      table (tail ι.1) (T.2 ι.1) ι.2 ℓ

theorem ExecutionTerms.eq_of_table {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (T : ExecutionTerms D E start)
    (ι ι' : E.Choices)
    (h : ∀ ℓ : Fin (D.top + 1), start ≤ ℓ.val → ExecutionTerms.table E T ι ℓ = ExecutionTerms.table E T ι' ℓ) :
    ι = ι' := by
  induction E generalizing start with
  | done =>
    change Unit at ι ι'
    cases ι
    cases ι'
    rfl
  | more p tail ih =>
    rcases ι with ⟨i, z⟩
    rcases ι' with ⟨i', z'⟩
    have hi : i = i' := by
      apply T.1.encode.injective
      simpa only [ExecutionTerms.table, dite_eq_left rfl, dite_true] using
        h ⟨start, T.1.in_range⟩ le_rfl
    subst i'
    congr
    apply ih i (start := start + 1) (T.2 i) z z'
    intro ℓ hℓ
    have hn : (⟨start, T.1.in_range⟩ : Fin (D.top + 1)) ≠ ℓ := by
      intro he
      have hv : start = ℓ.val := congrArg (fun v : Fin (D.top + 1) => v.val) he
      omega
    simpa only [ExecutionTerms.table, dite_eq_right hn] using h ℓ (by omega)

theorem ExecutionTerms.table_injective {D : Dims} {a g : ℕ} {X : State a g}
    (E : StateExecution R b n X) {start : ℕ} (T : ExecutionTerms D E start) :
    Function.Injective (ExecutionTerms.table E T) :=
  fun ι ι' h => ExecutionTerms.eq_of_table E T ι ι' (fun ℓ _ => congrFun h ℓ)

end P1Wit.SolWitfill
