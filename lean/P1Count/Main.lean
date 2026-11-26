import P1Count.Concrete
import P1Count.Dispatch

/-!
# P1Count.Main: the P9 count in the form of `P1Int.LemmaP` (lane P1-lean-W2-count)

The count of `P1Count.Concrete` joined with the dispatcher `P1Count.R` of `P1Count.Dispatch`.
For one input `x`: the language bit is the parity of the witnesses `u : Fin m → Bool` on which `R` answers
`true` for every selector `γ : Fin k → Bool` within `4 d + bnd` steps. This is the parity clause of
`P1Int.LemmaP` (with `inputRegs letter x (List.ofFn u) (List.ofFn γ)`); P11 adds the totality clause
from `P1Count.R_total`, the bound `4 d + bnd ≤ lpCost2 ..`, and the lengths `m = lpM2`, `k = lpK2`.

Hypotheses (what the other lanes supply):
* count data (`NetData`, P4 `hP4`, P5 `hP5`, P0 `b`, `l`, `hl`), see `P1Count.Concrete`;
* `hL` (P4 + `P1Net.sum_card_skeleton` + `P1Int.parDecides_oai`): `Lx ↔ Odd (∑ σ, acc σ)`;
* `enc`, `hinj` (P6): the witness encoding of the tuples `(σ, ι, z, chain)` is injective;
* `hchecks` (checker lanes C1-C14, the chain ends, `lem:unique`): the witnesses on which every check program
  `chk c` (`c < 2 ^ d`) answers `true` for every index of length `k - d` are exactly the encodings of the
  valid tuples. `lemmaP_count_of_stages` derives it from stage lemmas (`P1Count.stages_iff`).
-/

namespace P1Count

open Module
open OAI.Computability.IntegerMultiplication P1Int
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.VPVNP.WireTensor

noncomputable section

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] (C : NetData F) {D : ℕ}
  (b : Basis (Fin D) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hl : l 1 = 1)
  (Xn : C.Sk → Network) (F1 : ∀ σ, Factors F (Xn σ)) (s : ∀ σ, (Xn σ).Site)
  (e : ∀ σ, (Xn σ).Site → F) (he : ∀ σ u, u ≠ s σ → e σ u = 1)
  (hes : ∀ σ, e σ (s σ) = (2 : F) ^ C.unowned σ)
  {A : Type} (bit : Option A → Bool) (letter : Bool → A) (hbit : ∀ b, bit (some (letter b)) = b)
  (answer : Option A → Bool) (hacc : answer (some (letter true)) = true)
  (d : ℕ) (chk : ℕ → Option (Prog A)) (k : ℕ) (hk : d ≤ k) (bnd : ℕ) (hb : 1 ≤ bnd)
  (x : List Bool) {m : ℕ} (enc : C.toCountData.Tup D → (Fin m → Bool)) (hinj : Function.Injective enc)
include hl he hes hbit hacc hk hb hinj

open scoped Classical in
/-- **P9 (1) + (3): the count of Lemma P.** -/
theorem lemmaP_count
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
    (hchecks : ∀ u : Fin m → Bool,
      (∀ c < 2 ^ d, ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd) ↔
      ∃ t, C.toCountData.Valid b l t ∧ enc t = u)
    (Lx : Prop) (hL : Lx ↔ Odd (∑ σ, C.acc σ)) :
    Lx ↔ Odd (Finset.univ.filter fun u : Fin m → Bool =>
      ∀ γ : Fin k → Bool, ProgAnswers (R bit letter d chk) answer
        (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true (4 * d + bnd)).card := by
  refine C.lang_iff b l hl Xn F1 s e he hes hP4 hP5 _ enc hinj ?_ Lx hL
  intro u
  rw [forall_ofFn_iff (fun γ => ProgAnswers (R bit letter d chk) answer
      (inputRegs letter x (List.ofFn u) γ) true (4 * d + bnd)),
    R_forall_iff_fam bit letter hbit answer d chk x (List.ofFn u) k hk bnd hb hacc]
  exact hchecks u

open scoped Classical in
/-- **The same count from stage lemmas.** `Stage c u`: every program of family `c` answers `true` on `u` for
every index. `Tr c u`: the first `c` groups of fields of `u` hold their true values (`lem:unique`).
The families are numbered `0, …, 2 ^ d - 1` (families without a check accept). -/
theorem lemmaP_count_of_stages
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
    (Tr : ℕ → (Fin m → Bool) → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ c < 2 ^ d, ∀ u, Tr c u →
      ((∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd) ↔ Tr (c + 1) u))
    (hmono : ∀ c < 2 ^ d, ∀ u, Tr (c + 1) u → Tr c u)
    (hform : ∀ u, Tr (2 ^ d) u ↔ ∃ t, C.toCountData.Valid b l t ∧ enc t = u)
    (Lx : Prop) (hL : Lx ↔ Odd (∑ σ, C.acc σ)) :
    Lx ↔ Odd (Finset.univ.filter fun u : Fin m → Bool =>
      ∀ γ : Fin k → Bool, ProgAnswers (R bit letter d chk) answer
        (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true (4 * d + bnd)).card :=
  lemmaP_count C b l hl Xn F1 s e he hes bit letter hbit answer hacc d chk k hk bnd hb x enc hinj
    hP4 hP5 (fun u => pass_iff_of_stages enc (C.toCountData.Valid b l) (2 ^ d)
      (fun c u => ∀ Rc, chk c = some Rc → ∀ ρ : List Bool, ρ.length = k - d →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) ρ) true bnd)
      Tr h0 hstep hmono hform u) Lx hL

open scoped Classical in
/-- **The count from stage lemmas in any stage order.** A check is a pair `(c, ρ)` (family, index);
`grp j` is the set of checks of stage `j < K` (D5: C1-C3, C14, C4, per level C5-C9 then C10, C11, C12,
C13link + C13ends); `hcover`: every check is in some stage. `Tr j u`: the fields of the first `j` stages
hold their true values. -/
theorem lemmaP_count_of_groups
    (hP4 : ∀ σ, contract (Xn σ) (fun u z => e σ u * F1 σ u z) = (C.acc σ : F))
    (hP5 : ∀ σ, contract (Xn σ) (F1 σ) = ∑ ι : C.Ch σ,
      ∑ z : (e : (C.Y σ ι).Edge) → (C.Y σ ι).Payload e,
        ∏ v, C.G σ ι v (edgeAssignment (C.Y σ ι).src (C.Y σ ι).dst z v))
    (grp : ℕ → ℕ × List Bool → Prop) (K : ℕ) (hcover : ∀ p, ∃ j < K, grp j p)
    (Tr : ℕ → (Fin m → Bool) → Prop) (h0 : ∀ u, Tr 0 u)
    (hstep : ∀ j < K, ∀ u, Tr j u →
      ((∀ p, grp j p → p.1 < 2 ^ d → p.2.length = k - d → ∀ Rc, chk p.1 = some Rc →
        ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) p.2) true bnd) ↔ Tr (j + 1) u))
    (hmono : ∀ j < K, ∀ u, Tr (j + 1) u → Tr j u)
    (hform : ∀ u, Tr K u ↔ ∃ t, C.toCountData.Valid b l t ∧ enc t = u)
    (Lx : Prop) (hL : Lx ↔ Odd (∑ σ, C.acc σ)) :
    Lx ↔ Odd (Finset.univ.filter fun u : Fin m → Bool =>
      ∀ γ : Fin k → Bool, ProgAnswers (R bit letter d chk) answer
        (inputRegs letter x (List.ofFn u) (List.ofFn γ)) true (4 * d + bnd)).card := by
  refine lemmaP_count C b l hl Xn F1 s e he hes bit letter hbit answer hacc d chk k hk bnd hb x enc hinj
    hP4 hP5 (fun u => ?_) Lx hL
  have hg := pass_iff_of_groups enc (C.toCountData.Valid b l)
    (fun (p : ℕ × List Bool) (u : Fin m → Bool) => p.1 < 2 ^ d → p.2.length = k - d →
      ∀ Rc, chk p.1 = some Rc → ProgAnswers Rc answer (inputRegs letter x (List.ofFn u) p.2) true bnd)
    grp K hcover Tr h0 hstep hmono hform u
  rw [← hg]
  constructor
  · intro h p hc hρ Rc hR
    exact h p.1 hc Rc hR p.2 hρ
  · intro h c hc Rc hR ρ hρ
    exact h (c, ρ) hc hρ Rc hR

end

end P1Count
