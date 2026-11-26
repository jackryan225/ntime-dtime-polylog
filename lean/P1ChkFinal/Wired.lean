import P1Wit.Layout
import P1ChkFinal.Checks
import P1ChkFinal.C13

/-!
# P1, wave 2: checks C11, C12, C13link, C13ends in the dispatcher form of D5 (lane P1-lean-W2-chkfinal)

G3-chief D5 (board 10:49Z) and its amendment (10:51Z): each family is a Prop `Ck (fixed data) (x u : List Bool)
(i : ℕ)`, with out-of-range indices accepting (`Ck_out`). The fields are read with the P6 readers of
`P1Wit.Layout` (job wit-3): `rdOmega` (section `secOmega`), `rdWidth` at the final level `D.top` (field index
`((y * lanes + lane) * slots + slot)`), `rdPayload` (S3 = `u.drop D.fixedLen`), `rdChain` (section `secChain`).
`dims n` is the format at input length `n` (fixed data, P6/P10).

Arc order inside a final base (S3, paper l.1059 "base, lane, outgoing slot"): arc `t = lane * slots + slot`,
`t < lanes * slots`.
-/

namespace P1ChkFinal

open P1Wit Module

/-- Number of final bases. -/
def finN (D : Dims) : ℕ := (D.lv D.top).bases

/-- Arcs per final base. -/
def finArcs (D : Dims) : ℕ := (D.lv D.top).lanes * (D.lv D.top).slots

/-- Stored width of arc `t` of final base `y` (`t = lane * slots + slot`). -/
def arcW (D : Dims) (u : List Bool) (y t : ℕ) : ℕ :=
  rdWidth D u D.top y (t / (D.lv D.top).slots) (t % (D.lv D.top).slots)

/-- Stored width sum of final base `y` (the `ws y` of C11, C12). -/
def wsOf (D : Dims) (u : List Bool) (y : ℕ) : ℕ := pre (arcW D u y) (finArcs D)

/-- Family 10: **C11** at final base `i`. -/
def C11w (dims : ℕ → Dims) (x u : List Bool) (i : ℕ) : Prop :=
  C11 (finN (dims x.length)) (rdOmega (dims x.length) u) (wsOf (dims x.length) u) i

/-- Family 11: **C12** (one check, index 0). -/
def C12w (dims : ℕ → Dims) (x u : List Bool) (i : ℕ) : Prop :=
  i = 0 → C12 (finN (dims x.length)) (rdOmega (dims x.length) u) (wsOf (dims x.length) u)
    (rdPayload (dims x.length) u)

/-- Number of final positions `P` (the chain has `P + 1 = chainLen` entries). -/
def finP (D : Dims) : ℕ := D.chainLen - 1

variable {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}

/-- Family 12: **C13link** at final position `i`; `Wof x u v` is the value `W_v(z|_v; ι(u))` that the check
computes (P5 `Wv_eval`, interface). -/
def C13linkw (b : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims) (Wof : List Bool → List Bool → ℕ → F)
    (x u : List Bool) (i : ℕ) : Prop :=
  C13link b (finP (dims x.length)) (Wof x u) (rdChain (dims x.length) u) i

/-- Family 13: **C13ends** (index 0 start, 1 end). -/
def C13endsw (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims) (x u : List Bool)
    (i : ℕ) : Prop :=
  C13ends b l (finP (dims x.length)) (rdChain (dims x.length) u) i

/-! ## Counts and out-of-range indices (D5 amendment) -/

def cnt11 (dims : ℕ → Dims) (n : ℕ) : ℕ := finN (dims n)
def cnt12 (_dims : ℕ → Dims) (_n : ℕ) : ℕ := 1
def cnt13link (dims : ℕ → Dims) (n : ℕ) : ℕ := finP (dims n)
def cnt13ends (_dims : ℕ → Dims) (_n : ℕ) : ℕ := 2

theorem C11w_out (dims : ℕ → Dims) (x u : List Bool) {i : ℕ} (hi : cnt11 dims x.length ≤ i) :
    C11w dims x u i := C11_out hi

theorem C12w_out (dims : ℕ → Dims) (x u : List Bool) {i : ℕ} (hi : cnt12 dims x.length ≤ i) :
    C12w dims x u i := fun h => absurd h (by simp only [cnt12] at hi; omega)

theorem C13linkw_out (b : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims) (Wof : List Bool → List Bool → ℕ → F)
    (x u : List Bool) {i : ℕ} (hi : cnt13link dims x.length ≤ i) : C13linkw b dims Wof x u i :=
  C13link_out b _ _ hi

theorem C13endsw_out (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims)
    (x u : List Bool) {i : ℕ} (hi : cnt13ends dims x.length ≤ i) : C13endsw b l dims x u i :=
  C13ends_out b l _ _ hi

/-! ## Stage forms (what the passing checks force) -/

/-- C11 at every index iff the stored prefixes are the true prefix sums of the stored final widths. -/
theorem C11w_iff (dims : ℕ → Dims) (x u : List Bool) :
    (∀ i, C11w dims x u i) ↔
      ∀ y < finN (dims x.length), rdOmega (dims x.length) u y = pre (wsOf (dims x.length) u) y := by
  rw [← C11_iff]
  exact ⟨fun h y _ => h y, fun h y => if hy : y < finN (dims x.length) then h y hy else C11_out (not_lt.mp hy)⟩

/-- Under C11 everywhere, C12 iff S3 is a payload of length `pre ws N` followed by zeros. -/
theorem C12w_iff (dims : ℕ → Dims) (x u : List Bool) (h11 : ∀ i, C11w dims x u i) :
    (∀ i, C12w dims x u i) ↔
      pre (wsOf (dims x.length) u) (finN (dims x.length)) ≤ (rdPayload (dims x.length) u).length ∧
        ∀ c ∈ (rdPayload (dims x.length) u).drop (pre (wsOf (dims x.length) u) (finN (dims x.length))),
          c = false := by
  have h11' : ∀ y < finN (dims x.length), C11w dims x u y := fun y _ => h11 y
  have ht := total_eq h11'
  constructor
  · intro h
    have h0 := h 0 rfl
    rw [C12, ht] at h0
    exact h0
  · intro h i hi
    rw [C12, ht]
    exact h

/-- C13link and C13ends at every index iff the stored chain numbers are a chain with `ChainOK`. -/
theorem C13w_iff (b : Basis (Fin Dd) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (dims : ℕ → Dims)
    (Wof : List Bool → List Bool → ℕ → F) (x u : List Bool) :
    ((∀ i, C13linkw b dims Wof x u i) ∧ (∀ i, C13endsw b l dims x u i)) ↔
      ∃ j : Fin (finP (dims x.length) + 1) → Fin Dd,
        (∀ v : Fin (finP (dims x.length) + 1), (j v : ℕ) = rdChain (dims x.length) u v) ∧
        P1Count.ChainOK b l (fun i : Fin (finP (dims x.length)) => Wof x u i) j :=
  C13link_iff b l _ _ _

end P1ChkFinal
