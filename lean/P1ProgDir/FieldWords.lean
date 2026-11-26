import P1ProgDir.FrontWords
import P1ProgDir.FieldRead
import P1ProgDir.Offsets

namespace P1ProgDir.SolFieldWords

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1Wit P1Int
open P1ProgDir.SolGeometry P1ProgDir.SolFrontWords P1ProgDir.SolOffsets P1ProgDir.SolFieldRead

variable {X : Type} [Codec X]

theorem poly_add {f g : X → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => add (f x, g x)) :=
  (hf.pair hg).compose (easy_add Easy.identity).poly

theorem poly_scale (k : ℕ) {f : X → Word} (hf : Poly f) :
    Poly (fun x => scale k (f x)) :=
  hf.compose (easy_scale k Easy.identity).poly

theorem poly_mul {f g : X → Word} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => product (f x, g x)) :=
  (hf.pair hg).compose Poly.product_base

theorem poly_list {A : Type} [Codec A] (fs : List (X → A)) (hf : ∀ f ∈ fs, Poly f) :
    Poly (fun x => fs.map (fun f => f x)) := by
  induction fs with
  | nil => exact Code.Poly.const []
  | cons f fs ih =>
    exact ((hf f List.mem_cons_self).pair (ih fun g hg => hf g (List.mem_cons_of_mem _ hg))).compose
      Poly.cons

def fieldRequest (offset width index : Word) : P1Batch.Req :=
  (add (offset, product (index, width)), width)

theorem poly_fieldRequest {offset width index : X → Word}
    (ho : Poly offset) (hw : Poly width) (hi : Poly index) :
    Poly (fun x => fieldRequest (offset x) (width x) (index x)) :=
  (poly_add ho (poly_mul hi hw)).pair hw

theorem fieldRequest_values (offset width index : Word) :
    P1Batch.bval (fieldRequest offset width index).1 = value offset + value index * value width ∧
    P1Batch.bval (fieldRequest offset width index).2 = value width := by
  simp only [fieldRequest, P1Batch.bval_eq_value, add_val, exact_prod, and_self]

theorem fieldRequest_fits {D : Dims} {s : ℕ} {u : Word} {offset width index : Word}
    (ho : value offset = D.off s) (hw : value width = D.width s)
    (hi : value index < D.count s) (hs : s + 1 ≤ 5) (hfit : guessEnd D ≤ u.length) :
    P1Batch.bval (fieldRequest offset width index).1 + P1Batch.bval (fieldRequest offset width index).2 ≤
      u.length := by
  obtain ⟨ha, hb⟩ := fieldRequest_values offset width index
  rw [ha, hb, ho, hw]
  exact interval_fits hi hs hfit

theorem fieldRequest_read {D : Dims} {s : ℕ} (u offset width index : Word)
    (ho : value offset = D.off s) (hw : value width = D.width s) :
    value (P1Batch.fetch u (fieldRequest offset width index)) = readField D u s (value index) := by
  obtain ⟨ha, hb⟩ := fieldRequest_values offset width index
  apply fetch_value
  · rw [← P1Batch.bval_eq_value, ha, ho, hw]
  · rw [← P1Batch.bval_eq_value, hb, hw]

def widthWord (a b w₀ w₁ : ℕ) (n : Word) : Word :=
  born (widthTally a b w₀ w₁ n).length

theorem poly_widthWord (a b w₀ w₁ : ℕ) : Poly (widthWord a b w₀ w₁) :=
  (poly_widthTally a b w₀ w₁).compose easy_chart.poly

theorem widthWord_value (a b w₀ w₁ : ℕ) (n : Word) :
    value (widthWord a b w₀ w₁ n) = w₀ + w₁ * lpK2 a b (value n) := by
  rw [widthWord, birthValue, widthTally_length]

def blocksWord (a b aM r : ℕ) (n : Word) : Word := scale r (iWord a b aM n)

theorem poly_blocksWord (a b aM r : ℕ) : Poly (blocksWord a b aM r) :=
  poly_scale r (poly_iWord a b aM)

theorem blocksWord_value (a b aM r : ℕ) (n : Word) :
    value (blocksWord a b aM r n) = bigCount a b aM (value n) * r := by
  simp only [blocksWord, scale_exact, iWord_value, Nat.mul_comm]

def startWord (a b aM r : ℕ) (n : Word) : Word := false :: tritCountWord a b aM r n

theorem poly_startWord (a b aM r : ℕ) : Poly (startWord a b aM r) := by
  have hp : Poly (fun n : Word => (false, tritCountWord a b aM r n)) :=
    (Code.Poly.const false).pair (poly_tritCountWord a b aM r)
  exact Code.Poly.compose (f := fun n => (false, tritCountWord a b aM r n))
    (g := fun p : Bool × Word => p.1 :: p.2) hp Code.Poly.cons

theorem startWord_value (a b aM r : ℕ) (n : Word) :
    value (startWord a b aM r n) = bigCount a b aM (value n) * laneCount a b (value n) * r * 2 := by
  simp only [startWord, value_cons, d0, zero_add, tritCountWord_value, Nat.mul_comm 2]

def directoryWidth (a b aM r w₀ w₁ : ℕ) (n : Word) : Word :=
  product (blocksWord a b aM r n, widthWord a b w₀ w₁ n)

theorem poly_directoryWidth (a b aM r w₀ w₁ : ℕ) : Poly (directoryWidth a b aM r w₀ w₁) :=
  poly_mul (poly_blocksWord a b aM r) (poly_widthWord a b w₀ w₁)

theorem directoryWidth_value (a b aM r w₀ w₁ : ℕ) (n : Word) :
    value (directoryWidth a b aM r w₀ w₁ n) =
      bigCount a b aM (value n) * r * (w₀ + w₁ * lpK2 a b (value n)) := by
  simp only [directoryWidth, exact_prod, blocksWord_value, widthWord_value]

def endWord (a b aM r w₀ w₁ c : ℕ) (n : Word) : Word :=
  add (startWord a b aM r n, scale c (directoryWidth a b aM r w₀ w₁ n))

theorem poly_endWord (a b aM r w₀ w₁ c : ℕ) : Poly (endWord a b aM r w₀ w₁ c) :=
  poly_add (poly_startWord a b aM r) (poly_scale c (poly_directoryWidth a b aM r w₀ w₁))

theorem endWord_value (a b aM r w₀ w₁ c : ℕ) (n : Word) :
    value (endWord a b aM r w₀ w₁ c n) =
      value (startWord a b aM r n) + c * value (directoryWidth a b aM r w₀ w₁ n) := by
  simp only [endWord, add_val, scale_exact]

end P1ProgDir.SolFieldWords
