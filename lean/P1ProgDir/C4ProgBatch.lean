import P1Batch.Statement
import OAI.Computability.IntegerMultiplication.Code.Auto
import OAI.Computability.IntegerMultiplication.Bits.Word

namespace P1ProgDir.SolC4

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1Batch (Req fetch total)

theorem size_fieldResults (u : List Bool) (qs : List Req) :
    size (qs.map (fetch u)) ≤ size qs + 2 * total qs := by
  induction qs with
  | nil => simp [total]
  | cons q qs ih =>
    have h : (fetch u q).length ≤ P1Batch.bval q.2 := by
      unfold fetch
      rw [List.length_take]
      exact Nat.min_le_left _ _
    simp only [List.map_cons, size_cons, size_word (fetch u q), total, List.sum_cons]
    have hq := size_pos q
    change size (qs.map (fetch u)) ≤ size qs + 2 * ((qs.map fun q => P1Batch.bval q.2).sum) at ih
    omega

/-- Run one batch scan, retaining the witness and the compact state for the
next stage. Only the two structural adapters copy or move the witness. -/
theorem batchKeep {X α : Type} [Codec α] (u : X → List Bool) (ctx : X → α) (qs : X → List Req)
    (hAddr : ∀ x q, q ∈ qs x → P1Batch.bval q.1 ≤ (u x).length) :
    ∃ c : ℕ,
      Task (fun x => 10 * ((u x).length + size (ctx x) + size (qs x) + total (qs x) + 1) +
        (size (qs x) + total (qs x) + 1) ^ c)
        (fun x => send ((ctx x, qs x), u x))
        (fun x => send ((ctx x, (qs x).map (fetch (u x))), u x)) := by
  obtain ⟨c, hBatch⟩ := P1Batch.batch_lookup
  let p : X → P1Batch.BatchIn := fun x => ⟨(u x, qs x), hAddr x⟩
  have hLookup := (hBatch.on p).left (fun x => send (u x, ctx x))
  have hPre : Easy (fun q : (α × List Req) × List Bool =>
      ((q.2, q.1.2), q.2, q.1.1)) := by fun_prop
  have hPost : Easy (fun q : List (List Bool) × List Bool × α =>
      ((q.2.2, q.1), q.2.1)) := by fun_prop
  have hPre' := hPre.on (fun x => ((ctx x, qs x), u x))
  have hPost' := hPost.on (fun x => ((qs x).map (fetch (u x)), u x, ctx x))
  refine ⟨c, ((hPre'.compose hLookup).compose hPost').mono ?_⟩
  intro x
  have hx := size_fieldResults (u x) (qs x)
  simp only [size_prod, size_word (u x), p]
  omega

/-- Apply the length encoder to both input lists while retaining the witness. -/
theorem easy_queryLengths (encode : ℕ → Word)
    (h : Easy (fun u : List Bool => encode u.length)) :
    Easy (fun p : List Bool × List Bool × List Bool =>
      ((encode p.1.length, encode p.2.1.length, p.2.2), p.2.1)) :=
  ((Easy.fst.compose h).pair
    ((Easy.snd.fstCompose.compose h).pair Easy.snd.sndCompose)).pair Easy.snd.fstCompose

/-- One witness-linear term and a polynomial in the compact input size. This
keeps the full witness outside each use of the polynomial-time combinators. -/
def ScanTask {X : Type} (u : X → Word) (small : X → ℕ) (query reply : X → Tree) : Prop :=
  ∃ cost, Dom small cost ∧ Task (fun x => (u x).length + cost x) query reply

namespace ScanTask

variable {X : Type} {u : X → Word} {small : X → ℕ} {q r s : X → Tree}

theorem compose (h₁ : ScanTask u small q r) (h₂ : ScanTask u small r s) : ScanTask u small q s := by
  obtain ⟨b, hb, h₁⟩ := h₁
  obtain ⟨d, hd, h₂⟩ := h₂
  refine ⟨fun x => b x + d x, hb.add hd, (h₁.compose h₂).bound 2 ?_⟩
  intro x
  dsimp only
  omega

theorem compact {A B : Type} [Codec A] [Codec B] {f : A → B} (hf : Poly f) (a : X → A)
    (ha : Dom small (fun x => size (a x))) :
    ScanTask u small (fun x => send (a x, u x)) (fun x => send (f (a x), u x)) := by
  obtain ⟨b, hb, ht⟩ := hf.on ha
  exact ⟨b, hb, (ht.left (fun x => send (u x))).mono (fun x => Nat.le_add_left _ _)⟩

theorem batch {A : Type} [Codec A] (a : X → A) (qs : X → List Req)
    (ha : Dom small (fun x => size (a x)))
    (hqs : Dom small (fun x => size (qs x) + total (qs x) + 1))
    (hAddr : ∀ x q, q ∈ qs x → P1Batch.bval q.1 ≤ (u x).length) :
    ScanTask u small (fun x => send ((a x, qs x), u x))
      (fun x => send ((a x, (qs x).map (fetch (u x))), u x)) := by
  obtain ⟨c, ht⟩ := batchKeep u a qs hAddr
  refine ⟨fun x => size (a x) + (size (qs x) + total (qs x) + 1) +
    (size (qs x) + total (qs x) + 1) ^ c, (ha.add hqs).add (hqs.pow c), ht.bound 10 ?_⟩
  intro x
  dsimp only
  omega

theorem dropWitness {A : Type} [Codec A] (a : X → A) (ha : Dom small (fun x => size (a x))) :
    ScanTask u small (fun x => send (a x, u x)) (fun x => send (a x)) := by
  refine ⟨fun x => size (a x), ha, (Task.dropRight (fun x => send (a x)) (fun x => send (u x))).bound 2 ?_⟩
  intro x
  change size (a x) + size (u x) + 1 ≤ _
  rw [size_word]
  dsimp only
  omega

/-- Carry out a compact request generator and one batch scan. The result-size
bound counts fetched field bits and does not depend on the witness length. -/
theorem scan {A B : Type} [Codec A] [Codec B] {f : A → B × List Req} (hf : Poly f)
    (a : X → A) (ha : Dom small (fun x => size (a x)))
    (hTotal : Dom small (fun x => total (f (a x)).2))
    (hAddr : ∀ x q, q ∈ (f (a x)).2 → P1Batch.bval q.1 ≤ (u x).length) :
    let result := fun x => ((f (a x)).1, (f (a x)).2.map (fetch (u x)))
    ScanTask u small (fun x => send (a x, u x)) (fun x => send (result x, u x)) ∧
      Dom small (fun x => size (result x)) := by
  have hfSize : Dom small (fun x => size (f (a x))) := (hf.on ha).length ha
  have hctx : Dom small (fun x => size (f (a x)).1) := hfSize.mono fun x => by
    rw [size_prod]
    omega
  have hreq : Dom small (fun x => size (f (a x)).2) := hfSize.mono fun x => by
    rw [size_prod]
    omega
  constructor
  · exact (compact hf a ha).compose
      (batch (fun x => (f (a x)).1) (fun x => (f (a x)).2) hctx
        ((hreq.add hTotal).add (Dom.const _ 1)) hAddr)
  · apply (hfSize.add ((Dom.const _ 2).mul hTotal)).mono
    intro x
    dsimp only
    rw [size_prod, size_prod]
    dsimp only
    have h := size_fieldResults (u x) (f (a x)).2
    omega

end ScanTask

end P1ProgDir.SolC4
