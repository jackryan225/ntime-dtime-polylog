import P1ProgDir.BatchCore

namespace P1ProgDir.SolSmallBatch

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolBatchCore

theorem size_fetches (w : Word) (qs : List P1Batch.Req) :
    size (qs.map (P1Batch.fetch w)) ≤ 2 * P1Batch.total qs + size qs := by
  induction qs with
  | nil => exact Nat.le_refl 1
  | cons q qs ih =>
    have hl : (P1Batch.fetch w q).length ≤ P1Batch.bval q.2 := by
      unfold P1Batch.fetch
      rw [List.length_take]
      exact Nat.min_le_left _ _
    have hs := size_pos q
    simp only [List.map_cons, size_cons, size_word, P1Batch.total, List.sum_cons] at *
    omega

/-- Execute a batch whose request length and total width are polynomial in a
small header. The data can have arbitrary contents and is charged linearly. -/
theorem task {X H S : Type} [Codec H] [Codec S]
    (header : X → H) (w : X → Word) (plan : H → List P1Batch.Req × S)
    (hp : Poly plan)
    (htot : Dom (fun x => size (header x)) (fun x => P1Batch.total (plan (header x)).1))
    (hfit : ∀ x q, q ∈ (plan (header x)).1 →
      P1Batch.bval q.1 + P1Batch.bval q.2 ≤ (w x).length) :
    ∃ t : X → ℕ, Dom (fun x => size (header x)) t ∧
      Task (fun x => 2 * (w x).length + t x)
        (fun x => send (header x, w x))
        (fun x => send ((plan (header x)).1.map (P1Batch.fetch (w x)), (plan (header x)).2)) := by
  let qs (x : X) := (plan (header x)).1
  let st (x : X) := (plan (header x)).2
  have hsz := (Code.Poly.length hp).map header
  have hqs := (Code.Poly.length (Code.Poly.fstCompose hp)).map header
  obtain ⟨a, ha, hpre⟩ := hp
  obtain ⟨c, hb⟩ := batchWith w qs st hfit
  have hpack : Easy (fun p : (List P1Batch.Req × S) × Word => ((p.2, p.1.1), p.1.2)) :=
    (Easy.snd.pair (Easy.fst.compose Easy.fst)).pair (Easy.fst.compose Easy.snd)
  let t (x : X) := a (header x) + size (plan (header x)) + size (qs x) +
    (size (qs x) + P1Batch.total (qs x) + 1) ^ c + 4
  refine ⟨t, ?_, ?_⟩
  · exact ((((ha.map header).add hsz).add hqs).add
      (((hqs.add htot).add (Dom.const _ 1)).pow c)).add (Dom.const _ 4)
  · refine (((hpre.on header).left (fun x => send (w x))).compose
      ((hpack.on (fun x => (plan (header x), w x))).compose hb)).bound 3 ?_
    intro x
    simp only [size_prod, size_word, t]
    omega

def readPlan {H S : Type} (plan : H → List P1Batch.Req × S) (header : H) (w : Word) :
    List Word × S :=
  ((plan header).1.map (P1Batch.fetch w), (plan header).2)

theorem readPlan_size {X H S : Type} [Codec H] [Codec S]
    (header : X → H) (w : X → Word) (plan : H → List P1Batch.Req × S)
    (hp : Poly plan)
    (htot : Dom (fun x => size (header x)) (fun x => P1Batch.total (plan (header x)).1)) :
    Dom (fun x => size (header x)) (fun x => size (readPlan plan (header x) (w x))) := by
  apply (((Dom.const _ 2).mul htot).add ((Code.Poly.length hp).map header)).mono
  intro x
  have h := size_fetches (w x) (plan (header x)).1
  simp only [readPlan, size_prod, Nat.add_assoc]
  omega

theorem once {X H S : Type} [Codec H] [Codec S]
    (header : X → H) (w : X → Word) (plan : H → List P1Batch.Req × S)
    (reply : List Word × S → Bool) (hp : Poly plan) (hr : Poly reply)
    (htot : Dom (fun x => size (header x)) (fun x => P1Batch.total (plan (header x)).1))
    (hfit : ∀ x q, q ∈ (plan (header x)).1 →
      P1Batch.bval q.1 + P1Batch.bval q.2 ≤ (w x).length) :
    ∃ t : X → ℕ, Dom (fun x => size (header x)) t ∧
      Task (fun x => (w x).length + t x) (fun x => send (header x, w x))
        (fun x => send (reply (readPlan plan (header x) (w x)))) := by
  obtain ⟨t₁, hd₁, h₁⟩ := task header w plan hp htot hfit
  obtain ⟨t₂, hd₂, h₂⟩ := hr.on (readPlan_size header w plan hp htot)
  refine ⟨_, hd₁.add hd₂, (h₁.compose h₂).bound 2 ?_⟩
  intro x
  change 2 * (w x).length + t₁ x + t₂ x + 1 ≤ 2 * ((w x).length + (t₁ x + t₂ x) + 1)
  omega

/-- The second plan can depend on the first reply. The width and address bounds
are checked for that actual reply before the second batch runs. -/
theorem twice {X H S T : Type} [Codec H] [Codec S] [Codec T]
    (header : X → H) (w : X → Word) (p₁ : H → List P1Batch.Req × S)
    (p₂ : List Word × S → List P1Batch.Req × T) (reply : List Word × T → Bool)
    (hp₁ : Poly p₁) (hp₂ : Poly p₂) (hr : Poly reply)
    (h₁ : Dom (fun x => size (header x)) (fun x => P1Batch.total (p₁ (header x)).1))
    (h₂ : Dom (fun x => size (readPlan p₁ (header x) (w x)))
      (fun x => P1Batch.total (p₂ (readPlan p₁ (header x) (w x))).1))
    (hf₁ : ∀ x q, q ∈ (p₁ (header x)).1 →
      P1Batch.bval q.1 + P1Batch.bval q.2 ≤ (w x).length)
    (hf₂ : ∀ x q, q ∈ (p₂ (readPlan p₁ (header x) (w x))).1 →
      P1Batch.bval q.1 + P1Batch.bval q.2 ≤ (w x).length) :
    ∃ t : X → ℕ, Dom (fun x => size (header x)) t ∧
      Task (fun x => (w x).length + t x) (fun x => send (header x, w x))
        (fun x => send (reply (readPlan p₂ (readPlan p₁ (header x) (w x)) (w x)))) := by
  let mid (x : X) := readPlan p₁ (header x) (w x)
  let out (x : X) := readPlan p₂ (mid x) (w x)
  obtain ⟨t₁, hd₁, e₁⟩ := task header w p₁ hp₁ h₁ hf₁
  obtain ⟨t₂, hd₂, e₂⟩ := task mid w p₂ hp₂ h₂ hf₂
  have hmid : Dom (fun x => size (header x)) (fun x => size (mid x)) :=
    readPlan_size header w p₁ hp₁ h₁
  have hout : Dom (fun x => size (header x)) (fun x => size (out x)) :=
    (readPlan_size mid w p₂ hp₂ h₂).sub hmid
  obtain ⟨t₃, hd₃, e₃⟩ := hr.on hout
  have hdup : Easy (fun p : H × Word => (p, p.2)) := Easy.identity.pair Easy.snd
  let t (x : X) := size (header x) + t₁ x + t₂ x + t₃ x
  refine ⟨t, (((Dom.base _).add hd₁).add (hd₂.sub hmid)).add hd₃, ?_⟩
  refine ((((hdup.on (fun x => (header x, w x))).compose
      (e₁.left (fun x => send (w x)))).compose e₂).compose e₃).bound 6 ?_
  intro x
  simp only [size_prod, size_word, t]
  omega

end P1ProgDir.SolSmallBatch
