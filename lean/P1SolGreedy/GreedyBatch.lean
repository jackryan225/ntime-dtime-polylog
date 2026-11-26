import P1ChkFinal.Skeleton

open OAI.Computability.IntegerMultiplication
open OAI.Computability.IntegerMultiplication.Code
open P1ChkFinal

namespace P1SolGreedy.SolDemand

/-- Keep the witness for the next batch while processing the current fields. -/
theorem batchPhase {X S T : Type} [Codec S] [Codec T] (hb : BatchHyp)
    (u : X → List Bool) (s : X → S) (σ : X → ℕ)
    (rq : S → List P1Batch.Req) (next : S × List (List Bool) → T)
    (hrq : Poly rq) (hn : Poly next)
    (hs : Dom σ (fun p => size (s p)))
    (htot : Dom σ (fun p => P1Batch.total (rq (s p))))
    (ha : ∀ p, ∀ r ∈ rq (s p), P1Batch.bval r.1 ≤ (u p).length) :
    ∃ t : X → ℕ, Dom σ t ∧
      Dom σ (fun p => size (next (s p, (rq (s p)).map (P1Batch.fetch (u p))))) ∧
      Code.Task (fun p => (u p).length + t p)
        (fun p => send (u p, s p))
        (fun p => send (u p, next (s p, (rq (s p)).map (P1Batch.fetch (u p))))) := by
  let R := fun p => rq (s p)
  let F := fun p => (R p).map (P1Batch.fetch (u p))
  obtain ⟨c, hBatch⟩ := hb
  obtain ⟨tR, htR, taskR⟩ := hrq.pair Poly.identity
  have hnlen := hn.length
  obtain ⟨tN, htN, taskN⟩ := hn
  have phaseR := (taskR.on s).right (fun p => send (u p))
  let copy : List Bool × (List P1Batch.Req × S) → List Bool × ((List Bool × List P1Batch.Req) × S) :=
    fun p => (p.1, ((p.1, p.2.1), p.2.2))
  have copyEasy : Easy copy :=
    Easy.pair Easy.fst (Easy.pair (Easy.pair Easy.fst (Easy.compose Easy.snd Easy.fst))
      (Easy.compose Easy.snd Easy.snd))
  have phaseCopy := copyEasy.on (fun p => (u p, (R p, s p)))
  let i : X → P1Batch.BatchIn := fun p => ⟨(u p, R p), ha p⟩
  have phaseFetch := ((hBatch.on i).left (fun p => send (s p))).right (fun p => send (u p))
  have phaseSwap := ((Easy.exchange (X := List (List Bool)) (Y := S)).on
    (fun p => (F p, s p))).right (fun p => send (u p))
  have phaseNext := (taskN.on (fun p => (s p, F p))).right (fun p => send (u p))
  have whole := (((phaseR.compose phaseCopy).compose phaseFetch).compose phaseSwap).compose phaseNext
  let t : X → ℕ := fun p => tR (s p) + size (R p) + 2 * size (s p) +
    (size (R p) + P1Batch.total (R p) + 1) ^ c + size (F p) + tN (s p, F p) + 8
  have hR : Dom σ (fun p => size (R p)) := (hrq.length.map s).sub hs
  have hF : Dom σ (fun p => size (F p)) :=
    ((((Dom.const σ 2).mul htot).add ((Dom.const σ 2).mul hR)).add (Dom.const σ 1)).mono
      (fun p => size_fields (u p) (R p))
  have hNsmall : Dom σ (fun p => size (s p, F p)) :=
    ((hs.add hF).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  have hNs : Dom σ (fun p => tN (s p, F p)) := (htN.map _).sub hNsmall
  have hNextSmall : Dom σ (fun p => size (next (s p, F p))) :=
    (hnlen.map _).sub hNsmall
  refine ⟨t, ?_, hNextSmall, whole.bound 20 fun p => ?_⟩
  · exact (((((((htR.map s).sub hs).add hR).add ((Dom.const σ 2).mul hs)).add
        (((hR.add htot).add (Dom.const σ 1)).pow c)).add hF).add hNs).add (Dom.const σ 8)
  · simp only [size_prod, size_listBool, i, t]
    have hu := size_listBool (u p)
    have hu' : (send (u p)).count = 2 * (u p).length + 1 := hu
    simp only [hu']
    change _ ≤ _
    omega

/-- Compose two field batches with a polynomial update of the small state between them. -/
theorem twoBatchCheck {X S T : Type} [Codec S] [Codec T] (hb : BatchHyp)
    (Q : X → Tree) (u : X → List Bool) (s : X → S) (σ setup : X → ℕ)
    (rq₁ : S → List P1Batch.Req) (next : S × List (List Bool) → T)
    (rq₂ : T → List P1Batch.Req) (dec : T × List (List Bool) → Bool)
    (ck : X → Bool)
    (hA : Code.Task setup Q (fun p => send (u p, s p)))
    (hr₁ : Poly rq₁) (hn : Poly next) (hr₂ : Poly rq₂) (hd : Poly dec)
    (hs : Dom σ (fun p => size (s p)))
    (ht₁ : Dom σ (fun p => P1Batch.total (rq₁ (s p))))
    (ha₁ : ∀ p, ∀ r ∈ rq₁ (s p), P1Batch.bval r.1 ≤ (u p).length)
    (ht₂ : let s' := fun p => next (s p, (rq₁ (s p)).map (P1Batch.fetch (u p)))
      Dom σ (fun p => P1Batch.total (rq₂ (s' p))))
    (ha₂ : let s' := fun p => next (s p, (rq₁ (s p)).map (P1Batch.fetch (u p)))
      ∀ p, ∀ r ∈ rq₂ (s' p), P1Batch.bval r.1 ≤ (u p).length)
    (hck : let s' := fun p => next (s p, (rq₁ (s p)).map (P1Batch.fetch (u p)))
      ∀ p, ck p = dec (s' p, (rq₂ (s' p)).map (P1Batch.fetch (u p)))) :
    ∃ t : X → ℕ, Dom σ t ∧ Code.Task (fun p => setup p + 2 * (u p).length + t p)
      Q (fun p => send (ck p)) := by
  let s' := fun p => next (s p, (rq₁ (s p)).map (P1Batch.fetch (u p)))
  obtain ⟨t₁, ht₁', hs', T₁⟩ := batchPhase hb u s σ rq₁ next hr₁ hn hs ht₁ ha₁
  let setup' := fun p => setup p + ((u p).length + t₁ p)
  have T₀ : Code.Task setup' Q (fun p => send (u p, s' p)) := hA.compose T₁
  obtain ⟨t₂, ht₂', T₂⟩ := checkSkeleton hb Q u s' rq₂ dec ck setup' σ T₀
    (hr₂.pair Poly.identity) hd hs' ht₂ ha₂ hck
  refine ⟨fun p => t₁ p + t₂ p, ht₁'.add ht₂', T₂.bound 1 fun p => ?_⟩
  dsimp only [setup']
  omega

#print axioms batchPhase
#print axioms twoBatchCheck

end P1SolGreedy.SolDemand
