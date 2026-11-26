import P1C10.Prog

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code

namespace P1SolC10P.SolC10prog

open P1ChkFinal

private theorem stepOnce {X S : Type} [Codec S] (hb : BatchHyp)
    (u : X → List Bool) (s : X → S) (rq : S → List P1Batch.Req)
    (step : S × List (List Bool) → S) (σ : X → ℕ)
    (hrq : Poly (fun z : S => (rq z, z))) (hstep : Poly step)
    (hs : Dom σ (fun p => size (s p)))
    (htot : Dom σ (fun p => P1Batch.total (rq (s p))))
    (haddr : ∀ p, ∀ q ∈ rq (s p), P1Batch.bval q.1 ≤ (u p).length) :
    ∃ t : X → ℕ, Dom σ t ∧
      Code.Task (fun p => (u p).length + t p) (fun p => send (u p, s p))
        (fun p => send (u p, step (s p, (rq (s p)).map (P1Batch.fetch (u p))))) := by
  let F (p : X) := (rq (s p)).map (P1Batch.fetch (u p))
  have hR : Dom σ (fun p => size (rq (s p))) := by
    have h : Dom size (fun z : S => size (rq z)) :=
      hrq.length.mono (fun z => by simp only [size_prod]; omega)
    exact (h.map s).sub hs
  have hF : Dom σ (fun p => size (F p)) :=
    ((((Dom.const σ 2).mul htot).add ((Dom.const σ 2).mul hR)).add (Dom.const σ 1)).mono
      (fun p => size_fields (u p) (rq (s p)))
  have hPair : Dom σ (fun p => size (s p, F p)) :=
    ((hs.add hF).add (Dom.const σ 1)).mono (fun p => by rw [size_prod])
  obtain ⟨tr, htr, Tr⟩ := hrq.on hs
  obtain ⟨ts, hts, Ts⟩ := hstep.on hPair
  obtain ⟨cb, Tb⟩ := hb
  let bin (p : X) : P1Batch.BatchIn := ⟨(u p, rq (s p)), haddr p⟩
  let reshuffle (v : List Bool × (List P1Batch.Req × S)) := ((v.1, v.2.1), v.2.2)
  have easyReshuffle : Easy reshuffle :=
    Easy.pair (Easy.pair Easy.fst (Easy.snd.compose Easy.fst)) (Easy.snd.compose Easy.snd)
  have fetchStep :=
    (((Tr.right (fun p => send (u p))).compose
      (easyReshuffle.on (fun p => (u p, (rq (s p), s p))))).compose
      ((Tb.on bin).left (fun p => send (s p)))).compose
      ((Easy.exchange (X := List (List Bool)) (Y := S)).on (fun p => (F p, s p)))
  have copy : Easy (fun v : List Bool × S => (v.1, v)) :=
    Easy.pair Easy.fst Easy.identity
  have T := (copy.on (fun p => (u p, s p))).compose
    ((fetchStep.compose Ts).right (fun p => send (u p)))
  let b (p : X) := (size (rq (s p)) + P1Batch.total (rq (s p)) + 1) ^ cb
  have hb' : Dom σ b := ((hR.add htot).add (Dom.const σ 1)).pow cb
  let t (p : X) := tr p + ts p + 3 * size (s p) + size (rq (s p)) + size (F p) + b p + 6
  have ht : Dom σ t :=
    ((((((htr.add hts).add ((Dom.const σ 3).mul hs)).add hR).add hF).add hb').add
      (Dom.const σ 6))
  refine ⟨t, ht, T.bound 10 (fun p => ?_)⟩
  change size (u p, s p) + ((send (u p)).count +
    ((send (u p)).count + tr p + size (u p, (rq (s p), s p)) +
      ((u p).length + b p) + size (F p, s p) + ts p)) + 1 ≤ 10 * ((u p).length + t p + 1)
  have hu : (send (u p)).count = 2 * (u p).length + 1 := size_listBool (u p)
  simp only [size_prod, size_listBool, hu, t]
  omega

end P1SolC10P.SolC10prog

theorem P1SolC10P.checkRounds : P1C10.CheckRoundsTarget := by
  intro X S codec hb R Q u s0 rq step dec ck a σ hA hrq hstep hdec hs htot haddr hck
  let state (r : ℕ) (p : X) := P1C10.roundState rq step (u p) (s0 p) r
  have run : ∀ r ≤ R, ∃ t : X → ℕ, Dom σ t ∧
      Code.Task (fun p => a p + r * (u p).length + t p) Q (fun p => send (u p, state r p)) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨fun _ => 0, Dom.const σ 0, by
        simpa only [Nat.zero_mul, Nat.add_zero, state, P1C10.roundState] using hA⟩
    | succ r ih =>
      intro hr
      have hl : r < R := Nat.lt_of_succ_le hr
      obtain ⟨t, ht, T⟩ := ih (r.le_succ.trans hr)
      obtain ⟨t', ht', T'⟩ := P1SolC10P.SolC10prog.stepOnce hb u (state r) rq step σ hrq hstep
        (hs r (Nat.le_of_lt hl)) (htot r hl) (fun p => haddr p r hl)
      refine ⟨fun p => t p + t' p, ht.add ht', (T.compose T').conform ?_ (fun _ => rfl) (fun _ => rfl)⟩
      intro p
      change a p + r * (u p).length + t p + ((u p).length + t' p) =
        a p + (r + 1) * (u p).length + (t p + t' p)
      rw [Nat.succ_mul]
      omega
  obtain ⟨t, ht, T⟩ := run R le_rfl
  obtain ⟨td, htd, Td⟩ := hdec.on (hs R le_rfl)
  have drop := Code.Task.dropLeft (fun p => send (u p)) (fun p => send (state R p))
  have Tf := (T.compose drop).compose Td
  refine ⟨fun p => t p + td p + 1, (ht.add htd).add (Dom.const σ 1), ?_⟩
  have Tf' := Tf.bound (b' := fun p => a p + (R + 1) * (u p).length + (t p + td p + 1)) 2
    (fun p => by
      have hu : (send (u p)).count = 2 * (u p).length + 1 := P1ChkFinal.size_listBool (u p)
      rw [hu, Nat.add_mul, Nat.one_mul]
      omega)
  exact Tf'.conform (fun _ => rfl) (fun _ => rfl) (fun p => by rw [hck p])

#print axioms P1SolC10P.checkRounds
