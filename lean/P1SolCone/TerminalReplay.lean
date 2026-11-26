import P1SolCone.TerminalProgram

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

theorem terminalIncidenceKeys_kinds (h : TerminalHeader) (k : FieldKey)
    (hk : k ∈ terminalIncidenceKeys h) : k.1 < 13 := by
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> dsimp only <;> decide

theorem terminalWidthKeys_kinds (h : TerminalHeader) (y : ℕ) (k : FieldKey)
    (hk : k ∈ terminalWidthKeys h y) : k.1 < 13 := by
  rcases List.mem_cons.mp hk with rfl | hk
  · change 12 < 13
    decide
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hk
    change Mem.width.toNat < 13
    decide

theorem terminalArcWidths_kinds (h : TerminalHeader) (c : FieldCache) (k : FieldKey)
    (hk : k ∈ terminalArcWidths h c) : k.1 < 13 := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hk
  exact terminalWidthKeys_kinds h a.1 k ha

def readTerminalFields (h : TerminalHeader) (ks : List FieldKey) (u : List Bool) : FieldCache :=
  fieldCache ks ((terminalFieldRequests h ks).map (P1Batch.fetch u))

def replayTerminalSpans (h : TerminalHeader) (u : List Bool) : Bool × List Span × List Span :=
  let inc := readTerminalFields h (terminalIncidenceKeys h) u
  let widths := readTerminalFields h (terminalArcWidths h inc) u
  cachedTerminalSpans h inc widths

theorem replayTerminalSpans_eq (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally)
    (hc : (D.lv D.top).slots ≤ clock.length) (hc' : finArcs D ≤ clock.length) (hf : D.fixedLen ≤ u.length) :
    terminalSpanOption (replayTerminalSpans (actualTerminalHeader D u.length w v clock) u) =
      terminalSpans D u w v := by
  unfold replayTerminalSpans
  apply cachedTerminalSpans_eq D u w v clock _ _ hc hc' _ _ hf
  · intro k hk
    exact readCachedTerminal D u w v clock _ (terminalIncidenceKeys_kinds _) k hk
  · intro k hk
    exact readCachedTerminal D u w v clock _ (terminalArcWidths_kinds _ _) k hk

def replayTerminalPayload (h : TerminalHeader) (u : List Bool) : Bool × HalfCode :=
  let s := replayTerminalSpans h u
  (s.1, splitPayload s.2 ((payloadRequests s.2).map (P1Batch.fetch u)))

/-- Terminal payload and width checks jointly determine the same optional half word as Wof. -/
theorem terminalPayload_replay (D : Dims) (u : List Bool) (w v : ℕ) (clock : Tally)
    (hc : (D.lv D.top).slots ≤ clock.length) (hc' : finArcs D ≤ clock.length) (hf : D.fixedLen ≤ u.length) :
    let reply := replayTerminalPayload (actualTerminalHeader D u.length w v clock) u
    (bif reply.1 then some reply.2 else none) =
      (bif widthsWithin w (readHalfWidths D u D.top (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes))
        then readFinalHalf D u v else none) := by
  let h := actualTerminalHeader D u.length w v clock
  cases hraw : replayTerminalSpans h u with
  | mk ok spans =>
    have hs := replayTerminalSpans_eq D u w v clock hc hc' hf
    change terminalSpanOption (replayTerminalSpans h u) = _ at hs
    rw [hraw] at hs
    simp only [replayTerminalPayload]
    change (bif (replayTerminalSpans h u).1 then some (splitPayload (replayTerminalSpans h u).2 _) else none) = _
    rw [hraw]
    cases ok
    · change none = terminalSpans D u w v at hs
      change none = (bif _ then _ else _)
      by_cases hw : widthsWithin w (readHalfWidths D u D.top (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)) = true
      · rw [hw]
        cases hf' : readFinalHalf D u v with
        | none => rfl
        | some half =>
          have hm := terminalSpans_complete D u w v (show (readFinalHalf D u v).isSome = true by rw [hf']; rfl) hw
          rw [← hs] at hm
          contradiction
      · rw [Bool.eq_false_iff.mpr hw]
        rfl
    · change some spans = terminalSpans D u w v at hs
      obtain ⟨he, hw⟩ := terminalSpans_sound D u w v spans hs.symm
      rw [hw, splitPayload_eq, he]

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.terminalPayload_replay
