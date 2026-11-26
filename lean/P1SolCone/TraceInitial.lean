import P1SolCone.InitialConeState
import P1SolCone.ConeTraceBounds

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

theorem terminalHalf_size (D : Dims) (u : List Bool) (w v : ℕ) (z : HalfCode)
    (hr : readFinalHalf D u v = some z)
    (hw : widthsWithin w (readHalfWidths D u D.top (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)) = true) :
    z.1.length = (D.lv D.top).slots ∧ z.2.length = (D.lv D.top).slots ∧
       ∀ word ∈ z.1 ++ z.2, word.length ≤ w := by
  have hSpan := terminalSpans_complete D u w v (by rw [hr]; rfl) hw
  cases h : terminalSpans D u w v with
  | none => rw [h] at hSpan; contradiction
  | some spans =>
    have zEq := (terminalSpans_sound D u w v spans h).1
    rw [hr] at zEq
    have newZ := Option.some.inj zEq
    subst z
    have widths (s : Span) (hs : s ∈ spans.1 ++ spans.2) : s.2 ≤ w := by
      unfold terminalSpans at h
      dsimp only at h
      split at h
      next ok =>
        have e := Option.some.inj h
        have hs' := e.symm ▸ hs
        have hs' := List.all_eq_true.mp ok.2.2.2 s hs'
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hs'
        exact hs'.2
      next => contradiction
    have spanLen : spans.1.length = (D.lv D.top).slots ∧ spans.2.length = (D.lv D.top).slots := by
      unfold terminalSpans at h
      dsimp only at h
      split at h
      next ok =>
        rw [← Option.some.inj h]
        simp only [terminalArcCodes,List.length_map,List.length_range, and_self]
      next => contradiction
    refine ⟨by simpa only [List.length_map] using spanLen.1,
      by simpa only [List.length_map] using spanLen.2, ?_⟩
    intro word hh
    rw [← List.map_append] at hh
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hh
    change (P1Batch.fetch u (spanRequest s)).length ≤ w
    unfold P1Batch.fetch spanRequest
    simp only [bval_bin, List.length_take]
    exact (min_le_left _ _).trans (widths s hs)

theorem initialConeState_shape {F : Type} (D : Dims) (u : List Bool) (w v : ℕ) (addr lane slots : ℕ)
    (haddr : v < 2 ^ addr) (hLane : (D.lv D.top).lanes ≤ lane) (hLanePos : 0 < (D.lv D.top).lanes)
    (hslots : (D.lv D.top).slots ≤ slots)
    (s : List KeyCode × List (P1P5.Level F))
    (h : initialConeState (F := F) D u w v = some s) :
    ∃ key, s = ([key],[]) ∧ keyFits addr lane slots w key := by
  let pos := (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)
  unfold initialConeState at h
  dsimp only at h
  split at h
  next ok =>
    split at h
    next hw =>
      cases hr : readFinalHalf D u v with
      | none => rw [hr] at h; contradiction
      | some half =>
        rw [hr] at h
        have hEq : ([(pos,half)],[]) = s := Option.some.inj h
        refine ⟨(pos,half),hEq.symm, ?_⟩
        obtain ⟨ho,hi,words⟩ := terminalHalf_size D u w v half hr hw
        exact ⟨(Nat.div_le_self _ _).trans_lt haddr, (Nat.mod_lt _ hLanePos).trans_le hLane,
          ho.le.trans hslots, hi.le.trans hslots,words⟩
    next => contradiction
  next => contradiction

end P1SolCone.SolCone
