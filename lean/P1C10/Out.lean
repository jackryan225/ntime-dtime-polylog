import P1C10.Field

/-!
# P1C10.Out: family 9 in the field `out` of `D5Steps` (lane P1-lean-c10wire)

Every index of family 9 at stage 0 (`i ≥ cnt 9`, or level `i % 2^L ≥ top`) accepts: `d5_c10_out`, for any `D5Index`
with `cnt 9 = cntBase D`, `lev 9 i = i % 2 ^ levBits D`, `top = D.top` (`D = dims |x|`; integ's `fixedIndex` has the
last two by `rfl` at `dims |x| = fixedDims`).
-/

namespace P1C10

open P1Wit

/-- **Family 9 at stage 0 accepts** (the part of the field `out` of `D5Steps` for `c = 9`). -/
theorem d5_c10_out (fx : C10Fix) (dims : ℕ → Dims) (x : List Bool) (X : P1Int.P11.D5Index)
    (htop : X.top = (dims x.length).top) (hcnt : X.cnt 9 = P1ChkGreedy.cntBase (dims x.length))
    (hlev : ∀ i, X.lev 9 i = i % 2 ^ P1ChkGreedy.levBits (dims x.length))
    {U : Type*} (w : U → List Bool) (ck : U → ℕ → Bool) (hck : ∀ u i, ck u i = true ↔ C10w fx dims x (w u) i) :
    ∀ u i, X.stg 9 i = 0 → ck u i = true := by
  intro u i h
  rw [hck]
  by_cases hc : X.cnt 9 ≤ i
  · exact C10w_out fx dims x (w u) (show P1ChkGreedy.cntBase (dims x.length) ≤ i by rw [← hcnt]; exact hc)
  · have hl : ¬ X.lev 9 i < X.top := by
      intro hl
      unfold P1Int.P11.D5Index.stg at h
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos rfl, if_pos hl] at h
      omega
    intro hidx
    have h' := hidx
    unfold C10Idx at h'
    rw [hlev, htop] at hl
    exact absurd h'.1 hl

end P1C10

#print axioms P1C10.d5_c10_out
