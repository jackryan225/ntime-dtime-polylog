-- Source: P1SolScoutGrp/IndexBudget.lean, row_positions_le.
import P1Int.WitnessFit
import P1Int.FormAg
import P1ChkGreedy.Local

namespace P1SolGreedy.SolBridge.ScoutRow

open P1Wrap P1Wit

theorem row_positions_le {K : Consts} {aM C t zl : ℕ} {D : Dims}
    (h : SpaceIn K aM C t D zl) (l : ℕ) (hl : l ≤ D.top) :
    (D.lv l).bases * (D.lv l).lanes ≤ C * D.I * D.N * (Params.p t + 1) := by
  refine le_trans ?_ h.pos_le
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((D.lv j).bases * (D.lv j).lanes))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

end P1SolGreedy.SolBridge.ScoutRow
