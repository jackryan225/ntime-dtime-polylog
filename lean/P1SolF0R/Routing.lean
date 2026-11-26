import P1SolF0R.RouteTables
import P1SolF0R.CrossHeader

namespace P1SolF0R.SolReader

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1ChkFinal.AstraC10 P1SolFactor P1SolFactor.Owner
open scoped P1ChkFinal.AstraC10

/-- A constant number of copies of a row-count clock. -/
def repeatClock : ℕ → Tally → Tally
  | 0, _ => []
  | k + 1, clock => clock ++ repeatClock k clock

theorem repeatClock_poly (k : ℕ) : Poly (repeatClock k) := by
  induction k with
  | zero => exact Code.Poly.const []
  | succ k ih =>
    exact Code.Poly.app Poly.identity ih

theorem repeatClock_length (k : ℕ) (clock : Tally) : (repeatClock k clock).length = k * clock.length := by
  induction k with
  | zero => simp only [repeatClock, List.length_nil, Nat.zero_mul]
  | succ k ih => simp only [repeatClock, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

def unaryTables (xs : List ℕ) : List Tally × List Tally :=
  (tallyRows xs, tallyRows (inverseRows xs))

theorem unaryTables_poly : Poly unaryTables :=
  tallyRows_poly.pair (inverseRows_poly.compose tallyRows_poly)

theorem unaryTables_eq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    unaryTables (P1Benes.Tab.tabOf π) = ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally) := by
  simp only [unaryTables, inverseRows_eq, tallyRows_eq]

def contentTables (p : Tally × List ℕ) : List Tally × List Tally :=
  unaryTables (forwardRows contentAt (p, repeatClock 8 (ruler p.2)))

theorem contentTables_poly : Poly contentTables := by
  have hr : Poly (fun p : Tally × List ℕ => ruler p.2) :=
    (Easy.ruler Easy.snd).poly
  exact (Poly.identity.pair (hr.compose (repeatClock_poly 8))).compose
    ((forwardRows_poly ([], []) contentAt_poly).compose unaryTables_poly)

def stateTables (p : Tally × Tally) : List Tally × List Tally :=
  unaryTables (forwardRows stateAt (p, repeatClock 2 p.2))

theorem stateTables_poly : Poly stateTables :=
  (Poly.identity.pair (Easy.snd.poly.compose (repeatClock_poly 2))).compose
    ((forwardRows_poly ([], []) stateAt_poly).compose unaryTables_poly)

section Content

variable {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K)

theorem contentAt_eq (j : Fin (2 ^ (3 + h))) :
    contentAt ((tally h, trueCenters σ ι k), j.val) =
      (((itemLabel 3 h).permCongr (accPerm I σ ι k)) j).val := by
  let i := (itemLabel 3 h).symm j
  have hi : (itemLabel 3 h i).val = j.val := congrArg Fin.val ((itemLabel 3 h).apply_symm_apply j)
  have hd : decodeLabel ((tally 3, tally h, 2 ^ h), j.val) = (i.1.val, i.2.val) := by
    rw [← hi]
    exact decodeLabel_eq i
  rw [contentAt_def]
  simp only [length_trueCenters, hd]
  rw [accessRow_eq, encodeLabel_eq]
  rfl

theorem contentTables_eq :
    let π := (bitWordFinEquiv (3 + h)).permCongr (accAddr I σ ι k)
    contentTables (tally h, trueCenters σ ι k) =
      ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally) := by
  have hn : (repeatClock 8 (ruler (trueCenters σ ι k))).length = 2 ^ (3 + h) := by
    rw [repeatClock_length, ruler_length, length_trueCenters, pow_add]
    rfl
  unfold contentTables
  rw [forwardRows_eq _ _ _ hn ((itemLabel 3 h).permCongr (accPerm I σ ι k)) (contentAt_eq σ ι k), unaryTables_eq]
  rfl

end Content

theorem stateAt_eq {h : ℕ} (j : Fin (2 ^ (1 + h))) :
    stateAt ((tally h, tally (2 ^ h)), j.val) = (((itemLabel 1 h).permCongr (stPerm h)) j).val := by
  let i := (itemLabel 1 h).symm j
  have hi : (itemLabel 1 h i).val = j.val := congrArg Fin.val ((itemLabel 1 h).apply_symm_apply j)
  have hd : decodeLabel ((tally 1, tally h, 2 ^ h), j.val) = (i.1.val, i.2.val) := by
    rw [← hi]
    exact decodeLabel_eq i
  unfold stateAt
  simp only [tally_length, hd]
  rw [stateRow_eq, encodeLabel_eq]
  rfl

theorem stateTables_eq (h : ℕ) :
    let π := (bitWordFinEquiv (1 + h)).permCongr (stAddr h)
    stateTables (tally h, tally (2 ^ h)) =
      ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally) := by
  have hn : (repeatClock 2 (tally (2 ^ h))).length = 2 ^ (1 + h) := by
    rw [repeatClock_length, tally_length, pow_add]
    rfl
  unfold stateTables
  rw [forwardRows_eq _ _ _ hn ((itemLabel 1 h).permCongr (stPerm h)) stateAt_eq, unaryTables_eq]
  rfl

/-- Apply the crossing interface using the dimension itself and the common coordinate convention. -/
theorem routeHeader_eq_dimension (cross : CrossIn → Bool)
    (hc : ∀ (n : ℕ) (π : Equiv.Perm (Fin (2 ^ (n + 1)))) (κ a : ℕ),
      cross ((tally n, ((P1Benes.Tab.tabOf π).map tally, (P1Benes.Tab.tabOf π.symm).map tally)),
        (tally κ, tally a)) = P1Benes.Tab.crossT n (P1Benes.Tab.tabOf π) (P1Benes.Tab.tabOf π.symm) κ a)
    (V : FiniteMultiTapeMachine) (m column : ℕ) [NeZero m]
    (π : Equiv.Perm (P1Net.Routing.Addr m)) (r : P1Net.Routing.Addr m) :
    let p := (bitWordFinEquiv m).permCongr π
    let s := P1Benes.NetBridge.bset m π
    let j := (bitWordFinEquiv m r).val
    routeHeader cross ((tally (m - 1), ((P1Benes.Tab.tabOf p).map tally, (P1Benes.Tab.tabOf p.symm).map tally)),
        (tally column, tally j)) =
      ruleCode V (.route (routeInChoice s column r) (routeOutChoice s column r)) := by
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
    have hl : P1Benes.label n = bitWordFinEquiv (n + 1) :=
      Equiv.ext (label_eq_bitWordFinEquiv n)
    simpa only [hl, Nat.add_sub_cancel] using routeHeader_eq cross hc V n column π r

/-- A request already carries the lane in label order. Only its type field needs reversal. -/
def requestLabel (p : RouteShape × AccessItem) : ℕ :=
  p.2.2 + p.1.2.2 * reverseNum (p.1.1, p.2.1)

theorem requestLabel_poly : Poly requestLabel := by
  have h : Poly (fun p : RouteShape × AccessItem => reverseNum (p.1.1, p.2.1)) :=
    (show Poly (fun p : RouteShape × AccessItem => (p.1.1, p.2.1)) from by fun_prop).compose
      reverseNum_poly
  unfold requestLabel
  fun_prop

theorem requestLabel_eq {t h : ℕ} (typ : BitWord t) (lane : BitWord h) :
    requestLabel ((tally t, tally h, 2 ^ h), ((laneEquiv t typ).val, P1ChkFinal.bwNum lane)) =
      (bitWordFinEquiv (t + h) (addrOf typ lane)).val := by
  simp only [requestLabel, reverseNum_lane, addressNumber, P1ChkFinal.bwNum]

theorem type3_number (π : BitWord 3) : num3 π = (laneEquiv 3 π).val := by
  revert π
  decide

theorem type1_number (π : BitWord 1) : (π 0).val = (laneEquiv 1 π).val := by
  revert π
  decide

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.contentTables_eq
#print axioms P1SolF0R.SolReader.stateTables_eq
