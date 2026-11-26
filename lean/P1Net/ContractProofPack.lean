import P1Net.ContractProofRunState

/-! Prescribe the physical outgoing edge words of one run, at their actual nominal widths. -/

namespace P1Net.AstraContract

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP Compression NetworkKernel WireTensor

variable {h : ℕ} (V : FiniteMultiTapeMachine) (B : ℕ) [NeZero B] (I : ℕ) [NeZero I]
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) {a : ℕ} (ha : 4 ≤ 2 ^ a)
  (bset : ∀ (m : ℕ) [NeZero m], Equiv.Perm (Routing.Addr m) → Routing.Settings m) (input : List Bool)

noncomputable def runStrings (t : ℕ) := extData V B (runIn (B := B) input t) (runOut input t)

noncomputable def runCArc (ι : Fin I) (k : V.K) (c : ℕ) (x : Routing.Addr (3 + h)) (b : Bool) :
    Fin (strWidth V B) → Bool :=
  canonicalArc (bset (3 + h) (accAddr I σ ι k))
    (fun u => runContentSource V B I σ input ι k ((itemEquiv h).symm u)) c x b

noncomputable def runSArc (ι : Fin I) (c : ℕ) (x : Routing.Addr (1 + h)) (b : Bool) :
    Fin (strWidth V B) → Bool :=
  canonicalArc (bset (1 + h) (stAddr h))
    (fun u => runStateSource V B h input ι ((stItemEquiv h).symm u)) c x b

noncomputable def runRaw (v : Fin I × Loc V.K h) (l : BitWord h) (s : Fin 4) (W : ℕ) : Fin W → Bool :=
  let j := laneEquiv h l
  let t := (v.1 : ℕ) * 2 ^ h + j
  match v.2 with
  | .tabC => asWord W (tupleWord V B (runStrings V B input t))
  | .tabP c => if s = 1 then asWord W (tupleWord V B (runStrings V B input t))
               else asWord W (runStrings V B input t c)
  | .portIn k δ => asWord W (runHistory V B I σ input k (portBlock I σ v.1 k δ j) ((v.1 : ℕ) * 2 ^ h))
  | .portOut k δ => asWord W (runHistory V B I σ input k (portBlock I σ v.1 k δ j) (((v.1 : ℕ) + 1) * 2 ^ h))
  | .eIn => asWord W (runBoundary V B h input ((v.1 : ℕ) * 2 ^ h) j)
  | .eOut => asWord W (runBoundary V B h input (((v.1 : ℕ) + 1) * 2 ^ h) j)
  | .rt k c π => asWord W (runCArc V B I σ bset input v.1 k c (addrOf π l) (decide (s = 1)))
  | .st c π => asWord W (runSArc V B I bset input v.1 c (addrOf π l) (decide (s = 1)))

noncomputable def runLabels : Labels V B I σ ha :=
  packSlots V B I σ ha (fun v l s => runRaw V B I σ bset input v l s (widthAt V B I v s))

local notation "zR" => runLabels V B I σ ha bset input
local notation "raw" => runRaw V B I σ bset input

theorem run_out {v : Fin I × Loc V.K h} {s : Fin 4} {W : ℕ}
    (hm : netMate I σ (v, s) ≠ none) (hw : widthAt V B I v s = W) (l : BitWord h) :
    slotOut V B I σ ha zR v l s W = raw v l s W := by
  subst W
  exact slotOut_pack_mated V B I σ ha _ hm l

theorem run_in {v v' : Fin I × Loc V.K h} {s s' : Fin 4} {W : ℕ}
    (hm : netMate I σ (v, s) = some (v', s')) (hw : widthAt V B I v' s' = W) (l : BitWord h) :
    slotIn V B I σ ha zR v l s W = raw v' (l + netDisp I σ (v,s)) s' W := by
  rw [slotIn_mate V B I σ ha zR hm l W]
  apply run_out V B I σ ha bset input _ hw (l + netDisp I σ (v,s))
  rw [netMate_symm I σ hm]
  exact Option.some_ne_none _

theorem run_local_in (ι : Fin I) {v v' : Loc V.K h} {s s' : Fin 4} {W : ℕ}
    (hm : locMate v s = some (v', s')) (d : disp1 I ((ι, v), s) = 0)
    (d' : disp1 I ((ι, v'), s') = 0) (hw : widthAt V B I (ι, v') s' = W) (l : BitWord h) :
    slotIn V B I σ ha zR (ι,v) l s W = raw (ι,v') l s' W := by
  rw [slotIn_local V B I σ ha zR ι hm d d' l W]
  apply run_out V B I σ ha bset input _ hw l
  rw [local_mate V I σ ι (locMate_symm hm)]
  exact Option.some_ne_none _

theorem run_local_out (ι : Fin I) {v v' : Loc V.K h} {s s' : Fin 4} {W : ℕ}
    (hm : locMate v s = some (v', s')) (hw : widthAt V B I (ι,v) s = W) (l : BitWord h) :
    slotOut V B I σ ha zR (ι,v) l s W = raw (ι,v) l s W := by
  apply run_out V B I σ ha bset input _ hw l
  rw [local_mate V I σ ι hm]
  exact Option.some_ne_none _

theorem runCArc_last (route : Routes bset) (ι : Fin I) (k : V.K) (y : Fin 8 × Fin (2 ^ h)) :
    runCArc V B I σ bset input ι k (rcolLast h) (itemEquiv h y) false =
      runContentDest V B I σ input ι k y := by
  have hc : (rcolLast h : ℕ) = 2 * (3 + h) - 1 := by
    change 2 * (h + 3) - 1 = _
    omega
  rw [runCArc, hc, last_arc_eq_prefix]
  exact last_prefix_conjugate (itemEquiv h) (accPerm I σ ι k) _ (route _ _) _ y

theorem runSArc_last (route : Routes bset) (ι : Fin I) (y : Fin 2 × Fin (2 ^ h)) :
    runSArc V B I bset input ι (scolLast h) (stItemEquiv h y) false = runStateDest V B h input ι y := by
  have hc : (scolLast h : ℕ) = 2 * (1 + h) - 1 := by
    change 2 * (h + 1) - 1 = _
    omega
  rw [runSArc, hc, last_arc_eq_prefix]
  exact (last_prefix_conjugate (stItemEquiv h) (stPerm h) _ (route _ _) _ y).trans
    (runStateSource_symm V B h input ι y)

end P1Net.AstraContract
