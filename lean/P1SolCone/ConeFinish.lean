import P1SolCone.TraceTask
import P1SolCone.FactorTask
import P1P5.ConeTarget

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW P1Int P1Int.P11 Module
open scoped P1ChkFinal.AstraC10

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
variable {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] {Dd : ℕ}

def finishTrace (bs : Basis (Fin Dd) (ZMod 2) F) (evaluate : EncodedLevels F → List Bool)
    (factors : Factor0In F → List (Label F)) (x u : List Bool) (state : CheckedTableState F) : List Bool :=
  let s := encodeConeState state
  factorReply bs evaluate ((factors ((x,u),factorRequest s)).take (s.2.1.length+1),s.1,s.2.2)

private theorem foldDead (allow : ℕ → KeyCode → Bool)
    (pre : ℕ → PositionCode → List PositionCode) (half : ℕ → PositionCode → List HalfCode)
    (kernel : ℕ → KeyCode → List KeyCode → F) (ls : List ℕ) :
    ls.foldl (advanceChecked allow pre half kernel) none = none := by
  induction ls with
  | nil => rfl
  | cons l ls ih => exact ih

set_option maxHeartbeats 1600000 in
theorem finishTrace_eq (bs : Basis (Fin Dd) (ZMod 2) F) (evaluate : EncodedLevels F → List Bool)
    (he : ∀ (Ls : List (P1P5.Level F)) (st : List F) (i : ℕ),
        evaluate ((Ls.map P1P5.encLevel, st.map Label.mk), tally i) =
          coords bs ((P1P5.runLevels Ls st).getD i 0))
    (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (factors : Factor0In F → List (Label F)) (q : Qry) :
    finishTrace bs evaluate factors q.1 q.2.1
      (queryTrace B V a b d bigBias termBias shr ref q (queryIndices B V a b d bigBias termBias q)) =
    coords bs (P1P5.Cone.coneWof B V a b d bigBias termBias (numericKernelValues shr ref) factors
      q.1 q.2.1 (P1Batch.bval q.2.2)) := by
  let D := coneDims B V a b d bigBias termBias q.1.length
  let width := Mbar B V a b q.1.length
  let x := q.1
  let u := q.2.1
  let v := P1Batch.bval q.2.2
  let p := (v / (D.lv D.top).lanes,v % (D.lv D.top).lanes)
  let allow := phaseAllowed D u B.recordLimit width
  let pre := phasePreimages D u
  let halves := phaseHalves D u
  let kr := phaseKernel (numericKernelValues shr ref) (conePad B.growthConstant width)
    (2 ^ S.expanderExponent) D u
  let ls := List.range D.top
  have hT : queryTrace B V a b d bigBias termBias shr ref q (queryIndices B V a b d bigBias termBias q) =
      ls.reverse.foldl (advanceChecked allow pre halves kr) (initialConeState D u width v) := by
    simp only [queryTrace,queryIndices,queryInitial,checkedPhaseStep,bval_bin,ls,allow,pre,halves,kr,D,x,u,v,width]
  rw [hT]
  have dead : finishTrace bs evaluate factors x u none = coords bs 0 := rfl
  unfold P1P5.Cone.coneWof Wof initialConeState
  change finishTrace bs evaluate factors x u
    (ls.reverse.foldl (advanceChecked allow pre halves kr)
      (if D.fixedLen ≤ u.length ∧ v < finP D then
        if widthsWithin width (readHalfWidths D u D.top p) then
          (readFinalHalf D u v).map (fun half => ([(p,half)],[]))
        else none
      else none)) =
    coords bs
      (if D.fixedLen ≤ u.length ∧ v < finP D then
        if widthsWithin width (readHalfWidths D u D.top p) then
          match readFinalHalf D u v with
          | none => 0
          | some z => match assembleCheckedChain allow pre halves kr ls [(p,z)] with
            | none => 0
            | some (ks, levels) => (P1P5.runLevels levels ((factors ((x,u),(⟨1⟩,ks))).map Label.val)).getD 0 0
        else 0
      else 0)
  split
  next valid =>
    split
    next ok =>
      cases hZ : readFinalHalf D u v with
      | none =>
        change finishTrace bs evaluate factors x u (ls.reverse.foldl (advanceChecked allow pre halves kr) none) =
          coords bs 0
        rw [foldDead,dead]
      | some z =>
        change finishTrace bs evaluate factors x u (ls.reverse.foldl (advanceChecked allow pre halves kr)
          (some ([(p,z)],[]))) = coords bs
          (match assembleCheckedChain allow pre halves kr ls [(p,z)] with
          | none => 0
          | some (ks, levels) => (P1P5.runLevels levels ((factors ((x,u),(⟨1⟩,ks))).map Label.val)).getD 0 0)
        rw [← assembleChecked_eq_fold]
        cases run : assembleCheckedChain allow pre halves kr ls [(p,z)] with
        | none => exact dead
        | some output =>
          obtain ⟨ks, tab⟩ := output
          let initial := factors ((x,u),(⟨1⟩,ks))
          let short := initial.take (ks.length+1)
          have hlist (st : List (Label F)) : (st.map Label.val).map Label.mk = st := by
            induction st with
            | nil => rfl
            | cons v vs ih => simpa only [List.map_cons, ih]
          have hcut : (initial.map Label.val).take (ks.length+1) = short.map Label.val :=
            List.map_take.symm
          change evaluate ((tab.map P1P5.encLevel,short),tally 0) =
            coords bs ((P1P5.runLevels tab (initial.map Label.val)).getD 0 0)
          have hp := he tab (short.map Label.val) 0
          rw [hlist] at hp
          rw [hp,← hcut, checkedLevels_take allow pre halves kr ls [(p,z)] ks tab run]
    next no => rw [foldDead,dead]
  next no => rw [foldDead,dead]

set_option maxHeartbeats 1300000 in
theorem coneExecution_interface (bs : Basis (Fin Dd) (ZMod 2) F)
    (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F) (hs : Poly shr) (hr : Poly ref)
    (factors : Factor0In F → List (Label F)) (e : ℕ)
    (hf : Computes (fun p : Factor0In F => p.1.1.length + p.1.2.length +
      (size p.2 + Nat.log 2 (p.1.1.length+1) + 1)^e) factors) :
    ∃ c : ℕ, ∀ M K : ℕ → ℕ,
      WHyp bs (P1P5.Cone.coneWof B V a b d bigBias termBias (numericKernelValues shr ref) factors) M K
        (P1SolCone.βW B V a b c) := by
  let σ := coneScale B V a b
  let scan := coneScan B a b
  let trace (q : Qry) := queryTrace B V a b d bigBias termBias shr ref q
    (queryIndices B V a b d bigBias termBias q)
  have hb : Dom σ (fun q => size (encodeConeState (trace q))) :=
    queryTrace_dom B V a b d bigBias termBias (id : Qry → Qry) (queryIndices B V a b d bigBias termBias) shr ref
      (fun _ _ h => List.mem_range.mp (List.mem_reverse.mp h))
      (fun q => by simp only [queryIndices,List.length_reverse,List.length_range,id_eq,le_refl])
  have hscan (q : Qry) : q.1.length + q.2.1.length + 1 ≤ scan q := by
    unfold scan coneScan
    exact (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans' (by omega)
  have hlog : Dom σ (fun q : Qry => Nat.log 2 (q.1.length+1)) := (Dom.base σ).mono (fun q => by
    have h : Nat.log 2 (q.1.length+1) ≤ coneQuerySize q := by unfold coneQuerySize; omega
    exact h.trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans (Nat.le_add_right _ _)))
  obtain ⟨eval,he,heEq⟩ := evalCoords_poly bs
  obtain ⟨t₀,ht₀,read⟩ := queryTrace_task B V a b d bigBias termBias shr ref hs hr
  obtain ⟨t₁,ht₁,finish⟩ := finishFactor_task bs (fun q : Qry => q.2.1) Prod.fst
    (fun q => encodeConeState (trace q)) σ scan hb hscan hlog factors e hf eval he
  have exe := read.compose finish
  refine coneTask_interface B V a b bs _ (fun q => t₀ q+t₁ q) (ht₀.add ht₁)
    ((exe.bound 2 (fun q => by dsimp only [scan]; omega)).conform (fun _ => rfl) (fun _ => rfl) (fun q => ?_))
  exact congrArg send (finishTrace_eq B V a b d bigBias termBias bs eval heEq shr ref factors q)

end

end P1SolCone.SolCone
