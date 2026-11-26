import P1SolCone.TraceDom

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
local notation "σ" => coneScale B V a b
local notation "Wn" q => bin (List.length (Prod.fst q))
local notation "Dq" q => coneDims B V a b d bigBias termBias (P1Batch.bval (Wn q))
local notation "Padq" q => conePad B.growthConstant (Mbar B V a b (P1Batch.bval (Wn q)))

def queryOrder (q : Qry) : List FullPhaseDescriptor :=
  fullScheduleInput B V a b d bigBias termBias (smallQuery q,Padq q)

theorem queryPad_dom : Dom σ (fun q : Qry => size (Padq q)) := by
  simpa only [bval_bin] using coneScale_padSize B V a b

theorem queryOrder_dom : Dom σ (fun q => size (queryOrder B V a b d bigBias termBias q)) :=
  ((fullScheduleInput_poly B V a b d bigBias termBias).length.map _).sub
    (dom_sizePair (smallQuery_dom B V a b) (queryPad_dom B V a b))

theorem queryOrder_size (q : Qry) : (queryOrder B V a b d bigBias termBias q).length = (Dq q).top := by
  unfold queryOrder
  rw [fullSchedule_eq]
  simp only [List.length_reverse,List.length_map,List.length_range]

theorem queryOrder_initTask {F : Type} [CommRing F] [Fintype F] :
    ∃ cost : Qry → ℕ, Dom σ cost ∧
    Task (fun q => coneScan B a b q + cost q) (fun q => send q)
      (fun q => send ((queryOrder B V a b d bigBias termBias q,
        (q.2.1,encodeConeState (queryInitial (F := F) B V a b d bigBias termBias q))),q.1)) := by
  let s (q : Qry) := encodeConeState (queryInitial (F := F) B V a b d bigBias termBias q)
  let wdata (q : Qry) := (q.1,q.2.1)
  let msg (q : Qry) := smallQuery q
  let e (q : Qry) := coneFuelExponent B V a b (Wn q)
  let pad (q : Qry) := Padq q
  let order := queryOrder B V a b d bigBias termBias
  have hs : Dom σ (fun q => size (s q)) := by
    simpa only [queryTrace,List.foldl_nil,Function.comp_def,id_eq] using
      queryTrace_dom B V a b d bigBias termBias (id : Qry → Qry) (fun _ => [])
        (fun _ => (⟨0⟩ : Label F)) (fun _ => ⟨0⟩) (fun _ _ h => False.elim (List.not_mem_nil h))
        (fun _ => Nat.zero_le _)
  obtain ⟨t₀,ht₀,start⟩ := coneTerminal_headerTask B V a b d bigBias termBias (F := F)
  have begin : Task (fun q => coneScan B a b q + t₀ q) (fun q => send q)
      (fun q => send (wdata q,msg q,s q)) :=
    start.conform (fun _ => rfl) (fun _ => rfl) (fun q => by
      unfold s queryInitial wdata msg
      rw [bval_bin])
  have prepare : Easy (fun p : (List Bool × List Bool) × QueryWords × ConeStateCode F =>
    (p.2.1,(p.1,p.2.2))) := by fun_prop
  have powInput : Poly (fun p : QueryWords => (coneFuelExponent B V a b p.1,p)) :=
    (Easy.fst.poly.compose (coneFuelExponent_poly B V a b)).pair Code.Poly.identity
  obtain ⟨t₁,ht₁,expTask⟩ := powInput.on (smallQuery_dom B V a b)
  have computePad := (coneFuel_fromExponent B V a b).on (fun q : Qry => Wn q)
  have padTask := (computePad.left (fun q => send (msg q))).left (fun q => send (wdata q,s q))
  have arrange : Easy (fun p : (Tally × QueryWords) × (List Bool × List Bool) × ConeStateCode F =>
      ((p.1.2,p.1.1),p.2)) := by fun_prop
  obtain ⟨t₂,ht₂,orderTask⟩ := (fullScheduleInput_poly B V a b d bigBias termBias).on
    (dom_sizePair (smallQuery_dom B V a b) (queryPad_dom B V a b))
  have output : Easy (fun p : List FullPhaseDescriptor × (List Bool × List Bool) × ConeStateCode F =>
    ((p.1,p.2.1.2,p.2.2),p.2.1.1)) := by fun_prop
  have exe := begin
    |>.compose (prepare.on (fun q => (wdata q,msg q,s q)))
    |>.compose (expTask.left (fun q => send (wdata q,s q)))
    |>.compose padTask
    |>.compose (arrange.on (fun q => ((pad q,msg q),wdata q,s q)))
    |>.compose (orderTask.left (fun q => send (wdata q,s q)))
    |>.compose (output.on (fun q => (order q,wdata q,s q)))
  have hcostPad : Dom σ (fun q => 2 ^ (e q).length) := (queryPad_dom B V a b).mono
    (fun q => by simp only [e,coneFuelExponent,pad,conePad,tally_length,size_tally]; omega)
  let localCost (q : Qry) := t₀ q + t₁ q + t₂ q + 2 ^ (e q).length +
    2*size (msg q) + 3*size (s q) + size (pad q) + size (order q) + 30
  have hcost : Dom σ localCost :=
    ((((((((ht₀.add ht₁).add ht₂).add hcostPad).add ((Dom.const _ 2).mul (smallQuery_dom B V a b))).add
      ((Dom.const _ 3).mul hs)).add (queryPad_dom B V a b)).add
        (queryOrder_dom B V a b d bigBias termBias)).add (Dom.const σ 30))
  refine ⟨localCost,hcost,exe.bound 20 (fun q => ?_)⟩
  have hscan : q.1.length + q.2.1.length + q.2.2.length + 1 ≤ coneScan B a b q :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hw : size (wdata q) = 2*q.1.length + 2*q.2.1.length + 3 := by
    unfold wdata
    simp only [size_prod,P1ChkFinal.size_listBool]
    omega
  have h₁ : size (wdata q,msg q,s q) = size (wdata q) + size (msg q) + size (s q) + 2 := by
    rw [size_prod (wdata q,(msg q,s q)), size_prod (msg q,s q)]
    dsimp only
    omega
  have h₂ : size ((pad q,msg q),wdata q,s q) =
      size (pad q) + size (msg q) + size (wdata q) + size (s q) + 3 := by
    rw [size_prod ((pad q,msg q),(wdata q,s q)), size_prod (pad q,msg q), size_prod (wdata q,s q)]
    dsimp only
    omega
  have h₃ : size (order q,wdata q,s q) = size (order q) + size (wdata q) + size (s q) + 2 := by
    rw [size_prod (order q,(wdata q,s q)), size_prod (wdata q,s q)]
    dsimp only
    omega
  change coneScan B a b q + t₀ q + size (wdata q,msg q,s q) +
    t₁ q + 2 ^ (e q).length + size ((pad q,msg q),wdata q,s q) +
    t₂ q + size (order q,wdata q,s q) + 1 ≤ 20 * (coneScan B a b q + localCost q + 1)
  let s₀ := coneScan B a b q
  let loc := t₀ q + t₁ q + t₂ q + 2 ^ (e q).length +
    2*size (msg q) + 3*size (s q) + size (pad q) + size (order q)
  have hlarge : 3 * size (wdata q) + 8 ≤ 17*s₀ := by
    calc
      _ ≤ 17 * (q.1.length+q.2.1.length+q.2.2.length+1) := by rw [hw]; omega
      _ ≤ _ := Nat.mul_le_mul_left _ hscan
  have hsmall : loc ≤ localCost q := Nat.le_add_right _ _
  calc
    _ = (s₀ + loc) + (3*size (wdata q) + 8) := by
      rw [h₁,h₂,h₃]
      dsimp only [s₀,loc]
      ring
    _ ≤ (s₀ + localCost q) + 17*s₀ := Nat.add_le_add (Nat.add_le_add_left hsmall s₀) hlarge
    _ ≤ (s₀ + localCost q) + 17*(s₀ + localCost q) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 17 (Nat.le_add_right _ _)) _
    _ ≤ _ := by
      let n := s₀ + localCost q
      change n + 17*n ≤ 20*(n+1)
      omega

end

end P1SolCone.SolCone
