import P1SolCone.SetupSweep
import P1SolCone.PhaseSweep

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW P1Int P1Int.P11
open scoped P1ChkFinal.AstraC10
open private slotCap levelConstant from P1Wit.SpaceFacts

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)
local notation "σ" => coneScale B V a b
local notation "Wn" q => bin (List.length (Prod.fst q))
local notation "Dq" q => coneDims B V a b d bigBias termBias (P1Batch.bval (Wn q))

def queryIndices (q : Qry) : List ℕ := (List.range (Dq q).top).reverse

theorem queryIndices_lt {q : Qry} {l n : ℕ} (hl : l ∈ (queryIndices B V a b d bigBias termBias q).take n) :
    l < (Dq q).top :=
  List.mem_range.mp (List.mem_reverse.mp (List.mem_of_mem_take hl))

theorem queryIndices_take_len (q : Qry) (n : ℕ) :
    ((queryIndices B V a b d bigBias termBias q).take n).length ≤ (Dq q).top := by
  simp only [queryIndices,List.length_take,List.length_reverse,List.length_range,min_le_right]

variable {F : Type} [CommRing F] [Fintype F]
variable (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)

set_option maxHeartbeats 1500000 in
theorem queryOrder_fold (q : Qry) (n : ℕ) :
    ((queryOrder B V a b d bigBias termBias q).take n).foldl (conePhaseStep B shr ref q.2.1)
        (encodeConeState (queryInitial B V a b d bigBias termBias q)) =
      encodeConeState (queryTrace B V a b d bigBias termBias shr ref q
          ((queryIndices B V a b d bigBias termBias q).take n)) := by
  have he := fullSchedule_eq B V a b d bigBias termBias q
    (conePad B.growthConstant (Mbar B V a b (P1Batch.bval (Wn q))))
  change queryOrder B V a b d bigBias termBias q = _ at he
  rw [he, ← List.map_take]
  apply phaseFold_eq
  exact fun l hl => queryIndices_lt B V a b d bigBias termBias hl

set_option maxHeartbeats 1600000 in
theorem queryTrace_task (hs : Poly shr) (hr : Poly ref) :
    ∃ cost : Qry → ℕ, Dom σ cost ∧
      Task (fun q => coneScan B a b q + cost q) (fun q => send q)
        (fun q => send ((q.1,q.2.1),encodeConeState
          (queryTrace B V a b d bigBias termBias shr ref q (queryIndices B V a b d bigBias termBias q)))) := by
  let order := queryOrder B V a b d bigBias termBias
  let indices := queryIndices B V a b d bigBias termBias
  let init (q : Qry) := encodeConeState (queryInitial (F := F) B V a b d bigBias termBias q)
  let step (q : Qry) := conePhaseStep B shr ref q.2.1
  let final (q : Qry) := encodeConeState (queryTrace B V a b d bigBias termBias shr ref q (indices q))
  let Reach := ConeReach order
  let base (p : Reach) := p.val.2.2
  let head (p : Reach) := p.val.1
  let tail (p : Reach) := p.val.1 :: p.val.2.1
  let u (q : Qry) := q.2.1
  let prior (p : Reach) := coneBefore step init order (base p) (tail p)
  let pkt (p : Reach) : PhaseInput F := ((head p).1,(head p).2,prior p)
  have hm (p : Reach) : head p ∈ order (base p) := p.property.subset List.mem_cons_self
  have hhead : Dom (σ ∘ base) (fun p => size (head p)) :=
    ((queryOrder_dom B V a b d bigBias termBias).map base).mono (fun p => (size_bel (hm p)).le)
  have hsize : Dom (σ ∘ base) (fun p => size (prior p)) := by
    let n (p : Reach) := (order (base p)).length - (tail p).length
    have h := queryTrace_dom B V a b d bigBias termBias base (fun p => (indices (base p)).take (n p)) shr ref
      (fun _ _ hp => queryIndices_lt B V a b d bigBias termBias hp)
      (fun p => queryIndices_take_len B V a b d bigBias termBias (base p) (n p))
    refine h.mono (fun p => ?_)
    have eq := queryOrder_fold B V a b d bigBias termBias shr ref (base p) (n p)
    change prior p = _ at eq
    rw [eq]
  have hpacket : Dom (σ ∘ base) (fun p => size (pkt p)) :=
    ((hhead.add hsize).add (Dom.const _ 1)).mono (fun p => by
      change size ((head p).1,((head p).2,prior p)) ≤ _
      rw [size_prod ((head p).1,((head p).2,prior p)),size_prod ((head p).2,prior p),size_prod (head p)]
      dsimp only
      omega)
  have hlen : ∀ p, (pkt p).1.2.1 = (u (base p)).length := by
    intro p
    have h := hm p
    unfold order queryOrder at h
    rw [fullSchedule_eq] at h
    obtain ⟨l,_,e⟩ := List.mem_map.mp h
    change (head p).1.2.1 = _
    rw [← e]
    rfl
  obtain ⟨cost,hcost,exec⟩ := onePhase_task (levelConstant S) (slotCap S) B.recordLimit
    (kernelFieldKeys (2 ^ S.expanderExponent)) (cachedPhaseKernel shr ref (2 ^ S.expanderExponent))
    (kernelFieldKeys_poly _) (cachedPhaseKernel_poly shr ref hs hr _) (u ∘ base) pkt (σ ∘ base) hpacket hlen
    (fun p y k h => kernelFieldKeys_bounds _ (pkt p).1 y k h)
  have arrange : Easy (fun p : FullPhaseDescriptor × List Bool × ConeStateCode F =>
    (p.2.1,p.1.1,p.1.2,p.2.2)) := by fun_prop
  let cost' (p : Reach) := cost p + size (head p) + size (prior p) + 3
  have hcost' : Dom (σ ∘ base) cost' := ((hcost.add hhead).add hsize).add (Dom.const _ 3)
  have exec' : Task (fun p : Reach => 32*(u (base p)).length + cost' p)
      (fun p => send (head p,(u (base p),prior p)))
      (fun p => send (u (base p),step (base p) (prior p) (head p))) := by
    have go := (arrange.on (fun p : Reach => (head p,u (base p),prior p))).compose exec
    refine go.mono (fun p => ?_)
    have he : size (head p,u (base p),prior p) =
        size (head p) + (size (u (base p)) + size (prior p) + 1) + 1 := rfl
    simp only [he, size_listBool, Function.comp_def, cost']
    omega
  have ho : Dom σ (fun q => (order q).length) :=
    (queryOrder_dom B V a b d bigBias termBias).mono (fun q => (duration (order q)).le)
  obtain ⟨t₁,ht₁,sweep⟩ := phaseSweep_task u step init order σ 32 cost' hcost' ho hhead exec'
  obtain ⟨t₀,ht₀,start⟩ := queryOrder_initTask B V a b d bigBias termBias (F := F)
  have hfinal : Dom σ (fun q => size (final q)) := by
    have h := queryTrace_dom B V a b d bigBias termBias (id : Qry → Qry) indices shr ref
      (fun q l hl => List.mem_range.mp (List.mem_reverse.mp hl))
      (fun q => by simp only [indices,queryIndices,List.length_reverse,List.length_range,id_eq,le_refl])
    exact h
  have done (q : Qry) :
      (order q).foldl (step q) (init q) = final q := by
    have h := queryOrder_fold B V a b d bigBias termBias shr ref q (order q).length
    rw [List.take_length] at h
    have he : (order q).length = (indices q).length := by
      rw [queryOrder_size B V a b d bigBias termBias]
      simp only [indices,queryIndices,List.length_reverse,List.length_range]
    rw [he, List.take_length] at h
    exact h
  have move : Easy (fun p : (List Bool × ConeStateCode F) × List Bool => ((p.2,p.1.1),p.1.2)) := by fun_prop
  have swept : Task (fun q => 32 * (order q).length * (u q).length + t₁ q)
      (fun q => send ((order q,(u q,init q)),q.1))
      (fun q => send ((u q,final q),q.1)) :=
    (sweep.left (fun q => send q.1)).conform (fun _ => rfl) (fun _ => rfl) (fun q => by
      change send ((u q,(order q).foldl (step q) (init q)),q.1) = _
      rw [done q])
  have go := start.compose swept
  have exe := go.compose (move.on (fun q => ((u q,final q),q.1)))
  let rest (q : Qry) := t₀ q+t₁ q+size (final q)+5
  refine ⟨rest, ((ht₀.add ht₁).add hfinal).add (Dom.const _ 5), exe.bound 36 (fun q => ?_)⟩
  have htop : (order q).length = (S.steps+1)*P1Wrap.Params.T (portConsts B) (lpTime a b q.1.length) := by
    rw [queryOrder_size B V a b d bigBias termBias]
    change (coneDims B V a b d bigBias termBias (P1Batch.bval (Wn q))).top = _
    rw [bval_bin]
    exact genuine_top B (portConsts B) (toOAI V) 1 (lpTime a b q.1.length) (a * (q.1.length^2+1)) d bigBias termBias
  have hBig : (order q).length * (u q).length ≤ coneScan B a b q := by
    rw [htop]
    exact Nat.mul_le_mul (Nat.le_succ _) (by dsimp only [u]; omega)
  have hscan : q.1.length+(u q).length+1 ≤ coneScan B a b q :=
    (by dsimp only [u]; omega : _ ≤ q.1.length+q.2.1.length+q.2.2.length+1).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hmove : size ((u q,final q),q.1) = 2*(u q).length + size (final q) + 2*q.1.length+4 := by
    rw [size_prod ((u q,final q),q.1),size_prod (u q,final q)]
    simp only [size_listBool]
    omega
  simp only [hmove,rest,Nat.mul_assoc]
  omega

end

end P1SolCone.SolCone
