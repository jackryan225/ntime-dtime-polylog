import P1SolCone.PhaseMatch

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

abbrev PhaseInput (F : Type) := PhaseHeader × (Tally × ℕ) × ConeStateCode F

def stepPhaseCode {F : Type} [CommRing F] [Fintype F]
    (lim slots parents : ℕ) (extra : PhaseHeader × ℕ → List FieldKey)
    (kernel : PhaseLocal × KeyCode × List KeyCode → Label F)
    (u : List Bool) (p : PhaseInput F) : ConeStateCode F :=
  let source := phaseLocalOf lim extra u p.1 p.2.1.1 p.2.1.2 p.2.2.2.1
  advanceConeCode parents (localAllowed lim parents) (localParents lim) (localHalves slots) kernel (source,p.2.2)

theorem onePhase_task {X F : Type} [CommRing F] [Fintype F] (lim slots parents : ℕ)
    (extra : PhaseHeader × ℕ → List FieldKey) (kernel : PhaseLocal × KeyCode × List KeyCode → Label F)
    (he : Poly extra) (hk : Poly kernel) (u : X → List Bool) (p : X → PhaseInput F) (σ : X → ℕ)
    (hsize : Dom σ (fun x => size (p x))) (hlen : ∀ x, (p x).1.2.1 = (u x).length)
    (hex : ∀ x y k, k ∈ extra ((p x).1,y) → k.1 ≤ (p x).1.2.1 ∧ k.2 ≤ (p x).1.1.length) :
    ∃ cost : X → ℕ, Dom σ cost ∧
      Task (fun x => 30 * (u x).length + cost x) (fun x => send (u x,p x))
        (fun x => send (u x,stepPhaseCode lim slots parents extra kernel (u x) (p x))) := by
  let A := PhaseInput F
  let hd (x : X) := (p x).1
  let keys (x : X) := (p x).2.2.2.1
  let info (x : X) := (hd x,phaseRoots lim (hd x) (keys x))
  let rootSetup (z : A) := (z.1,phaseRoots lim z.1 z.2.2.2.1)
  have hroot : Poly rootSetup := Easy.fst.poly.pair
    ((show Poly (fun z : A => (z.1,z.2.2.2.1)) from by unfold A; fun_prop).compose (phaseRoots_poly lim))
  have hinfo : Dom σ (fun x => size (info x)) := (hroot.length.map p).sub hsize
  let visited (x : X) := phaseVisited lim extra (u x) (hd x) (keys x)
  let inc (x : X) := phaseIncidence lim extra (u x) (hd x) (keys x)
  let walked (x : X) := ((hd x,visited x),inc x)
  obtain ⟨⟨t₁,h₁,walk⟩,hw⟩ :=
    rawWalk_task extra he u hd (fun x => (info x).2) σ hinfo hlen hex 3
  obtain ⟨t₀,h₀,setup⟩ := (Code.Poly.identity.pair hroot).on hsize
  have f₁ : Easy (fun z : List Bool × (A × (PhaseHeader × List ℕ)) => (z.2.1,(z.1,z.2.2))) := by
    fun_prop
  let W := (PhaseHeader × List ℕ) × FieldCache
  have f₂ : Easy (fun z : A × (List Bool × W) => (z.2.1,z.1,z.2.2)) := by
    fun_prop
  have start := (setup.right (fun x => send (u x))).compose (f₁.on (fun x => (u x,p x,info x)))
  have fetchInc := start.compose (walk.right (fun x => send (p x)))
  have withWalked := fetchInc.compose (f₂.on (fun x => (p x,u x,walked x)))
  let preIn (x : X) := (p x,walked x)
  have hpre : Dom σ (fun x => size (preIn x)) :=
    ((hsize.add hw).add (Dom.const σ 1)).mono (fun x => by unfold preIn; rw [size_prod]; rfl)
  let P := A × FieldCache × List PositionCode
  let pack (z : A × W) : P := (z.1,z.2.2,phaseParents lim z.1.1 z.2.2 z.1.2.2.2.1)
  have hp : Poly pack := by
    have args : Poly (fun z : A × W => (z.1.1,z.2.2,z.1.2.2.2.1)) := by unfold A W; fun_prop
    exact Easy.fst.poly.pair (Easy.snd.poly.sndCompose.pair (args.compose (phaseParents_poly lim)))
  let prepped (x : X) := pack (preIn x)
  have hpack : Dom σ (fun x => size (prepped x)) := (hp.length.map preIn).sub hpre
  obtain ⟨t₂,h₂,preparation⟩ := hp.on hpre
  let widthKeys (z : P) := phaseWidthRequests z.1.1 z.2.1 z.2.2
  have widthKeysPoly : Poly widthKeys :=
    (show Poly (fun z : P => (z.1.1,z.2.1,z.2.2)) from by unfold P A; fun_prop).compose phaseWidthRequests_poly
  obtain ⟨⟨t₃,h₃,widthTask⟩,hWithWidth⟩ := phaseBatch_task
    (fun z : P => z.1.1) widthKeys Easy.fst.poly.fstCompose widthKeysPoly u prepped σ hpack hlen
    (fun x _ h => phaseWidthRequests_bounds h)
  let advance (z : P × FieldCache) : ConeStateCode F :=
    advanceConeCode parents (localAllowed lim parents) (localParents lim) (localHalves slots) kernel
      ((z.1.1.1,z.1.2.1,z.2,z.1.1.2.1.1,z.1.1.2.1.2),z.1.1.2.2)
  have ha : Poly advance := by
    have cfg : Poly (fun z : P × FieldCache =>
        ((z.1.1.1,z.1.2.1,z.2,z.1.1.2.1.1,z.1.1.2.1.2),z.1.1.2.2)) := by unfold P A; fun_prop
    exact cfg.compose (advanceConeCode_poly parents (localAllowed_poly lim parents) (localParents_poly lim)
      (localHalves_poly slots) hk)
  obtain ⟨t₄,h₄,done⟩ := ha.on hWithWidth
  have exe₀ := withWalked.compose (preparation.right (fun x => send (u x)))
  have exe₁ := exe₀.compose widthTask
  have exe := exe₁.compose (done.right (fun x => send (u x)))
  let cost (x : X) := t₀ x+t₁ x+t₂ x+t₃ x+t₄ x+3*size (p x)+size (info x)+size (walked x)+10
  refine ⟨cost, (((((((h₀.add h₁).add h₂).add h₃).add h₄).add
    ((Dom.const σ 3).mul hsize)).add hinfo).add hw).add (Dom.const σ 10), ?_⟩
  refine (exe.mono (fun x => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hu : (send (u x)).count = size (u x) := rfl
  have hc : (send (p x)).count = size (p x) := rfl
  have hf₁ : size (u x,p x,info x) = size (u x) + (size (p x) + size (info x) + 1) + 1 := rfl
  have hf₂ : size (p x,u x,walked x) = size (p x) + (size (u x) + size (walked x) + 1) + 1 := rfl
  simp only [hu,hc,hf₁,hf₂,P1ChkFinal.size_listBool,cost]
  omega

end P1SolCone.SolCone
