import P1SolCone.PhaseC10
import P1SolCone.PhaseMatch

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1P5.KW
open scoped P1ChkFinal.AstraC10
open private levelConstant from P1Wit.SpaceFacts

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

def cachedShrinkBall (dH : ℕ) (h : PhaseHeader) (c : FieldCache) (x : ℕ) :
    List (ℕ × Option ShrinkDatumCode) :=
  ballList (cachedValidNeighbors h c) (P1SolC10P.SolC10prog.readShrink dH h c) x 3

def cachedRefreshBall (dH : ℕ) (h : PhaseHeader) (c : FieldCache) (x : ℕ) :
    List (ℕ × Option RefreshDatumCode) :=
  ballList (cachedValidNeighbors h c) (P1SolC10P.SolC10prog.readRefresh dH h c) x 1

private theorem cachedValidNeighbors_poly_pair :
    Poly (fun p : (PhaseHeader × FieldCache) × ℕ => cachedValidNeighbors p.1.1 p.1.2 p.2) :=
  (show Poly (fun p : (PhaseHeader × FieldCache) × ℕ => (p.1.1,p.1.2,p.2)) from by fun_prop).compose
    cachedValidNeighbors_poly

theorem cachedShrinkBall_poly (dH : ℕ) :
    Poly (fun p : (PhaseHeader × FieldCache) × ℕ => cachedShrinkBall dH p.1.1 p.1.2 p.2) :=
  poly_ballList_fixed cachedValidNeighbors_poly_pair (P1SolC10P.SolC10prog.poly_readShrink dH) 3

theorem cachedRefreshBall_poly (dH : ℕ) :
    Poly (fun p : (PhaseHeader × FieldCache) × ℕ => cachedRefreshBall dH p.1.1 p.1.2 p.2) :=
  poly_ballList_fixed cachedValidNeighbors_poly_pair (P1SolC10P.SolC10prog.poly_readRefresh dH) 1

abbrev PhaseKernelInput := PhaseLocal × KeyCode × List KeyCode

def kernelForebear (p : PhaseKernelInput) : ℕ :=
  p.2.1.1.1 / P1SolC10P.SolC10prog.childFactor p.1.1

def kernelChildTag (p : PhaseKernelInput) : ℕ :=
  p.2.1.1.1 % P1SolC10P.SolC10prog.childFactor p.1.1

theorem kernelForebear_poly : Poly kernelForebear := by
  unfold kernelForebear
  fun_prop

theorem kernelChildTag_poly : Poly kernelChildTag := by
  unfold kernelChildTag
  fun_prop

def cachedShrinkKIn (dH : ℕ) (p : PhaseKernelInput) : ShrinkKIn :=
  let h := p.1.1
  let c := p.1.2.1
  let x := kernelForebear p
  packShrinkKIn ((((x,cachedShrinkBall dH h c x),decide (rawRead h c .layout 0 = 1)),
    (kernelChildTag p,p.2.1.1.2)), (p.2.2,p.2.1.2)) p.1.2.2.2.1

def cachedRefreshKIn (dH : ℕ) (p : PhaseKernelInput) : RefreshKIn :=
  let h := p.1.1
  let c := p.1.2.1
  let x := kernelForebear p
  (((x,cachedRefreshBall dH h c x),(kernelChildTag p,p.2.1.1.2)), (p.2.2,p.2.1.2))

theorem cachedShrinkKIn_poly (dH : ℕ) : Poly (cachedShrinkKIn dH) := by
  unfold cachedShrinkKIn packShrinkKIn
  have panel : Poly (fun p : PhaseKernelInput => (p.1.1,p.1.2.1)) := by fun_prop
  have cells := (panel.pair kernelForebear_poly).compose (cachedShrinkBall_poly dH)
  have key : Poly (fun p : PhaseKernelInput => (p.1.1,p.1.2.1,0)) := by fun_prop
  have lay := poly_eqNat (key.compose (rawRead_poly .layout)) (Code.Poly.const 1)
  have lan : Poly (fun p : PhaseKernelInput => p.2.1.1.2) := by fun_prop
  have payload : Poly (fun p : PhaseKernelInput => (p.2.2,p.2.1.2)) := by fun_prop
  have pad : Poly (fun p : PhaseKernelInput => p.1.2.2.2.1) := by fun_prop
  exact ((((kernelForebear_poly.pair cells).pair lay).pair
    (kernelChildTag_poly.pair lan)).pair payload).pair pad

theorem cachedRefreshKIn_poly (dH : ℕ) : Poly (cachedRefreshKIn dH) := by
  unfold cachedRefreshKIn
  have panel : Poly (fun p : PhaseKernelInput => (p.1.1,p.1.2.1)) := by fun_prop
  have cells := (panel.pair kernelForebear_poly).compose (cachedRefreshBall_poly dH)
  have lan : Poly (fun p : PhaseKernelInput => p.2.1.1.2) := by fun_prop
  have payload : Poly (fun p : PhaseKernelInput => (p.2.2,p.2.1.2)) := by fun_prop
  exact ((kernelForebear_poly.pair cells).pair (kernelChildTag_poly.pair lan)).pair payload

def cachedPhaseKernel {F : Type} (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (dH : ℕ) (p : PhaseKernelInput) : Label F :=
  bif phaseShrinkBit p.1.1 then shr (P1SolC10P.SolC10prog.oldBits p.1.1,cachedShrinkKIn dH p)
    else ref (cachedRefreshKIn dH p)

theorem cachedPhaseKernel_poly {F : Type} [Fintype F] (shr : ℕ × ShrinkKIn → Label F) (ref : RefreshKIn → Label F)
    (hs : Poly shr) (hr : Poly ref) (dH : ℕ) : Poly (cachedPhaseKernel shr ref dH) := by
  unfold cachedPhaseKernel
  have h : Poly (fun p : PhaseKernelInput => p.1.1) := by fun_prop
  have a : Poly (fun p : PhaseKernelInput => P1SolC10P.SolC10prog.oldBits p.1.1) := by fun_prop
  exact Poly.choose (h.compose phaseShrinkBit_poly) ((a.pair (cachedShrinkKIn_poly dH)).compose hs)
    ((cachedRefreshKIn_poly dH).compose hr)

end P1SolCone.SolCone
