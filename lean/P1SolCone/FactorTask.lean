import P1SolCone.FactorFinish

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1ChkFinal P1ChkFinal.AstraC10 Module
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

noncomputable section Finish

variable {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] {d : ℕ}

abbrev FactorHeader (F : Type) := Tally × Bool × List (LevelCode F)

def factorHeader (state : ConeStateCode F) : FactorHeader F :=
  (() :: ruler state.2.1,state.1,state.2.2)

theorem factorHeader_poly : Poly (factorHeader (F := F)) := by
  have h : Easy (fun p : ConeStateCode F => ruler p.2.1) := (Easy.snd.compose Easy.fst).ruler
  have hs : Poly (fun p : ConeStateCode F => () :: ruler p.2.1) := (Code.Poly.const ()).pair h.poly |>.compose Poly.cons
  exact hs.pair (Easy.fst.poly.pair (Easy.snd.compose Easy.snd).poly)

def factorRequest (state : ConeStateCode F) : Label F × List KeyCode :=
  (⟨1⟩,state.2.1)

theorem factorRequest_poly : Poly (factorRequest (F := F)) :=
  (Code.Poly.const (⟨1⟩ : Label F)).pair (Easy.snd.compose Easy.fst).poly

def factorReply (b : Basis (Fin d) (ZMod 2) F) (eval : EncodedLevels F → List Bool)
    (p : List (Label F) × Bool × List (LevelCode F)) : List Bool :=
  bif p.2.1 then eval ((p.2.2,p.1),[]) else coords b 0

theorem factorReply_poly (b : Basis (Fin d) (ZMod 2) F) {eval : EncodedLevels F → List Bool}
    (he : Poly eval) : Poly (factorReply b eval) := by
  exact Poly.choose (Easy.snd.compose Easy.fst).poly
    ((show Poly (fun p : List (Label F) × Bool × List (LevelCode F) => ((p.2.2,p.1),([] : Tally))) from by
      exact ((Easy.snd.compose Easy.snd).poly.pair Easy.fst.poly).pair (Code.Poly.const [])).compose he)
    (Code.Poly.const (coords b 0))

private theorem factor_domPair {X A B : Type*} [Codec A] [Codec B] {σ : X → ℕ} {u : X → A} {v : X → B}
    (hu : Dom σ (fun x => size (u x))) (hv : Dom σ (fun x => size (v x))) :
    Dom σ (fun x => size (u x,v x)) :=
  ((hu.add hv).add (Dom.const σ 1)).mono (fun x => by rw [size_prod])

set_option maxHeartbeats 1200000 in
theorem finishFactor_task {X : Type*} (bs : Basis (Fin d) (ZMod 2) F)
    (u x : X → List Bool) (state : X → ConeStateCode F) (σ scan : X → ℕ)
    (hstate : Dom σ (fun p => size (state p)))
    (hscan : ∀ p, (x p).length + (u p).length + 1 ≤ scan p)
    (hx : Dom σ (fun p => Nat.log 2 ((x p).length+1)))
    (factors : Factor0In F → List (Label F)) (e : ℕ)
    (hf : Computes (fun p : Factor0In F => p.1.1.length + p.1.2.length +
      (size p.2 + Nat.log 2 (p.1.1.length+1) + 1)^e) factors)
    (eval : EncodedLevels F → List Bool) (he : Poly eval) :
    ∃ cost : X → ℕ, Dom σ cost ∧ Task (fun p => scan p + cost p)
      (fun p => send ((x p,u p),state p))
      (fun p => send (factorReply bs eval
        ((factors ((x p,u p), factorRequest (state p))).take ((state p).2.1.length+1),
          (state p).1,(state p).2.2))) := by
  let word (p : X) := (x p,u p)
  let fr (p : X) := factorRequest (state p)
  let hd (p : X) := factorHeader (state p)
  let src (p : X) : Factor0In F := (word p,fr p)
  let vals (p : X) := factors (src p)
  let cut (p : X) := (hd p).1
  let aux (p : X) := (hd p).2
  let pre (p : X) := (vals p).take (cut p).length
  let localF (p : X) := (size (fr p) + Nat.log 2 ((x p).length+1) + 1)^e
  have hhd : Dom σ (fun p => size (hd p)) := (factorHeader_poly.length.map state).sub hstate
  have hr : Dom σ (fun p => size (fr p)) := (factorRequest_poly.length.map state).sub hstate
  have hsplit (p : X) : size (hd p) = size (cut p) + size (aux p) + 1 := rfl
  have hc : Dom σ (fun p => size (cut p)) := hhd.mono (fun p => by rw [hsplit]; omega)
  have ha : Dom σ (fun p => size (aux p)) := hhd.mono (fun p => by rw [hsplit]; omega)
  have ht : Dom σ localF := ((hr.add hx).add (Dom.const σ 1)).pow e
  have hlen : Dom σ (fun p => (cut p).length) := hc.mono (fun p => (duration (cut p)).le)
  have hpre : Dom σ (fun p => size (pre p)) :=
    ((hlen.mul (Dom.const σ (2 * Fintype.card F + 2))).add (Dom.const σ 1)).mono
      (fun p => factorsPrefix_size (vals p) (cut p).length)
  obtain ⟨t₀,ht₀,prep⟩ := (factorRequest_poly.pair factorHeader_poly).on hstate
  have arrange : Easy (fun z : (List Bool × List Bool) × ((Label F × List KeyCode) × FactorHeader F) =>
      ((z.1,z.2.1),z.2.2)) := by fun_prop
  have Hrun := hf.on src
  obtain ⟨m, hm⟩ := Hrun.sizeBound
  have swap : Easy (fun z : List (Label F) × FactorHeader F => ((z.2.1,z.1),z.2.2)) := by fun_prop
  have cutTask := factorsPrefix_easy.on (fun p => (cut p,vals p))
  obtain ⟨t₁,ht₁,giveResult⟩ := (factorReply_poly bs he).on (factor_domPair hpre ha)
  have exe := (prep.right (fun p => send (word p)))
    |>.compose (arrange.on (fun p => (word p,fr p,hd p)))
    |>.compose (Hrun.left (fun p => send (hd p)))
    |>.compose (swap.on (fun p => (vals p,hd p)))
    |>.compose (cutTask.left (fun p => send (aux p)))
    |>.compose giveResult
  let tail (p : X) := t₀ p + t₁ p + (2*m+1)*localF p + 3*size (fr p) + size (cut p) +
    2*size (hd p) + (2*m + 10)
  have ht' : Dom σ tail :=
    (((((ht₀.add ht₁).add ((Dom.const _ (2*m+1)).mul ht)).add ((Dom.const _ 3).mul hr)).add hc).add
      ((Dom.const _ 2).mul hhd)).add (Dom.const _ (2*m+10))
  refine ⟨tail,ht', (exe.bound (20+2*m) (fun p => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun p => by
    simp only [pre, vals, src, word, fr, cut, hd, factorHeader, List.length_cons, ruler_length, aux])⟩
  have hw : size (word p) = 2*(x p).length + 2*(u p).length + 3 := by
    unfold word
    simp only [size_prod,size_listBool]
    omega
  have hi : (send (src p)).count = size (word p) + size (fr p) + 1 := rfl
  have ho : (send (vals p)).count = size (vals p) := rfl
  have hp : size (word p,fr p,hd p) = size (word p) + size (fr p) + size (hd p) + 2 := by
    change size (word p,(fr p,hd p)) = _
    rw [size_prod (word p,(fr p,hd p)),size_prod (fr p,hd p)]
    dsimp only
    omega
  have hswap : size (vals p,hd p) = size (vals p) + size (hd p) + 1 := rfl
  have hcut : size (cut p,vals p) = size (cut p) + size (vals p) + 1 := rfl
  have hword : (send (word p)).count = size (word p) := rfl
  have hz := hm p
  change (send (vals p)).count ≤ (send (src p)).count + m * ((x p).length + (u p).length + localF p + 1) at hz
  rw [hi,ho,hw,show (x p).length + (u p).length + localF p + 1 =
    ((x p).length + (u p).length + 1) + localF p by omega, Nat.mul_add] at hz
  have hc₀ := hscan p
  have hm' := Nat.mul_le_mul_left m hc₀
  change size (word p) + t₀ p + size (word p,fr p,hd p) +
    ((x p).length+(u p).length+localF p) + size (vals p,hd p) +
    size (cut p,vals p) + t₁ p + 1 ≤ (20+2*m)*(scan p+tail p+1)
  simp only [hp,hswap,hcut,hw]
  have hscale : (20+2*m)*(scan p+tail p+1) =
      20*scan p + 2*(m*scan p) + tail p + (19+2*m)*tail p + (20+2*m) := by ring
  rw [hscale]
  have hn : size (vals p) ≤ 2*(x p).length+2*(u p).length+4+size (fr p)+m*scan p+m*localF p := by omega
  unfold tail
  simp only [Nat.add_mul,Nat.mul_assoc,Nat.one_mul]
  omega

end Finish

end P1SolCone.SolCone
