import P1SolF0R.Interval
import P1Int.DirLinkProof

namespace P1SolF0R.SolReader

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11 P1Net P1Wit P1Wit.SolWitfill

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (B I : ℕ) [NeZero B] [NeZero I]
  {h : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ h) {D : Dims} {d : ℕ}

variable (H : NetRecordInputs Bt κ hκ V B I T hn D d) (tapeIndex : (toOAI V).K → ℕ)
  (hTape : ∀ tape, (H.tape_order tape).val = tapeIndex tape)

local notation "tuples" => P1Count.CountData.Tup (P1Count.NetData.toCountData
  (netData Bt κ hκ V a x B I (h := h) T hn (netSiteOrder Bt κ hκ V B I (h := h) T hn))) d
local notation "records" => p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H

include hTape in
/-- The first four sections of a genuine tuple contain the trits, starts and owners
in the specified tape numbering. -/
theorem genuine_directory (q : tuples) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload records q).length ≤ m) :
    let u := List.ofFn (encTuple records m q)
    (∀ (i : Fin (I * 2 ^ h)) (tape : (toOAI V).K),
      rdTrit D u i (tapeIndex tape) = (q.1 i tape).val) ∧
    (∀ (ι : Fin I) (tape : (toOAI V).K),
      rdStart D u ι (tapeIndex tape) = zigzag (betaOf q.1 tape (ι.val * 2 ^ h))) ∧
    (∀ (ι : Fin I) (tape : (toOAI V).K) (δ : Fin 3),
      rdPrev D u ι (tapeIndex tape) δ =
        P1ChkDir.ownToN (prevOwner I q.1 tape ι (portQ I q.1 tape ι δ))) ∧
    (∀ (ι : Fin I) (tape : (toOAI V).K) (δ : Fin 3),
      rdNext D u ι (tapeIndex tape) δ =
        P1ChkDir.ownToN (nextOwner I q.1 tape ι (portQ I q.1 tape ι δ))) := by
  cases D with
  | mk r numInt numLanes nGB top lv bigW wW chainLen chainW =>
    have hI : numInt = I := H.interval_count
    have hN : numLanes = 2 ^ h := H.initial_lanes
    subst numInt
    subst numLanes
    obtain ⟨ht, hs, hp, hh⟩ := readDirectory_encTuple
      (p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H) q m hm
    obtain ⟨dt, ds, dn, dp, _⟩ := dirLink_proof Bt κ hκ V a x B I T hn H q
    have hσ : dimSkel Bt κ hκ V B I T hn H q.1 = q.1 := by
      funext i tape
      rfl
    simp only [hσ, P1ChkDir.betaT, P1ChkDir.prevT_eq_prevOwner, P1ChkDir.nextT_eq_nextOwner] at dt ds dn dp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i tape
      rw [← hTape]
      exact (ht i (H.tape_order tape)).trans (dt i tape)
    · intro ι tape
      rw [← hTape]
      exact (hs ι (H.tape_order tape)).trans (ds ι tape)
    · intro ι tape δ
      rw [← hTape]
      exact (hp ι (H.tape_order tape) δ).trans (dp ι tape δ)
    · intro ι tape δ
      rw [← hTape]
      exact (hh ι (H.tape_order tape) δ).trans (dn ι tape δ)

end

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.genuine_directory
