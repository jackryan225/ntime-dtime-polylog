import P1Int.FormSoundDefs
import P1Int.FormDir
import P1Int.FormC14
import P1Int.FormLev
import P1Int.FormC11

noncomputable section

namespace P1Int.P11.SolFormSound

open P1Wit P1Wit.SolWitfill P1ChkFinal
open private pre_wsOf_eq from P1Int.FormC11

private theorem payload_sound {F : Type*} {D : Dims} {C : P1Count.CountData F} {d m : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (hfit : D.fixedLen + (tuplePayload R t).length ≤ m) :
    let w := List.ofFn (encTuple R m t)
    pre (wsOf D w) (finN D) ≤ (rdPayload D w).length ∧
      ∀ c ∈ (rdPayload D w).drop (pre (wsOf D w) (finN D)), c = false := by
  let f := ofTuple R t
  let z := tuplePayload R t
  let w := enc D m f z
  have htotal : pre (wsOf D w) (finN D) = z.length := by
    rw [pre_wsOf_eq, tuplePayload_length]
    have harcs : finN D * finArcs D = FinalArcs D := by
      simp only [finN, finArcs, Nat.mul_assoc]
    rw [harcs, widthPrefix, widthPrefix]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < (D.lv D.top).count .width := Finset.mem_range.mp hi
    have hcount : i < D.count (secLev D.top .width) := by
      rw [D.count_secLev .width le_rfl]
      exact hi'
    have hread := decode_enc D m f z (ofTuple_inRange R t) (D.secLev_lt_nSec .width le_rfl) hcount
    change readField D w (secLev D.top .width) i = _ at hread
    rw [hread]
    simp only [f, Fields.val, D.kind_secLev .width le_rfl, ofTuple_levVal R t _ _ _ hi',
      levelAt, dite_eq_left (Nat.lt_succ_self D.top), LevelRecords.code, finalLevel, Fin.last]
  change pre (wsOf D (List.ofFn (encFn D m f z))) (finN D) ≤
      (rdPayload D (List.ofFn (encFn D m f z))).length ∧
    ∀ c ∈ (rdPayload D (List.ofFn (encFn D m f z))).drop
      (pre (wsOf D (List.ofFn (encFn D m f z))) (finN D)), c = false
  rw [ofFn_encFn D m f z hfit, htotal, drop_fixedLen_enc]
  constructor
  · rw [List.length_append]
    exact Nat.le_add_right _ _
  · rw [List.drop_left' rfl]
    exact fun c hc => List.eq_of_mem_replicate hc

private theorem chainOK_cast {F : Type*} [CommRing F] [Algebra (ZMod 2) F] {d p q : ℕ}
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (hpq : p = q)
    (w : Fin q → F) (j : Fin (q + 1) → Fin d) (h : P1Count.ChainOK bs l w j) :
    P1Count.ChainOK bs l (fun i => w (Fin.cast hpq i))
      (fun i => j (Fin.cast (congrArg (· + 1) hpq) i)) := by
  cases hpq
  exact h

private theorem chain_sound {F : Type*} [CommRing F] [Algebra (ZMod 2) F]
    {D : Dims} {C : P1Count.CountData F} {d m : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (hfit : D.fixedLen + (tuplePayload R t).length ≤ m)
    (bs : Module.Basis (Fin d) (ZMod 2) F) (l : F →ₗ[ZMod 2] ZMod 2) (W : ℕ → F)
    (hW : ∀ (i : Fin (C.P t.1 t.2.1)), W i = C.W t.1 t.2.1 t.2.2.1 i)
    (hp : finP D = C.P t.1 t.2.1) (hchain : P1Count.ChainOK bs l (C.W t.1 t.2.1 t.2.2.1) t.2.2.2) :
    ∃ j : Fin (finP D + 1) → Fin d,
      (∀ v : Fin (finP D + 1), (j v : ℕ) = rdChain D (List.ofFn (encTuple R m t)) v) ∧
      P1Count.ChainOK bs l (fun i : Fin (finP D) => W i) j := by
  let f := ofTuple R t
  let z := tuplePayload R t
  let j : Fin (finP D + 1) → Fin d := fun v => t.2.2.2 (Fin.cast (congrArg (· + 1) hp) v)
  refine ⟨j, ?_, ?_⟩
  · intro v
    let v' : Fin (C.P t.1 t.2.1 + 1) := Fin.cast (congrArg (· + 1) hp) v
    have hv : (v : ℕ) < D.chainLen := v'.isLt.trans_le (R.chain_fits_len t.1 t.2.1)
    change (t.2.2.2 v' : ℕ) = rdChain D (List.ofFn (encFn D m f z)) v
    rw [ofFn_encFn D m f z hfit, rdChain_enc D m f z (ofTuple_inRange R t) hv]
    exact (finValue_fin t.2.2.2 v').symm
  · have hw : (fun i : Fin (finP D) => W i) = fun i => C.W t.1 t.2.1 t.2.2.1 (Fin.cast hp i) := by
      funext i
      exact hW (Fin.cast hp i)
    rw [hw]
    exact chainOK_cast bs l hp _ _ hchain

private theorem stages_sound {U : Type*} (G : D5Groups U) (top : ℕ) (u : U)
    (hdir : G.dir u) (h14 : G.c14 u) (h4 : G.c4 u)
    (hlevels : ∀ lv < top, G.greedy lv u ∧ G.c10 lv u)
    (h11 : G.c11 u) (h12 : G.c12 u) (h13 : G.c13 u) :
    ∀ j < 7 + 2 * top, G.P top j u := by
  intro j hj
  by_cases h0 : j = 0
  · rw [h0, G.P_zero]
    exact True.intro
  by_cases h1 : j = 1
  · rw [h1, G.P_one]
    exact hdir
  by_cases h2 : j = 2
  · rw [h2, G.P_two]
    exact h14
  by_cases h3 : j = 3
  · rw [h3, G.P_three]
    exact h4
  by_cases hlevel : j < 4 + 2 * top
  · by_cases heven : j % 2 = 0
    · have hl : (j - 4) / 2 < top := by omega
      have heq : j = 4 + 2 * ((j - 4) / 2) := by omega
      exact Eq.mpr (congrArg (fun n => G.P top n u) heq)
        (Eq.mpr (G.P_greedy hl u) (hlevels _ hl).1)
    · have hl : (j - 5) / 2 < top := by omega
      have heq : j = 5 + 2 * ((j - 5) / 2) := by omega
      exact Eq.mpr (congrArg (fun n => G.P top n u) heq)
        (Eq.mpr (G.P_c10 hl u) (hlevels _ hl).2)
  by_cases h11j : j = 4 + 2 * top
  · rw [h11j, G.P_c11]
    exact h11
  by_cases h12j : j = 5 + 2 * top
  · rw [h12j, G.P_c12]
    exact h12
  have h13j : j = 6 + 2 * top := by omega
  rw [h13j, G.P_c13]
  exact h13

end P1Int.P11.SolFormSound

open P1Int.P11 P1Int.P11.SolFormSound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.formSound_asm {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.FormSoundAsmTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hfit bs l Wof hW hp cnt t ht j hj
  let D := fixedDims Bt V a b x d bigBias termBias
  let R := fixedTR Bt κ hκ V a b x d bigBias termBias H
  let u := fixedEnc Bt κ hκ V a b x d bigBias termBias H t
  have hsec := secEq_enc Bt κ hκ V a b x d bigBias termBias H hfit t
  have h4 : c4G Bt κ hκ V a b x d bigBias termBias H u := by
    have htrit : P1Wit.secTrit < D.nSec := by
      change 0 < 7 + 12 * (D.top + 1)
      omega
    exact ⟨t, hsec _ htrit, fun kk _ => hsec _ (D.secLev_lt_nSec kk (Nat.zero_le D.top))⟩
  have h12 : c12G Bt V a b x d bigBias termBias u := payload_sound R t (hfit t)
  have h13 : c13G Bt V a b x d bigBias termBias bs l Wof u :=
    chain_sound R t (hfit t) bs l (Wof x (List.ofFn u)) (hW t) (hp t.1 t.2.1) ht.2
  exact stages_sound (fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof) D.top u
    (dir_sound Bt κ hκ V a b x d bigBias termBias H hfit t)
    (c14_sound Bt κ hκ V a b x d bigBias termBias H hfit t ht.1)
    h4 (levels_sound Bt κ hκ V a b x d bigBias termBias H hfit t)
    (c11_sound Bt κ hκ V a b x d bigBias termBias H hfit t) h12 h13 j hj

example : ∀ {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias),
    P1Int.P11.FormSoundAsmTarget Bt κ hκ V a b x d bigBias termBias H := @P1Int.P11.formSound_asm

#print axioms P1Int.P11.formSound_asm
