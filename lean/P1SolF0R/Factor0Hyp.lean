import P1SolF0R.Agreement

open OAI.DepthThreeLowerBound
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open P1Int P1Int.P11 P1Net P1Wit P1Wit.SolWitfill P1Wrap
open P1SolF0R.SolReader P1SolFactor P1SolFactor.Owner
open scoped Classical P1ChkFinal.AstraC10

noncomputable section

set_option maxHeartbeats 400000 in
theorem P1SolF0R.factor0Hyp {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F]
    (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine)
    (a b d bigBias termBias : ℕ) (ρ : (P1Int.toOAI V).K ≃ Fin (Fintype.card (P1Int.toOAI V).K)) :
    P1P5.F0.Factor0Hyp Bt κ hκ V a b d bigBias termBias ρ P1Benes.NetBridge.bset := by
  let M := toOAI V
  let tape (k : M.K) := (ρ k).val
  let ha := four_le_baseDegree S
  obtain ⟨test, htest, htest_eq⟩ := P1SolFactor.factor0EntryPoly M (S.degreeExponent 0) ha
  obtain ⟨cross, hcross, hcross_eq⟩ := P1SolFactor.crossPoly
  obtain ⟨e, hrun⟩ := readFactor0_computes (F := F) M tape test cross htest hcross a b bigBias
  refine ⟨readFactor0 M tape test cross a b bigBias, e, hrun, ?_⟩
  intro x
  dsimp only
  intro H hρ q m hm
  let t := lpTime a b x.length
  let B := Params.B t
  let I := Params.I 1 t
  let h := Params.h t
  let T := Params.T (portConsts Bt) t
  let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) t
  let D := fixedDims Bt V a b x d bigBias termBias
  let g := a * (x.length ^ 2 + 1)
  let u := List.ofFn (encTuple (p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H) m q)
  have hD : D.N = 2 ^ h := rfl
  have hr : D.r = Fintype.card M.K := rfl
  have hchunk := chunks_of_records Bt κ hκ V a x B I (h := h) T hn (D := D) (d := d) H tape hρ q m hm hr
  intro c entries
  exact batchAgreement M tape test cross hcross_eq x u B I D g q.1 ha hr rfl hD hchunk
    (htest_eq B (netLayout V a x) I q.1 P1Benes.NetBridge.bset) c entries

#print axioms P1SolF0R.factor0Hyp
