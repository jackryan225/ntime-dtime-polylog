import P1Int.D5AsmDefs

noncomputable section

open P1Int P1Int.P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.d5Steps_asm {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool) (d bigBias termBias : ℕ)
    [NeZero (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).I]
    [NeZero ((P1Int.P11.fixedDims Bt V a b x d bigBias termBias).I * (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).N)]
    [NeZero (P1Wrap.Params.B (P1Int.lpTime a b x.length))]
    (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.D5StepsAsmTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hd bs l Wof ni cnt ck τ hτ
    hck0 hck1 hck2 hck3 hck14 hck10 hck11 hck12 hck13
    hc0 hc1 hc2 hc3 hc14 hc10 hc11 hc12 hc13 hfit hP hn hN
    hout hgreedy hc10Step hbridge hsound hclose henc hW hfinP
  let D := fixedDims Bt V a b x d bigBias termBias
  let dims := gdims Bt V a b d bigBias termBias
  let dims4 := c4dims Bt V a b d bigBias termBias
  let X := fixedIndex Bt V a b x d bigBias termBias cnt
  let G := fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof
  have countFits {c n : ℕ} (hc : cnt c = n) (hrange : c ≤ 3 ∨ (10 ≤ c ∧ c ≤ 14)) :
      n ≤ ni := hc.symm.le.trans (hfit c hrange)
  change D5Steps (fixedEnc Bt κ hκ V a b x d bigBias termBias H)
    ((fixedCD Bt κ hκ V a b x).Valid bs l) ck ni X G
  refine ⟨hout, ?_, ?_, ?_, hgreedy, hc10Step, ?_, ?_, ?_, ?_⟩
  · intro u
    exact d5_dir_step D H.tape_order ni cnt hc0 hc1 hc2
      (countFits hc0 (by decide)) (countFits hc1 (by decide)) (countFits hc2 (by decide))
      List.ofFn ck hck0 hck1 hck2 u
  · intro u hDir
    exact P1ChkDir.d5_c14_step (M := toOAI V) (B := P1Wrap.Params.B (lpTime a b x.length))
      (g := a * (x.length ^ 2 + 1)) x D hP hn H.tape_order ni (cnt 14) hc14
      (countFits hc14 (by decide)) List.ofFn (ck 14) hck14 u hDir
  · intro u hDir _
    -- The bridge converts the wired stage's panel predicate to agreement with a tuple.
    have hStage : (∀ i < ni, i < cnt 3 → ck 3 u i = true) ↔
        c4Rhs Bt V a b x d bigBias termBias τ u :=
      P1ChkDir.d5_c4w_step (four_le_baseDegree S) τ dims4 x H.tape_order hτ hN ni (cnt 3) hc3
        (countFits hc3 (by decide)) List.ofFn (ck 3) hck3 u hDir
    exact hStage.trans (hbridge hd τ hτ u hDir)
  · intro u _
    exact P1ChkFinal.d5_c11_step dims x ni (cnt 10) hc10 (countFits hc10 (by decide))
      List.ofFn (ck 10) hck10 u
  · intro u hPrev
    have h11 : G.c11 u := Eq.mp (G.P_c11 X.top u)
      (hPrev (4 + 2 * X.top) (Nat.add_lt_add_right (Nat.lt_succ_self 4) (2 * X.top)))
    exact P1ChkFinal.d5_c12_step dims x ni (cnt 11) hc11 (countFits hc11 (by decide))
      List.ofFn (ck 11) hck11 u h11
  · intro u _
    exact P1ChkFinal.d5_c13_step bs l dims Wof x ni cnt hc12 hc13
      (countFits hc12 (by decide)) (countFits hc13 (by decide)) List.ofFn ck hck12 hck13 u
  · exact form_of_cut Bt κ hκ V a b x bigBias termBias bs l H X G
      (hsound henc bs l Wof hW hfinP cnt)
      (formFix_asm Bt κ hκ V a b x d bigBias termBias H
        (c14_fix Bt κ hκ V a b x d bigBias termBias H) bs l Wof cnt)
      (hclose henc (c14_close Bt κ hκ V a b x d bigBias termBias H) bs l Wof hW hfinP cnt)

#print axioms P1Int.P11.d5Steps_asm
