import P1Int.DirLinkDefs

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolWitfill

namespace P1Int.SolDirLink

private theorem betaOf_congr_tape {K J : Type} {n : ℕ}
    (σ : Fin n → K → Fin 3) (τ : Fin n → J → Fin 3) (k : K) (j : J)
    (h : ∀ i, σ i k = τ i j) (p : ℕ) :
    P1Net.betaOf σ k p = P1Net.betaOf τ j p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [P1ChkDir.betaOf_succ', P1ChkDir.betaOf_succ', ih]
    by_cases hp : p < n
    · simp only [P1ChkDir.sig, dite_eq_left hp, h]
    · simp only [P1ChkDir.sig, dite_eq_right hp]

-- The scan depends on the owner set, including the proof that it is nonempty.
private def ownerScan {n : ℕ}
    (pick : (s : Finset (Fin n)) → s.Nonempty → Fin n)
    (s : Finset (Fin n)) : Option (Fin n) :=
  if hs : s.Nonempty then some (pick s hs) else none

private theorem rootPanel {D : Dims} {R : Type*} [CommSemiring R] {b n a g : ℕ}
    {X : State a g} (E : StateExecution R b n X) (P : ExecutionPanels D E 0)
    (ι : E.Choices) :
    ∃ p : PanelData D 0 X,
      P.atLevel E ι ⟨0, Nat.zero_lt_succ D.top⟩ (Nat.zero_le _) = ⟨a, g, X, p⟩ := by
  cases E with
  | done => exact ⟨P.val, rfl⟩
  | more =>
    refine ⟨P.1.val ι.1, ?_⟩
    simp only [ExecutionPanels.atLevel, Nat.lt_irrefl, dite_false]

private theorem panelOfRoot {D : Dims} {F : Type*} {C : P1Count.CountData F} {d a g : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (X : State a g)
    (fit : PanelFits D (D.lv 0) X) (extra : StepRecords D (D.lv 0))
    (hlevel : R.level t.1 t.2.1 ⟨0, Nat.zero_lt_succ D.top⟩ =
      levelRecordsOfState X fit extra) (y : X.Base) :
    P1ChkDir.PanelFields (ofTuple R t) 0 (X.baseIndex y).val (P1P7.panel X y) := by
  intro k
  have hslot : (fit.baseSlot.symm (y, k)).val =
      (X.baseIndex y).val * (D.lv 0).slots + k.val := rfl
  simp only [ofTuple, levelAt, dite_eq_left (Nat.zero_lt_succ D.top), hlevel,
    LevelRecords.code, ← hslot, finValue_fin, levelRecordsOfState, Equiv.apply_symm_apply,
    P1P7.panel, P1P7.outNbr, P1P7.inNbr, P1P7.outFar, P1P7.inFar, P1P7.addr,
    P1ChkDir.bwNum, true_and]
  intro lane
  rw [← fit.arc_symm_val y lane k, finValue_fin]
  have harc := fit.arc.apply_symm_apply (((y, lane), k) : X.network.Edge)
  simp only [PanelFits.wireWidth, P1P7.outWidths]
  rw [harc]

end P1Int.SolDirLink

namespace P1Int

namespace P11

open SolDirLink

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h) {D : P1Wit.Dims} {d : ℕ}

theorem dirLink_proof (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) :
    DirLinkStmt Bt κ hκ V a x Bk I Tc hn H t := by
  let σ := netSkeleton V I H.interval_count H.initial_lanes H.tape_order t.1
  let τ := dimSkel Bt κ hκ V Bk I Tc hn H t.1
  have htrit (i : Fin (D.I * D.N)) (j : (toOAI V).K) : σ i (H.tape_order j) = τ i j := by
    change t.1 _ (H.tape_order.symm (H.tape_order j)) = t.1 _ j
    rw [Equiv.symm_apply_apply]
  have hbeta (j : (toOAI V).K) (p : ℕ) :
      P1Net.betaOf σ (H.tape_order j) p = P1Net.betaOf τ j p :=
    betaOf_congr_tape σ τ (H.tape_order j) j (fun i => htrit i j) p
  have howns (j : (toOAI V).K) (i : Fin D.I) (Q : ℤ) :
      directoryOwns σ (H.tape_order j) i Q ↔
        P1ChkDir.ownsTab (P1ChkDir.betaTab D.N τ j) D.N i Q = true := by
    rw [P1ChkDir.ownsTab_betaTab]
    simp only [directoryOwns, P1ChkDir.OwnsB, P1ChkDir.bigOf, P1ChkDir.betaT, hbeta]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [ofTuple, atIndex_fin, finValue_fin, p11TupleRecords, netTupleRecords, σ, τ] using
      congrArg Fin.val (htrit i j)
  · intro i j
    let p := ord D.I D.r (i, H.tape_order j)
    have hp : p.val = i.val * D.r + (H.tape_order j).val := rfl
    simp only [ofTuple]
    rw [← hp]
    simp only [atIndex_fin, p, p11TupleRecords, netTupleRecords, directoryOfSkeleton,
      Equiv.symm_apply_apply, P1ChkDir.betaT]
    exact congrArg zigzag (hbeta j (i.val * D.N))
  · intro i j δ
    let p := ord (D.I * D.r) 3 (ord D.I D.r (i, H.tape_order j), δ)
    have hp : p.val = (i.val * D.r + (H.tape_order j).val) * 3 + δ.val := rfl
    simp only [ofTuple]
    rw [← hp]
    simp only [atIndex_fin, p, p11TupleRecords, netTupleRecords, directoryOfSkeleton,
      Equiv.symm_apply_apply, P1ChkDir.nextT, P1ChkDir.nextScan, P1ChkDir.portQT,
      P1ChkDir.bigOf, P1ChkDir.betaT]
    change ownerCode (ownerScan Finset.min' _) = ownerCode (ownerScan Finset.min' _)
    apply congrArg (fun s => ownerCode (ownerScan Finset.min' s))
    apply Finset.filter_congr
    intro u _
    rw [hbeta, howns]
  · intro i j δ
    let p := ord (D.I * D.r) 3 (ord D.I D.r (i, H.tape_order j), δ)
    have hp : p.val = (i.val * D.r + (H.tape_order j).val) * 3 + δ.val := rfl
    simp only [ofTuple]
    rw [← hp]
    simp only [atIndex_fin, p, p11TupleRecords, netTupleRecords, directoryOfSkeleton,
      Equiv.symm_apply_apply, P1ChkDir.prevT, P1ChkDir.prevScan, P1ChkDir.portQT,
      P1ChkDir.bigOf, P1ChkDir.betaT]
    change ownerCode (ownerScan Finset.max' _) = ownerCode (ownerScan Finset.max' _)
    apply congrArg (fun s => ownerCode (ownerScan Finset.max' s))
    apply Finset.filter_congr
    intro u _
    rw [hbeta, howns]
  · intro q
    simp only [ofTuple, atIndex_fin, p11TupleRecords, netTupleRecords, directoryOfSkeleton,
      P1ChkDir.gOwnT, P1ChkDir.guessP6, P1ChkDir.leastScan]
    change ownerCode (ownerScan Finset.min' _) = ownerCode (ownerScan Finset.min' _)
    apply congrArg (fun s => ownerCode (ownerScan Finset.min' s))
    apply Finset.filter_congr
    intro u _
    exact howns (toOAI V).inputTape u (q.val : ℤ)

theorem panelLink_proof (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) :
    PanelLinkStmt Bt κ hκ V a x Bk I Tc hn H t := by
  let X := P1Net.rnState (toOAI V) Bk I t.1 (four_le_baseDegree S)
  let E := netExecution Bt κ hκ V Bk I Tc hn t.1
  let ℓ : Fin (D.top + 1) := ⟨0, Nat.zero_lt_succ D.top⟩
  obtain ⟨p, hp⟩ := rootPanel E (H.panels t.1) t.2.1
  have hb : Fintype.card X.Base = 2 * (I * P1Net.locCount (toOAI V).K h) :=
    P1Net.card_stateNet_base I t.1 (four_le_baseDegree S)
      (P1Net.strWidth (toOAI V) Bk) (P1Net.strWidth (toOAI V) Bk) (P1Net.tupWidth (toOAI V) Bk)
  refine ⟨(p.fits.bases.trans hb).ge, p.fits.slots.ge, p.fits.lanes.ge, ?_⟩
  intro y
  have hy : (X.baseIndex y).val = P1ChkDir.addrL y := by
    rcases y with ⟨⟨i, l⟩, b⟩
    exact P1Net.stateNet_baseIndex_val I t.1 (four_le_baseDegree S)
      (P1Net.strWidth (toOAI V) Bk) (P1Net.strWidth (toOAI V) Bk) (P1Net.tupWidth (toOAI V) Bk) i l b
  have hlevel : (p11TupleRecords Bt κ hκ V a x Bk I Tc hn H).level t.1 t.2.1 ℓ =
      levelRecordsOfState X p.fits (p.step ((H.terms t.1).table E t.2.1 ℓ)) := by
    -- Read the state and its dependent panel data together.
    let readPanel (q : IndexedPanel D 0) : LevelRecords D (D.lv 0) :=
      levelRecordsOfState q.state q.data.fits (q.data.step ((H.terms t.1).table E t.2.1 ℓ))
    exact congrArg readPanel hp
  rw [← hy]
  exact panelOfRoot _ _ X p.fits _ hlevel y

end P11

end P1Int

#print axioms P1Int.P11.dirLink_proof
#print axioms P1Int.P11.panelLink_proof
