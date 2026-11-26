import P1Wit.WitCountInput
import P1ChkDir.Genuine

/-!
# P1Int.DirLinkDefs: the statement `DirLinkStmt` (witfill's directory = the TRUE directory of the check lanes)

Owner: P1-lean-integ (Opus restart, 2026-11-25). TARGET for a Sol prover (G3-chief order 12:05Z).

The witness of a typed tuple `t` is `P1Wit.ofTuple R t` with `R = P1Wit.p11TupleRecords .. H` (Sol witfill). Its
directory section is built by `P1Wit.SolWitfill.directoryOfSkeleton` from the skeleton `t.1`, renumbered by the
record package `H` (`H.interval_count`, `H.initial_lanes`, `H.tape_order`). The check lanes prove `Ck_true` for the
directory families (C1, C2, C3: `P1ChkDir.dirF_enc`; C14: `P1ChkDir.C14F_enc`, file ChkDir/P1ChkDir/Genuine.lean)
under FIVE hypotheses on the fields: `htrit`, `hstart`, `hnext`, `hprev`, `hguess`. `dirLink` states that witfill's
fields satisfy exactly these five hypotheses for the skeleton `dimSkel H t.1` and the tape order `H.tape_order`.

Both sides use `P1Net.betaOf` for the start blocks and the owner rule `⌊β / N⌋ - 1 ≤ Q ≤ ⌊β / N⌋ + 1`; witfill's
previous / next / least owners are `Finset.max'` / `Finset.min'` of the same filters as `P1ChkDir.prevScan`,
`nextScan`, `leastScan` (with `P1ChkDir.ownsTab_betaTab`); its field order is `P1Wit.ord` (`i * D.r + k`, then
`* 3 + δ`), which `ofTuple` reads back by `atIndex`.
-/

namespace P1Int

namespace P11

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression

noncomputable section

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (Tc : ℕ) (hn : Tc * S.laneBits ≤ h) {D : P1Wit.Dims} {d : ℕ}

/-- The skeleton of the run in the numbering of the dimensions `D`: small interval `i < D.I * D.N` (renumbered by
`H.interval_count`, `H.initial_lanes`), tape `k` of the machine. -/
def dimSkel (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (σ : P1Wit.SolWitfill.RoutedSkeleton V I h) : Fin (D.I * D.N) → (toOAI V).K → Fin 3 :=
  fun i kk => σ (finCongr (by rw [H.interval_count, H.initial_lanes]) i) kk

/-- **The statement of the target** (as a `Prop`, so that a prover cannot change it): the directory fields of
witfill's witness hold the true values of the check lanes, in the form of the five hypotheses of
`P1ChkDir.dirF_enc` and `P1ChkDir.C14F_enc`. -/
def DirLinkStmt (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) : Prop :=
    (∀ (i : Fin (D.I * D.N)) (kk : (toOAI V).K),
      (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).trit i (H.tape_order kk) =
        (dimSkel Bt κ hκ V Bk I Tc hn H t.1 i kk : ℕ)) ∧
    (∀ (ι : Fin D.I) (kk : (toOAI V).K),
      (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).start ι (H.tape_order kk) =
        P1Wit.zigzag (P1ChkDir.betaT D.N (dimSkel Bt κ hκ V Bk I Tc hn H t.1) ι kk)) ∧
    (∀ (ι : Fin D.I) (kk : (toOAI V).K) (δ : Fin 3),
      (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).nextOwn ι (H.tape_order kk) δ =
        P1ChkDir.ownToN (P1ChkDir.nextT D.N (dimSkel Bt κ hκ V Bk I Tc hn H t.1) ι kk δ)) ∧
    (∀ (ι : Fin D.I) (kk : (toOAI V).K) (δ : Fin 3),
      (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).prevOwn ι (H.tape_order kk) δ =
        P1ChkDir.ownToN (P1ChkDir.prevT D.N (dimSkel Bt κ hκ V Bk I Tc hn H t.1) ι kk δ)) ∧
    (∀ q : Fin D.nGB,
      (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t).guess q =
        P1ChkDir.ownToN (P1ChkDir.gOwnT (I := D.I)
          (P1ChkDir.guessP6 D (toOAI V).inputTape fun q => ((q : ℕ) : ℤ)) D.N
          (dimSkel Bt κ hκ V Bk I Tc hn H t.1) q))


/-- **The statement of the second target** (level 0 for check C4): level 0 of `D` has room for all bases, slots
and lanes of the routed network, and the level-0 panel fields of witfill's witness at the base address
`P1ChkDir.addrL y` are the numbers of the true panel `P1P7.panel (rnState ..) y` (hypotheses `hbases`, `hslots`,
`hlanes`, `hpanel` of `P1ChkDir.C4F_enc`, with `Wc = Ws = strWidth`, `Wt = tupWidth`, i.e. `rnState`). -/
def PanelLinkStmt (H : P1Wit.SolWitfill.NetRecordInputs Bt κ hκ V Bk I Tc hn D d)
    (t : (netData Bt κ hκ V a x Bk I Tc hn (P1Wit.netSiteOrder Bt κ hκ V Bk I Tc hn)).toCountData.Tup d) : Prop :=
  2 * (I * P1Net.locCount (toOAI V).K h) ≤ (D.lv 0).bases ∧
  2 ^ S.degreeExponent 0 ≤ (D.lv 0).slots ∧
  2 ^ h ≤ (D.lv 0).lanes ∧
  ∀ y : (Fin I × P1Net.Loc (toOAI V).K h) × Bool,
    P1ChkDir.PanelFields (P1Wit.ofTuple (P1Wit.p11TupleRecords Bt κ hκ V a x Bk I Tc hn H) t) 0
      (P1ChkDir.addrL y) (P1P7.panel (P1Net.rnState (toOAI V) Bk I t.1 (four_le_baseDegree S)) y)

end

end P11

end P1Int
