import P1ChkFinal.ProgC13link
import P1Int.WitfillLink
import P1P5.EvalOrder
import P1P5.ConeBudget
import P1P7.KernelPos
import P1SolCone.HalfWords
import P1SolCone.CheckedTables
import P1SolCone.ShrinkPad
import P1SolCone.Factor0
import OAI.Computability.VPVNP.BitSlotXor

namespace P1SolCone

open OAI.Computability.VPVNP.Compression
open P1Int P1Int.P11

namespace SolCone

/-- Read the word of the outgoing arc at `(y, l, k)` using the final base prefix and width fields.
Return `none` if the arc address or the interval of bits lies outside its storage. -/
def readArc (D : P1Wit.Dims) (u : List Bool) (y l k : ℕ) : Option (List Bool) :=
  let L := D.lv D.top
  if y < L.bases ∧ l < L.lanes ∧ k < L.slots then
    let j := l * L.slots + k
    let start := D.fixedLen + P1Wit.rdOmega D u y +
      P1ChkFinal.pre (P1ChkFinal.arcW D u y) j
    let width := P1Wit.rdWidth D u D.top y l k
    if start + width ≤ u.length then some ((u.drop start).take width) else none
  else none

/-- The outgoing and incoming words at D9 site `v`, each in slot order. An incoming word
is stored at its source, whose lane is the target lane translated by the stored displacement. -/
def readFinalHalf (D : P1Wit.Dims) (u : List Bool) (v : ℕ) :
    Option (List (List Bool) × List (List Bool)) :=
  let L := D.lv D.top
  if v < L.bases * L.lanes then do
    let y := v / L.lanes
    let l := v % L.lanes
    let slots := List.range L.slots
    let outgoing ← slots.mapM (readArc D u y l)
    let incoming ← slots.mapM fun k =>
      let displacement := P1Wit.rdInDisp D u D.top y k
      if displacement < L.lanes then
        readArc D u (P1Wit.rdInAddr D u D.top y k) (l ^^^ displacement)
          (P1Wit.rdInFar D u D.top y k)
      else none
    pure (outgoing, incoming)
  else none

section ArcCorrect

open P1Wit P1Wit.SolWitfill

private theorem flatten_read_padded {n : ℕ} {w : Fin n → ℕ}
    (z : (i : Fin n) → Fin (w i) → Bool) (padding : List Bool) (i : Fin n) :
    widthPrefix (atIndex w) i.val + w i ≤ (flatten z ++ padding).length ∧
    (((flatten z ++ padding).drop (widthPrefix (atIndex w) i.val)).take (w i)) =
      List.ofFn (z i) := by
  obtain ⟨rest, hr⟩ := cat_split (arcBits z) i.isLt
  have hprefix : (cat (arcBits z) i.val).length = widthPrefix (atIndex w) i.val := by
    simp only [cat_length_eq_prefix, arcBits_length]
  rw [flatten, hr, ← hprefix, arcBits_fin, List.append_assoc, List.append_assoc]
  constructor
  · simp only [List.length_append, List.length_ofFn]
    omega
  · rw [List.drop_left, List.take_left' List.length_ofFn]

/-- The final source-arc reader returns the word stored at the corresponding position
of the actual P6 tuple encoding. This includes zero-width arcs and padding. -/
theorem readArc_encTuple {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R t).length ≤ m)
    (y : Fin (D.lv D.top).bases) (l : Fin (D.lv D.top).lanes) (k : Fin (D.lv D.top).slots) :
    let i : Fin (FinalArcs D) := ⟨(y.val * (D.lv D.top).lanes + l.val) * (D.lv D.top).slots + k.val,
      idx_lt (idx_lt y.isLt l.isLt) k.isLt⟩
    readArc D (List.ofFn (encTuple R m t)) y l k =
      some (List.ofFn (R.payload t.1 t.2.1 t.2.2.1 i)) := by
  let L := D.lv D.top
  let w : Fin (FinalArcs D) → Fin (2 ^ D.wW) := (R.level t.1 t.2.1 (finalLevel D)).width
  let z := R.payload t.1 t.2.1 t.2.2.1
  let fields := ofTuple R t
  let u := enc D m fields (flatten z)
  let i : Fin (FinalArcs D) := ⟨(y.val * L.lanes + l.val) * L.slots + k.val,
    idx_lt (idx_lt y.isLt l.isLt) k.isLt⟩
  let start := y.val * (L.lanes * L.slots)
  let j := l.val * L.slots + k.val
  have hi : i.val = start + j := by dsimp only [i, start, j]; ring
  have hbuf : List.ofFn (encTuple R m t) = u := ofFn_encFn _ _ _ _ hm
  have hf := ofTuple_inRange R t
  have hw {l' k' : ℕ} (hl' : l' < L.lanes) (hk' : k' < L.slots) :
      rdWidth D u D.top y l' k' =
        finValue w ((y.val * L.lanes + l') * L.slots + k') := by
    rw [rdWidth_enc D m fields (flatten z) hf le_rfl y.isLt hl' hk']
    exact dite_eq_left (Nat.lt_succ_self D.top)
  have hω : rdOmega D u y = widthPrefix (finValue w) start := by
    rw [rdOmega_enc D m fields (flatten z) hf y.isLt]
    exact atIndex_fin (fun y' : Fin L.bases => widthPrefix (finValue w)
      (y'.val * (L.lanes * L.slots))) y
  have hloc : P1ChkFinal.pre (P1ChkFinal.arcW D u y) j =
      ∑ s ∈ Finset.range j, finValue w (start + s) := by
    apply Finset.sum_congr rfl
    intro s hs
    have hsn : s < L.lanes * L.slots :=
      (Finset.mem_range.mp hs).trans (idx_lt l.isLt k.isLt)
    have hdiv : s / L.slots < L.lanes :=
      (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt k.isLt)).mpr hsn
    have hmod : s % L.slots < L.slots := Nat.mod_lt _ (Nat.zero_lt_of_lt k.isLt)
    rw [P1ChkFinal.arcW, hw hdiv hmod]
    congr 1
    calc
      _ = start + (s / L.slots * L.slots + s % L.slots) := by dsimp only [start]; ring
      _ = _ := by rw [div_mul_add_mod]
  have hsum : rdOmega D u y + P1ChkFinal.pre (P1ChkFinal.arcW D u y) j =
      widthPrefix (finValue w) i.val := by
    rw [hω, hloc, hi]
    exact (Finset.sum_range_add (finValue w) start j).symm
  have htail := drop_fixedLen_enc D m fields (flatten z)
  have hread := flatten_read_padded z (List.replicate (m - (D.fixedLen + (flatten z).length)) false) i
  rw [← htail] at hread
  change readArc D (List.ofFn (encTuple R m t)) y l k = some (List.ofFn (z i))
  rw [hbuf]
  unfold readArc
  dsimp only
  rw [ite_eq_left ⟨y.isLt, l.isLt, k.isLt⟩]
  change (if D.fixedLen + rdOmega D u y + P1ChkFinal.pre (P1ChkFinal.arcW D u y) j +
      rdWidth D u D.top y l k ≤ u.length then
        some ((u.drop (D.fixedLen + rdOmega D u y + P1ChkFinal.pre
          (P1ChkFinal.arcW D u y) j)).take (rdWidth D u D.top y l k))
      else none) = some (List.ofFn (z i))
  rw [Nat.add_assoc D.fixedLen, hsum, hw l.isLt k.isLt]
  change (if D.fixedLen + widthPrefix (finValue w) i.val + finValue w i.val ≤ u.length then
      some ((u.drop (D.fixedLen + widthPrefix (finValue w) i.val)).take (finValue w i.val))
      else none) = some (List.ofFn (z i))
  rw [finValue_fin w i]
  have hfit : D.fixedLen ≤ u.length := by
    have hlen := enc_length D m fields (flatten z) hm
    change u.length = m at hlen
    rw [hlen]
    omega
  have hlen := hread.1
  simp only [rdPayload, List.length_drop] at hlen
  change widthPrefix (finValue w) i.val + (w i).val ≤ u.length - D.fixedLen at hlen
  have hsafe : D.fixedLen + widthPrefix (finValue w) i.val + (w i).val ≤ u.length := by omega
  rw [ite_eq_left hsafe, ← List.drop_drop]
  exact congrArg some hread.2

/-- The three source coordinates stored at an incoming base slot. -/
theorem readIncoming_encTuple {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R t).length ≤ m)
    (y : Fin (D.lv D.top).bases) (k : Fin (D.lv D.top).slots) :
    let u := List.ofFn (encTuple R m t)
    let L := R.level t.1 t.2.1 (finalLevel D)
    let i := ord (D.lv D.top).bases (D.lv D.top).slots (y, k)
    (rdInAddr D u D.top y k, rdInDisp D u D.top y k, rdInFar D u D.top y k) =
      ((L.inAddr i).val, (L.inDisp i).val, (L.inFar i).val) := by
  dsimp only
  change (rdInAddr D (List.ofFn (encFn D m (ofTuple R t) (tuplePayload R t))) D.top y k,
      rdInDisp D (List.ofFn (encFn D m (ofTuple R t) (tuplePayload R t))) D.top y k,
      rdInFar D (List.ofFn (encFn D m (ofTuple R t) (tuplePayload R t))) D.top y k) = _
  rw [ofFn_encFn _ _ _ _ hm,
    rdInAddr_enc D m _ _ (ofTuple_inRange R t) le_rfl y.isLt k.isLt,
    rdInDisp_enc D m _ _ (ofTuple_inRange R t) le_rfl y.isLt k.isLt,
    rdInFar_enc D m _ _ (ofTuple_inRange R t) le_rfl y.isLt k.isLt]
  let i := ord (D.lv D.top).bases (D.lv D.top).slots (y, k)
  let L := R.level t.1 t.2.1 (finalLevel D)
  have htop : D.top < D.top + 1 := Nat.lt_succ_self _
  simp only [ofTuple, levelAt, dite_eq_left htop, LevelRecords.code]
  exact Prod.ext (finValue_fin L.inAddr i)
    (Prod.ext (finValue_fin L.inDisp i) (finValue_fin L.inFar i))

/-- Each trit is read with a range check at the requested tape and small interval. -/
def readTrit? (D : Dims) (u : List Bool) (i tape : ℕ) : Option (Fin 3) :=
  if i < D.I * D.N ∧ tape < D.r then
    if h : rdTrit D u i tape < 3 then some ⟨rdTrit D u i tape, h⟩ else none
  else none

theorem readTrit_encTuple {F : Type*} {D : Dims} {C : P1Count.CountData F} {d : ℕ}
    (R : TupleRecords D C d) (t : C.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload R t).length ≤ m)
    (i : Fin (D.I * D.N)) (tape : Fin D.r) :
    readTrit? D (List.ofFn (encTuple R m t)) i tape = some (R.skeleton t.1 i tape) := by
  unfold readTrit?
  rw [ite_eq_left ⟨i.isLt, tape.isLt⟩]
  have h : rdTrit D (List.ofFn (encTuple R m t)) i tape = (R.skeleton t.1 i tape).val := by
    change rdTrit D (List.ofFn (encFn D m (ofTuple R t) (tuplePayload R t))) i tape = _
    rw [ofFn_encFn _ _ _ _ hm, rdTrit_enc D m _ _ (ofTuple_inRange R t) i.isLt tape.isLt]
    change atIndex (fun j => finValue (R.skeleton t.1 j) tape.val) i.val = _
    rw [atIndex_fin _ i, finValue_fin _ tape]
  split
  · exact congrArg some (Fin.ext h)
  · rename_i hbad
    exact False.elim (hbad (h ▸ (R.skeleton t.1 i tape).isLt))

end ArcCorrect

section ExecutionPayload

open P1Wit P1Wit.SolWitfill

private theorem castPayload_word {A : Type*} {D : Dims}
    {p q : LevelRecords D (D.lv D.top)} (h : p = q)
    (payload : A ≃ ((i : Fin (FinalArcs D)) → Fin (p.width i).val → Bool))
    (z : A) (i : Fin (FinalArcs D)) :
    List.ofFn ((Eq.mpr (congrArg
      (fun r : LevelRecords D (D.lv D.top) => A ≃ ((j : Fin (FinalArcs D)) → Fin (r.width j).val → Bool))
      h.symm) payload) z i) =
      List.ofFn (payload z i) := by
  cases h
  rfl

theorem executionPayload_word {F : Type*} [CommSemiring F] {D : Dims} {a g b n : ℕ}
    {X : State a g} (E : StateExecution F b n X)
    (P : ExecutionPanels D E 0) (T : ExecutionTerms D E 0) (ι : E.Choices)
    (z : (e : (E.finalState ι).network.Edge) → (E.finalState ι).network.Payload e)
    (i : Fin (FinalArcs D)) :
    List.ofFn (payloadOfExecution E P T ι z i) = List.ofFn (z ((P.final E ι).fits.arc i)) := by
  let Q := (P.final E ι).step (T.table E ι (finalLevel D))
  unfold payloadOfExecution
  exact castPayload_word (levelOfExecution_final E P T ι).symm
    (payloadOfState (E.finalState ι) (P.final E ι).fits Q) z i

end ExecutionPayload

section FinalHalf

open OAI.Computability.VPVNP OAI.Computability.VPVNP.NetworkKernel
open P1Wit P1Wit.SolWitfill

private theorem mapM_range_ofFn {A : Type*} {n : ℕ} (f : ℕ → Option A) (g : Fin n → A)
    (h : ∀ i : Fin n, f i = some (g i)) :
    (List.range n).mapM f = some (List.ofFn g) := by
  rw [← List.map_coe_finRange_eq_range, List.mapM_map, List.ofFn_eq_map]
  suffices ∀ l : List (Fin n), l.mapM (fun i => f i.val) = some (l.map g) by
    exact this _
  intro l
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.mapM_cons, h i, ih]
    rfl

private theorem bitWord_sub_val {g : ℕ} (u d : BitWord g) :
    (bitWordFinEquiv g (u - d)).val = (bitWordFinEquiv g u).val ^^^ (bitWordFinEquiv g d).val := by
  have h : -d = d := funext fun i => ZMod.neg_eq_self_mod_two (d i)
  rw [sub_eq_add_neg, h, bitWordFinEquiv_add_val]

theorem readFinalHalf_of_stateReads {D : Dims} {a g : ℕ} (X : State a g)
    (fit : PanelFits D (D.lv D.top) X) (u : List Bool)
    (z : (e : X.network.Edge) → X.network.Payload e)
    (hArc : ∀ e : X.network.Edge,
      readArc D u (X.baseIndex e.1.1).val (bitWordFinEquiv g e.1.2).val e.2.val = some (List.ofFn (z e)))
    (hIncoming : ∀ (y : X.Base) (k : Fin (2 ^ a)),
      let addr := (X.baseIndex y).val
      let src := X.slots.base.target.symm (y, k)
      (rdInAddr D u D.top addr k, rdInDisp D u D.top addr k, rdInFar D u D.top addr k) =
        ((X.baseIndex src.1).val, (bitWordFinEquiv g (X.slots.displacement src)).val, src.2.val))
    (v : Fin (Fintype.card X.network.Site)) :
    let s := (stateOrd X).symm v
    readFinalHalf D u v.val =
      some (halfWords X s (WireTensor.edgeAssignment X.network.src X.network.dst z s)) := by
  let s := (stateOrd X).symm v
  let y := (X.baseIndex s.1).val
  let l := (bitWordFinEquiv g s.2).val
  have hs := stateOrd_symm_apply X v
  have hi : v.val < (D.lv D.top).bases * (D.lv D.top).lanes := by
    rw [fit.bases, fit.lanes]
    have hh : Fintype.card X.network.Site = Fintype.card X.Base * 2 ^ g := by
      change Fintype.card (X.Base × BitWord g) = _
      rw [Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv g), Fintype.card_fin]
    exact hh ▸ v.isLt
  have hOut : (List.range (2 ^ a)).mapM (readArc D u y l) =
      some (List.ofFn fun k : Fin (2 ^ a) => List.ofFn (z (P1P7.outEdge X s k))) :=
    mapM_range_ofFn _ _ fun k => hArc (P1P7.outEdge X s k)
  let readIn (k : ℕ) : Option (List Bool) :=
    let disp := rdInDisp D u D.top y k
    if disp < 2 ^ g then
      readArc D u (rdInAddr D u D.top y k) (l ^^^ disp) (rdInFar D u D.top y k)
    else none
  have hIn : (List.range (2 ^ a)).mapM readIn =
      some (List.ofFn fun k : Fin (2 ^ a) => List.ofFn (z (P1P7.inEdge X s k))) := by
    apply mapM_range_ofFn
    intro k
    let src := X.slots.base.target.symm (s.1, k)
    let disp := X.slots.displacement src
    have h := hIncoming s.1 k
    have ha : rdInAddr D u D.top y k = (X.baseIndex src.1).val := congrArg Prod.fst h
    have hd : rdInDisp D u D.top y k = (bitWordFinEquiv g disp).val :=
      congrArg (fun p => p.2.1) h
    have hf : rdInFar D u D.top y k = src.2.val := congrArg (fun p => p.2.2) h
    have he : P1P7.inEdge X s k = ((src.1, s.2 - disp), src.2) := rfl
    dsimp only [readIn]
    rw [ha, hd, hf, ite_eq_left (bitWordFinEquiv g disp).isLt, he]
    change readArc D u (X.baseIndex src.1).val
      ((bitWordFinEquiv g s.2).val ^^^ (bitWordFinEquiv g disp).val) src.2.val = _
    rw [← bitWord_sub_val]
    exact hArc ((src.1, s.2 - disp), src.2)
  change readFinalHalf D u v.val =
    some (halfWords X s (WireTensor.edgeAssignment X.network.src X.network.dst z s))
  unfold readFinalHalf
  rw [ite_eq_left hi, fit.lanes, fit.slots, ← hs.1, ← hs.2]
  change (do
    let outgoing ← (List.range (2 ^ a)).mapM (readArc D u y l)
    let incoming ← (List.range (2 ^ a)).mapM readIn
    pure (outgoing, incoming)) = _
  rw [hOut, hIn]
  rfl

section P11Payload

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ h) {D : Dims} {d : ℕ}

local notation "C" => netData Bt κ hκ V a x Bk I T hn (netSiteOrder Bt κ hκ V Bk I T hn)

omit [Algebra (ZMod 2) F] in
/-- The concrete P11 tuple encoding has the claimed outgoing and incoming words at
each numbered final site. The right-hand side is the payload argument of `NetData.Wt`. -/
theorem readFinalHalf_p11 (H : NetRecordInputs Bt κ hκ V Bk I T hn D d)
    (t : (C).toCountData.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload (p11TupleRecords Bt κ hκ V a x Bk I T hn H) t).length ≤ m)
    (v : Fin ((C).P t.1 t.2.1)) :
    let s := ((C).ord t.1 t.2.1).symm v
    let X := (netExecution Bt κ hκ V Bk I T hn t.1).finalState t.2.1
    readFinalHalf D (List.ofFn (encTuple (p11TupleRecords Bt κ hκ V a x Bk I T hn H) m t)) v.val =
      some (halfWords X s (WireTensor.edgeAssignment X.network.src X.network.dst t.2.2.1 s)) := by
  let E := netExecution Bt κ hκ V Bk I T hn t.1
  let ι := t.2.1
  let X := E.finalState ι
  let P := H.panels t.1
  let Tr := H.terms t.1
  let fit := (P.final E ι).fits
  let z := t.2.2.1
  let R := p11TupleRecords Bt κ hκ V a x Bk I T hn H
  let u := List.ofFn (encTuple R m t)
  let s := (stateOrd X).symm v
  change readFinalHalf D u v.val =
    some (halfWords X s (WireTensor.edgeAssignment X.network.src X.network.dst z s))
  apply readFinalHalf_of_stateReads X fit u z _ _ v
  · intro e
    let y := finCongr fit.bases.symm (X.baseIndex e.1.1)
    let l := finCongr fit.lanes.symm (bitWordFinEquiv (h - T * S.laneBits) e.1.2)
    let k := finCongr fit.slots.symm e.2
    let i := (fit.arc).symm e
    have hArc := readArc_encTuple R t m hm y l k
    dsimp only at hArc
    let i' : Fin (FinalArcs D) := ⟨(y.val * (D.lv D.top).lanes + l.val) * (D.lv D.top).slots + k.val,
      idx_lt (idx_lt y.isLt l.isLt) k.isLt⟩
    change readArc D u y.val l.val k.val = some (List.ofFn (payloadOfExecution E P Tr ι z i')) at hArc
    have hi : i' = i := Fin.ext ((fit.arc_symm_val e.1.1 e.1.2 e.2).symm)
    rw [hi, executionPayload_word E P Tr ι, Equiv.apply_symm_apply] at hArc
    exact hArc
  · intro y k
    let y' := finCongr fit.bases.symm (X.baseIndex y)
    let k' := finCongr fit.slots.symm k
    let i := ord (D.lv D.top).bases (D.lv D.top).slots (y', k')
    have hIn := readIncoming_encTuple R t m hm y' k'
    dsimp only at hIn
    let recs := levelOfExecution E P Tr ι (finalLevel D)
    change (rdInAddr D u D.top y'.val k'.val, rdInDisp D u D.top y'.val k'.val,
      rdInFar D u D.top y'.val k'.val) = ((recs.inAddr i).val, (recs.inDisp i).val, (recs.inFar i).val) at hIn
    dsimp only [recs] at hIn
    rw [levelOfExecution_final E P Tr ι] at hIn
    have hi : fit.baseSlot i = (y, k) := by
      simp only [PanelFits.baseSlot, i, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply]
      change (X.baseIndex.symm (finCongr fit.bases y'), finCongr fit.slots k') = (y, k)
      have hy' : finCongr fit.bases y' = X.baseIndex y := Fin.ext rfl
      have hk' : finCongr fit.slots k' = k := Fin.ext rfl
      rw [hy', hk', Equiv.symm_apply_apply]
    simp only [levelRecordsOfState, hi] at hIn
    exact hIn

end P11Payload

end FinalHalf

section FixedD9

variable {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b : ℕ) (x : List Bool)

noncomputable abbrev fixedNetData : P1Count.NetData F :=
  let t := lpTime a b x.length
  let K := portConsts Bt
  netData Bt κ hκ V a x (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t)
    (P1Wrap.Params.T K t) (lane_bound K S.laneBits (portConsts_b0 Bt) t)
    (P1Int.P11.fixedOrd Bt κ hκ V a b x)

theorem fixed_finP (d bigBias termBias : ℕ)
    (σ : (fixedNetData Bt κ hκ V a b x).Sk) (ι : (fixedNetData Bt κ hκ V a b x).Ch σ) :
    P1ChkFinal.finP (P1Int.P11.fixedDims Bt V a b x d bigBias termBias) =
      (fixedNetData Bt κ hκ V a b x).P σ ι := by
  let t := lpTime a b x.length
  let K := portConsts Bt
  have h := P1Wit.SolSpace.genuineDims_chainLen Bt κ hκ K (toOAI V) 1 t
    (a * (x.length ^ 2 + 1)) d bigBias termBias (P1Int.four_le_baseDegree S)
    (lane_bound K S.laneBits (portConsts_b0 Bt) t) σ ι
  unfold P1ChkFinal.finP
  change (P1Int.P11.fixedDims Bt V a b x d bigBias termBias).chainLen =
    (fixedNetData Bt κ hκ V a b x).P σ ι + 1 at h
  rw [h, Nat.add_sub_cancel]

end FixedD9

/-- Uniform bound on the compressor's width parameter at input length `n`. -/
noncomputable def Mbar {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b n : ℕ) : ℕ :=
  let t := lpTime a b n
  let K := portConsts Bt
  Bt.growthConstant ^ P1Wrap.Params.T K t * (P1Net.tupWidth (toOAI V) (P1Wrap.Params.B t) + 1)

theorem Mbar_pos {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b n : ℕ) : 0 < Mbar Bt V a b n :=
  Nat.mul_pos (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) Bt.growthConstant_ge_two)) (Nat.succ_pos _)

theorem widthParam_le_Mbar {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b n : ℕ)
    (σ : P1Wit.SolWitfill.RoutedSkeleton V
      (P1Wrap.Params.I 1 (lpTime a b n)) (P1Wrap.Params.h (lpTime a b n))) :
    let t := lpTime a b n
    let X := P1Wit.SolWitfill.routedState (S := S) V (P1Wrap.Params.B t) (P1Wrap.Params.I 1 t) σ
    Bt.growthConstant ^ P1Wrap.Params.T (portConsts Bt) t * (X.maxWireWidth + 1) ≤ Mbar Bt V a b n := by
  dsimp only [Mbar]
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  exact P1Wit.SolSpace.initial_width_le (toOAI V) 1 (P1Int.four_le_baseDegree S) σ

end SolCone

open OAI.Computability.VPVNP.NetworkKernel
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open scoped Classical

/-- Decode the requested terminal half, then assemble the cone backwards through the P6
phase rows. Reject an invalid ordinal or a failed storage or size check. -/
noncomputable def Wof {F : Type} [CommRing F] (dims : ℕ → P1Wit.Dims)
    (parentCap C : ℕ) (widthCap : ℕ → ℕ) (dH : ℕ)
    (kernels : SolCone.KernelValues F) (factors : Factor0In F → List (Label F))
    (x u : List Bool) (v : ℕ) : F :=
  let D := dims x.length
  let w := widthCap x.length
  let lanes := (D.lv D.top).lanes
  let pos := (v / lanes, v % lanes)
  if D.fixedLen ≤ u.length ∧ v < P1ChkFinal.finP D then
    if SolCone.widthsWithin w (SolCone.readHalfWidths D u D.top pos) then
      match SolCone.readFinalHalf D u v with
      | none => 0
      | some half =>
        match SolCone.assembleCheckedChain (SolCone.phaseAllowed D u parentCap w) (SolCone.phasePreimages D u)
            (SolCone.phaseHalves D u) (SolCone.phaseKernel kernels (SolCone.conePad C w) dH D u) (List.range D.top) [(pos, half)] with
        | none => 0
        | some (keys, levels) =>
          let initial := (factors ((x, u), (⟨1⟩, keys))).map Label.val
          (P1P5.runLevels levels initial).getD 0 0
    else 0
  else 0

open SolCone in
/-- Interpret the checked cone of a selected half-label using the ordered level evaluator. -/
theorem SolCone.Wof_eq_checked {F : Type} [CommRing F] (dims : ℕ → P1Wit.Dims)
    (parentCap C : ℕ) (widthCap : ℕ → ℕ) (dH : ℕ) (kernels : KernelValues F)
    (factors : Factor0In F → List (Label F)) (x u : List Bool) (v : ℕ)
    {N Y : Network} (chain : TermChain F N Y) (src : KeyCoding N) (dst : KeyCoding Y)
    (F1 : Factors F N) (s : Y.Site) (z : Y.Half s) :
    let D := dims x.length
    let w := widthCap x.length
    let pos := (v / (D.lv D.top).lanes, v % (D.lv D.top).lanes)
    D.fixedLen ≤ u.length → v < P1ChkFinal.finP D → pos = dst.position s →
    widthsWithin w (readHalfWidths D u D.top pos) = true → readFinalHalf D u v = some (dst.half s z) →
    CheckedChainOK (phaseAllowed D u parentCap w) (phasePreimages D u) (phaseHalves D u)
      (phaseKernel kernels (conePad C w) dH D u) chain src dst (List.range D.top) →
    (∀ ks : List (P1P5.Key N), (factors ((x, u), (⟨1⟩, ks.map src.key))).map Label.val = P1P5.stateOfO ks F1) →
    Wof dims parentCap C widthCap dH kernels factors x u v = P1P5.chainPush chain F1 s z := by
  classical
  intro D w pos hstore hbound hpos hwidth hhalf hchain hfactor
  let fin : List (P1P5.Key Y) := [⟨s, z⟩]
  obtain ⟨o, ho, htables⟩ := assembleCheckedChain_good _ _ _ _ chain src dst _ fin hchain
  have hfinal : (⟨s, z⟩ : P1P5.Key Y) ∈ fin := List.mem_singleton_self _
  have index : fin.idxOf (⟨s, z⟩ : P1P5.Key Y) = 0 := List.idxOf_cons_self
  change (if D.fixedLen ≤ u.length ∧ v < P1ChkFinal.finP D then _ else _) = _
  rw [ite_eq_left ⟨hstore, hbound⟩]
  change (if widthsWithin w (readHalfWidths D u D.top pos) then _ else _) = _
  rw [ite_eq_left hwidth, hhalf]
  simp only
  have finalCode : [(pos, dst.half s z)] = fin.map dst.key := by rw [hpos]; rfl
  rw [finalCode, htables]
  simp only
  rw [hfactor]
  simpa only [index] using (P1P5.Wv_eq_runO chain o fin ho F1 s z hfinal).symm

section P11Correct

open SolCone P1Wit P1Wit.SolWitfill P1P7 P1ChkFinal
open OAI.Computability.VPVNP OAI.Computability.VPVNP.CompressorRecords

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (Bk : ℕ) [NeZero Bk] (I : ℕ) [NeZero I]
  {h : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ h) {D : Dims} {d : ℕ}

local notation "CountNet" => netData Bt κ hκ V a x Bk I (h := h) T hn
  (netSiteOrder Bt κ hκ V Bk I (h := h) T hn)

/-- The checked cone at a genuinely encoded P11 site, before specializing the time and
dimension parameters to their fixed values. -/
theorem SolCone.Wof_eq_p11 (H : NetRecordInputs Bt κ hκ V Bk I (h := h) T hn D d)
    (q : (CountNet).toCountData.Tup d) (m : ℕ)
    (hm : D.fixedLen + (tuplePayload (p11TupleRecords Bt κ hκ V a x Bk I T hn H) q).length ≤ m)
    (v : Fin ((CountNet).P q.1 q.2.1))
    (dims : ℕ → Dims) (hdim : dims x.length = D) (widthCap : ℕ → ℕ)
    (values : KernelValues F) (hv : ScheduleKernelsOK Bt κ hκ values)
    (factors : Factor0In F → List (Label F)) :
    let X := routedState (S := S) V Bk I q.1
    let E := netExecution Bt κ hκ V Bk I (h := h) T hn q.1
    let u := List.ofFn (encTuple (p11TupleRecords Bt κ hκ V a x Bk I T hn H) m q)
    let ι := q.2.1
    BranchExtras Bt κ hκ D u E (executeOrigins Bt κ hκ T hn X) ι 0 →
    Bt.growthConstant ^ T * (X.maxWireWidth + 1) ≤ widthCap x.length →
    v.val < P1ChkFinal.finP D →
    factor0Agreement factors V a Bk I (h := h) (four_le_baseDegree S) q.1 x u P1Benes.NetBridge.bset →
    Wof dims Bt.recordLimit Bt.growthConstant widthCap (2 ^ S.expanderExponent) values factors x u v.val = (CountNet).Wt q.1 ι q.2.2.1 v := by
  intro X E u ι hextra hcap hvbound hfactors
  let Y := E.finalState ι
  let chain := E.termChain (Bt.records κ hκ T hn X) ι
  let F1 := netF1 V a x Bk I h (four_le_baseDegree S) F q.1
  let s := (stateOrd Y).symm v
  let z := WireTensor.edgeAssignment Y.network.src Y.network.dst q.2.2.1 s
  have hpanels : BranchPanelsOK D u E ι 0 :=
    branchPanels_encTuple _ q m hm E (H.panels q.1) (H.terms q.1) ι (fun _ => rfl)
  have hCaps : BranchCapsOK Bt.recordLimit (widthCap x.length) E ι :=
    BranchCapsOK.monoWidth E hcap ι (branchCaps_execute Bt κ hκ T hn X ι)
  let origins := executeOrigins Bt κ hκ T hn X
  have hpad := branchPad_of_caps Bt κ hκ E origins ι hCaps
  have hchain := checkedChain_execution Bt κ hκ values hv (conePad Bt.growthConstant (widthCap x.length))
    D u Bt.recordLimit (widthCap x.length) E (Bt.records κ hκ T hn X) origins ι 0 hpanels hextra hCaps hpad
  have hhalf := readFinalHalf_p11 Bt κ hκ V a x Bk I T hn H q m hm v
  have fit := ((H.panels q.1).final E ι).fits
  have hposition := stateOrd_symm_apply Y v
  let pos := (v.val / (D.lv D.top).lanes, v.val % (D.lv D.top).lanes)
  have hpos : pos = (stateCoding Y).position s := by
    change (v.val / (D.lv D.top).lanes, v.val % (D.lv D.top).lanes) = _
    rw [fit.lanes]
    exact Prod.ext hposition.1.symm hposition.2.symm
  have hpanelFinal : StatePanelOK D u D.top Y := by
    refine ⟨fit.bases, fit.slots, fit.lanes, fun y => ?_⟩
    exact panelMatch_encTuple _ q m hm (finalLevel D) Y fit _ (levelOfExecution_final E (H.panels q.1) (H.terms q.1) ι) y
  have hwidth : widthsWithin (widthCap x.length) (readHalfWidths D u D.top pos) = true :=
    hpos.symm ▸ stateWidthsWithin D u D.top Y hpanelFinal _ (BranchCapsOK.finalWidth E ι hCaps) s
  have hF (ks : List (P1P5.Key X.network)) :
      (factors ((x, u), (⟨1⟩, ks.map (stateCoding X).key))).map Label.val = P1P5.stateOfO ks F1 := by
    have hh := hfactors (1 : F) ks
    change factors ((x, u), (⟨1⟩, ks.map (stateCoding X).key)) = _ at hh
    simp only [hh, List.map_map, one_mul]
    rfl
  have hstore : D.fixedLen ≤ u.length := by
    change D.fixedLen ≤ (List.ofFn (encTuple (p11TupleRecords Bt κ hκ V a x Bk I T hn H) m q)).length
    rw [List.length_ofFn]
    omega
  change Wof dims Bt.recordLimit Bt.growthConstant widthCap (2 ^ S.expanderExponent) values factors x u v.val =
    P1P5.chainPush chain F1 s z
  apply Wof_eq_checked dims _ _ _ _ _ _ _ _ _ chain (stateCoding X) (stateCoding Y) F1 s z
  all_goals try rw [hdim]
  · exact hstore
  · exact hvbound
  · exact hpos
  · exact hwidth
  · exact hhalf
  · simpa only [Nat.sub_zero, List.range_eq_range'] using hchain
  · exact hF


/-- The factor-zero agreement of a witness reader on the genuine P11 records at one input. -/
def SolCone.P11FactorAgreement (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K))
    (factors : Factor0In F → List (Label F)) : Prop :=
  ∀ (H : NetRecordInputs Bt κ hκ V Bk I (h := h) T hn D d),
    (∀ tape, (H.tape_order tape).val = (ρ tape).val) →
    let A := p11TupleRecords Bt κ hκ V a x Bk I T hn H
    ∀ (q : (CountNet).toCountData.Tup d) (m : ℕ),
      D.fixedLen + (tuplePayload A q).length ≤ m →
      factor0Agreement factors V a Bk I (h := h) (four_le_baseDegree S) q.1
        x (List.ofFn (encTuple A m q)) P1Benes.NetBridge.bset

/-- The concrete Wof equation for every genuine P6 tuple and every D9 site. -/
def SolCone.P11ConeCorrect (dims : ℕ → Dims) (widthCap : ℕ → ℕ)
    (values : KernelValues F) (factors : Factor0In F → List (Label F))
    (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K)) : Prop :=
  ∀ (H : NetRecordInputs Bt κ hκ V Bk I (h := h) T hn D d),
    (∀ tape, (H.tape_order tape).val = (ρ tape).val) →
    let A := p11TupleRecords Bt κ hκ V a x Bk I T hn H
    ∀ (q : (CountNet).toCountData.Tup d) (m : ℕ),
      D.fixedLen + (tuplePayload A q).length ≤ m →
      ∀ (v : Fin ((CountNet).P q.1 q.2.1)),
        let X := routedState (S := S) V Bk I (h := h) q.1
        let E := netExecution Bt κ hκ V Bk I (h := h) T hn q.1
        let u := List.ofFn (encTuple A m q)
        let ι := q.2.1
        BranchExtras Bt κ hκ D u E (executeOrigins Bt κ hκ T hn X) ι 0 →
        Wof dims Bt.recordLimit Bt.growthConstant widthCap (2 ^ S.expanderExponent)
          values factors x u v.val = (CountNet).Wt q.1 ι q.2.2.1 v

theorem SolCone.p11ConeCorrect_of (dims : ℕ → Dims) (hdim : dims x.length = D) (widthCap : ℕ → ℕ)
    (values : KernelValues F) (hv : ScheduleKernelsOK Bt κ hκ values)
    (factors : Factor0In F → List (Label F))
    (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K))
    (hf : P11FactorAgreement Bt κ hκ V a x Bk I T hn (D := D) (d := d) ρ factors)
    (hc : ∀ σ : RoutedSkeleton V I h,
      Bt.growthConstant ^ T * ((routedState (S := S) V Bk I (h := h) σ).maxWireWidth + 1) ≤ widthCap x.length)
    (hord : ∀ (σ : (CountNet).Sk) (ι : (CountNet).Ch σ), P1ChkFinal.finP D = (CountNet).P σ ι) :
    P11ConeCorrect Bt κ hκ V a x Bk I T hn (D := D) (d := d) dims widthCap values factors ρ := by
  intro H ht A q m hm v X E u ι he
  have hvD : v.val < P1ChkFinal.finP D := v.isLt.trans_eq (hord q.1 ι).symm
  exact Wof_eq_p11 Bt κ hκ V a x Bk I T hn H q m hm v dims hdim widthCap values hv factors
    he (hc q.1) hvD (hf H ht q m hm)

end P11Correct

section FixedCorrect

open SolCone P1Wit P1Wit.SolWitfill
open OAI.Computability.VPVNP

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
  {F : Type} [CommRing F] [Fintype F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
  (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ) (x : List Bool)

/-- The genuine P6 encoding at the fixed P11 parameters computes its factor in D9 order. -/
theorem wof_def_ok (ρ : (toOAI V).K ≃ Fin (Fintype.card (toOAI V).K))
    (values : KernelValues F) (hv : ScheduleKernelsOK Bt κ hκ values)
    (hf : Factor0Hyp Bt κ hκ V a b d bigBias termBias ρ P1Benes.NetBridge.bset) :
    let time := lpTime a b x.length
    let T := P1Wrap.Params.T (portConsts Bt) time
    let hn := lane_bound (portConsts Bt) S.laneBits (portConsts_b0 Bt) time
    P11ConeCorrect Bt κ hκ V a x (P1Wrap.Params.B time) (P1Wrap.Params.I 1 time) T hn
      (D := fixedDims Bt V a b x d bigBias termBias) (d := d)
      (fun n => SolSpace.genuineDims Bt (portConsts Bt) (toOAI V) 1
        (lpTime a b n) (a * (n ^ 2 + 1)) d bigBias termBias)
      (Mbar Bt V a b) values hf.choose ρ := by
  intro time T hn
  apply p11ConeCorrect_of Bt κ hκ V a x (P1Wrap.Params.B time) (P1Wrap.Params.I 1 time) T hn
  · rfl
  · exact hv
  · exact hf.choose_spec.choose_spec.2 x
  · exact widthParam_le_Mbar Bt V a b x.length
  · exact fixed_finP Bt κ hκ V a b x d bigBias termBias

end FixedCorrect

/-- D14 budget for the full C13 factor evaluation, including P6 scans. -/
noncomputable def βW {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    (V : C1Challenge.Machine) (a b c : ℕ) {M Kqry : ℕ → ℕ} (p : P1ChkFinal.QDom M Kqry) : ℕ :=
  let n := p.val.1.length
  let t := lpTime a b n
  let K := portConsts Bt
  let Λ := (S.steps + 1) * P1Wrap.Params.T K t
  let C := Bt.growthConstant
  c * ((Λ + 1) * (n + p.val.2.1.length + p.val.2.2.length + 1)) +
    2 ^ (c * C * SolCone.Mbar Bt V a b n) * (Nat.log 2 (n + 1) + p.val.2.2.length + 1) ^ c

end P1SolCone

#print axioms P1SolCone.SolCone.readFinalHalf_p11
#print axioms P1SolCone.SolCone.halfWords_injective
#print axioms P1SolCone.SolCone.halfWords_of_widths
#print axioms P1SolCone.SolCone.fixed_finP
#print axioms P1SolCone.SolCone.widthParam_le_Mbar
#print axioms P1SolCone.SolCone.Wof_eq_checked
#print axioms P1SolCone.SolCone.Wof_eq_p11
#print axioms P1SolCone.wof_def_ok
