import P1Net.StateGraph
import P1P7.Defs
import P1ChkDir.P6

/-!
# P1ChkDir.C4: the level-0 panels computed from the directory (check C4)

Lane P1-lean-W2-chkdir. Paper `subsec:witness`, check C4: the panel (P1), (P2) of a level-0 base equals the one
computed from the directory entries of its big interval, of the owners named there, and the construction of the
network. In Lean the level-0 state is lane net's `P1Net.stateNet I σ ha Wc Ws Wt` (the degree padding `regularize` of
`preGraph I σ`, small intervals per big interval `N = 2 ^ h`), and the panel is lane P7's `P1P7.panel`.

The skeleton `σ` enters the panel of base `((ι, l), t)` only through the four half-edge mates `netMate I σ ((ι, l), s)`
(`s < 4`), and these only through `interMate`: the big blocks `bigQ`, the next and previous owners, and the big block
of the named owner. So:
* `nextT_eq_nextOwner`, `prevT_eq_prevOwner`: the true directory entries of `P1ChkDir.Basic` ARE the owners of
  lane net (`N = 2 ^ h`);
* `interMateD L u`, `netMateD L u`: the links computed from the STORED directory of the witness `u` (layout `L`;
  an invalid field reads as `0` or `none`; this only matters before C1-C3 pass);
* `netMateD_eq`: with the true directory of `σ`, `netMateD = netMate I σ`;
* `panelOf ha mt Wc Ws Wt y`: the panel of base `y` given any mate function `mt`, by the formulas of `regularize`
  (out-slot `i < 4` with mate `q` goes to in-slot `q.2` of `(q.1, t)`; every other out-slot `k` of `(v, t)` to in-slot
  `k` of `(v, !t)`; the in-part equals the out-part because the slot map is an involution and the displacement of an
  edge is the same from both ends);
* `panelOf_eq`: `panelOf ha (netMate I σ) = P1P7.panel (stateNet I σ ha Wc Ws Wt)`;
* `panelD_eq`: the panel computed from a TRUE directory is the true panel;
* on the witness of lane P6 (`P1Wit.Layout`, level `0`): `PanelStored` (the panel fields of base address `A` hold the
  numbers of a panel; displacements and lanes numbered by OpenAI's `bitWordFinEquiv`), the check `C4` at a base,
  the family `C4F` of decision D5 (index = level-0 address), `C4F_out`, `C4F_iff`, and `C4_stage`: once the
  directory is true (stage 0), every C4 index passes iff every level-0 panel field holds the true panel of
  `stateNet I σ(u)`.
-/

namespace P1ChkDir

open P1Net OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {h I : ℕ}

/-! ## The true directory is the owner structure of the network -/

theorem minOpt_congr {s t : Finset (Fin I)} (hst : s = t) :
    (if hS : s.Nonempty then some (s.min' hS) else none) =
      (if hT : t.Nonempty then some (t.min' hT) else none) := by
  subst hst
  rfl

theorem maxOpt_congr {s t : Finset (Fin I)} (hst : s = t) :
    (if hS : s.Nonempty then some (s.max' hS) else none) =
      (if hT : t.Nonempty then some (t.max' hT) else none) := by
  subst hst
  rfl

theorem nextT_eq_nextOwner (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K) (δ : Fin 3) :
    nextT (2 ^ h) σ ι k δ = nextOwner I σ k ι (portQ I σ k ι δ) := by
  unfold nextT nextScan nextOwner
  apply minOpt_congr
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ownsTab_betaTab]
  exact Iff.rfl

theorem prevT_eq_prevOwner (σ : Fin (I * 2 ^ h) → K → Fin 3) (ι : Fin I) (k : K) (δ : Fin 3) :
    prevT (2 ^ h) σ ι k δ = prevOwner I σ k ι (portQ I σ k ι δ) := by
  unfold prevT prevScan prevOwner
  apply maxOpt_congr
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ownsTab_betaTab]
  exact Iff.rfl

/-! ## Links computed from the stored directory -/

variable (L : DirLayout K I (2 ^ h)) (u : List Bool)

/-- Stored start block (`0` if invalid). -/
def bD (ι : Fin I) (k : K) : ℤ := (L.betaS u ι k).getD 0

/-- Stored next owner (`none` if invalid). -/
def nD (ι : Fin I) (k : K) (δ : Fin 3) : Option (Fin I) := (L.nextS u ι k δ).getD none

/-- Stored previous owner (`none` if invalid). -/
def pD (ι : Fin I) (k : K) (δ : Fin 3) : Option (Fin I) := (L.prevS u ι k δ).getD none

/-- The big block of port `δ` of big interval `ι` on tape `k`, from the stored start block. -/
def portQD (ι : Fin I) (k : K) (δ : Fin 3) : ℤ := bigOf (2 ^ h) (bD L u ι k) - 1 + (δ : ℤ)

/-- The port of big block `Q` in big interval `ι'`, from the stored start block of `ι'`. -/
def slotD (ι' : Fin I) (k : K) (Q : ℤ) : Fin 3 := finOfInt 3 (Q - bigOf (2 ^ h) (bD L u ι' k) + 1)

/-- The links between big intervals (`P1Net.interMate`) computed from the stored directory. -/
def interMateD (ι : Fin I) (l : Loc K h) (s : Fin 4) : Option (Fin I × Loc K h × Fin 4) :=
  match l with
  | .portOut k δ =>
    if s = 1 then (nD L u ι k δ).map fun ι' => (ι', .portIn k (slotD L u ι' k (portQD L u ι k δ)), 1) else none
  | .portIn k δ =>
    if s = 1 then (pD L u ι k δ).map fun ι' => (ι', .portOut k (slotD L u ι' k (portQD L u ι k δ)), 1) else none
  | .eOut => if s = 1 then (colSucc ι).map fun ι' => (ι', .eIn, 1) else none
  | .eIn => if s = 1 then (colPred ι).map fun ι' => (ι', .eOut, 1) else none
  | _ => none

/-- The half-edge partners (`P1Net.netMate`) computed from the stored directory. -/
noncomputable def netMateD (p : (Fin I × Loc K h) × Fin 4) : Option ((Fin I × Loc K h) × Fin 4) :=
  match locMate p.1.2 p.2 with
  | some q => some ((p.1.1, q.1), q.2)
  | none => (interMateD L u p.1.1 p.1.2 p.2).map fun r => ((r.1, r.2.1), r.2.2)

section True

variable (σ : Fin (I * 2 ^ h) → K → Fin 3) (hβ : ∀ ι k, L.betaS u ι k = some (betaT (2 ^ h) σ ι k))
  (hown : ∀ ι k δ, L.nextS u ι k δ = some (nextT (2 ^ h) σ ι k δ) ∧
    L.prevS u ι k δ = some (prevT (2 ^ h) σ ι k δ))

include hβ in
theorem bD_eq (ι : Fin I) (k : K) : bD L u ι k = betaT (2 ^ h) σ ι k := by
  simp [bD, hβ]

include hβ in
theorem portQD_eq (ι : Fin I) (k : K) (δ : Fin 3) : portQD L u ι k δ = portQ I σ k ι δ := by
  simp only [portQD, bD_eq L u σ hβ]
  rfl

include hβ in
theorem slotD_eq (ι' : Fin I) (k : K) (Q : ℤ) : slotD L u ι' k Q = portSlot I σ k ι' Q := by
  simp only [slotD, bD_eq L u σ hβ]
  rfl

include hβ hown in
/-- With the true directory of `σ`, the stored links are the links of the network. -/
theorem interMateD_eq (ι : Fin I) (l : Loc K h) (s : Fin 4) : interMateD L u ι l s = interMate I σ ι l s := by
  have hn : ∀ ι k δ, nD L u ι k δ = nextOwner I σ k ι (portQ I σ k ι δ) := fun ι k δ => by
    simp [nD, (hown ι k δ).1, nextT_eq_nextOwner]
  have hp : ∀ ι k δ, pD L u ι k δ = prevOwner I σ k ι (portQ I σ k ι δ) := fun ι k δ => by
    simp [pD, (hown ι k δ).2, prevT_eq_prevOwner]
  cases l <;> simp only [interMateD, interMate, hn, hp, portQD_eq L u σ hβ, slotD_eq L u σ hβ]

include hβ hown in
/-- With the true directory of `σ`, the stored half-edge partners are those of the network. -/
theorem netMateD_eq (p : (Fin I × Loc K h) × Fin 4) : netMateD L u p = netMate I σ p := by
  unfold netMateD netMate
  cases hl : locMate p.1.2 p.2 with
  | some q => simp only [hl]
  | none => simp only [hl, interMateD_eq L u σ hβ hown]

end True

/-! ## The panel of a base from a mate function (the formulas of `regularize`) -/

section Panel

variable {a : ℕ} (ha : 4 ≤ 2 ^ a)

/-- The level-0 address of a base (lane net, `stateNet_baseIndex_val`). -/
noncomputable def addrL (y : (Fin I × Loc K h) × Bool) : ℕ :=
  (if y.2 then 1 else 0) + 2 * (locNum K h y.1.2 + locCount K h * y.1.1)

/-- Head of out-slot `k` of base `y` (= tail of in-slot `k`: the slot map is an involution). -/
def tgtOf (mt : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) : ((Fin I × Loc K h) × Bool) × Fin (2 ^ a) :=
  match PreGraph.slot4 k with
  | some i =>
    match mt (y.1, i) with
    | some q => ((q.1, y.2), q.2.castLE ha)
    | none => ((y.1, !y.2), k)
  | none => ((y.1, !y.2), k)

/-- Lane displacement of out-slot `k` of base `y` (the same on the reverse arc). -/
def dispOf (mt : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) : BitWord h :=
  match PreGraph.slot4 k with
  | some i =>
    match mt (y.1, i) with
    | some q => disp1 I (y.1, i) + disp1 I q
    | none => 0
  | none => 0

/-- Width of out-slot `k` of base `y` at a lane. -/
def widthOf (mt : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4)) (Wc Ws Wt : ℕ)
    (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) (_lane : BitWord h) : ℕ :=
  match PreGraph.slot4 k with
  | some i => if y.2 then 0 else if mt (y.1, i) = none then 0 else baseWidth Wc Ws Wt y.1.2 i
  | none => 0

/-- The panel (P1), (P2) of base `y` for the mate function `mt`, in the shape of `P1P7.panel`. -/
noncomputable def panelOf (mt : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4)) (Wc Ws Wt : ℕ)
    (y : (Fin I × Loc K h) × Bool) :
    (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) × (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) ×
      (Fin (2 ^ a) → BitWord h → ℕ) :=
  (fun k => (addrL (tgtOf ha mt y k).1, dispOf mt y k), fun k => ((tgtOf ha mt y k).2 : ℕ),
    fun k => (addrL (tgtOf ha mt y k).1, dispOf mt y k), fun k => ((tgtOf ha mt y k).2 : ℕ),
    fun k lane => widthOf mt Wc Ws Wt y k lane)

variable [NeZero I] (σ : Fin (I * 2 ^ h) → K → Fin 3) (Wc Ws Wt : ℕ)

theorem stateNet_target (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    (stateNet (K := K) I σ ha Wc Ws Wt).slots.base.target (y, k) = tgtOf ha (netMate I σ) y k := by
  show (preGraph (K := K) I σ).slotMap ha (y, k) = _
  unfold PreGraph.slotMap tgtOf
  dsimp only [preGraph]
  cases hs : PreGraph.slot4 (a := a) k with
  | none => simp only [hs]
  | some i =>
    cases hm : netMate I σ (y.1, i) with
    | none => simp only [hs, hm]
    | some q => simp only [hs, hm]

theorem stateNet_target_symm (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    (stateNet (K := K) I σ ha Wc Ws Wt).slots.base.target.symm (y, k) = tgtOf ha (netMate I σ) y k := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [← stateNet_target ha σ Wc Ws Wt y k]
  exact ((preGraph (K := K) I σ).slotMap_slotMap ha (y, k)).symm

theorem stateNet_disp (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    (stateNet (K := K) I σ ha Wc Ws Wt).slots.displacement (y, k) = dispOf (netMate I σ) y k := by
  show (preGraph (K := K) I σ).displacement (y, k) = _
  unfold PreGraph.displacement dispOf
  dsimp only [preGraph]
  cases hs : PreGraph.slot4 (a := a) k with
  | none => simp only [hs]
  | some i =>
    cases hm : netMate I σ (y.1, i) with
    | none => simp only [hs, hm]
    | some q => simp only [hs, hm, netDisp]

theorem stateNet_disp_symm (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    (stateNet (K := K) I σ ha Wc Ws Wt).slots.displacement (tgtOf ha (netMate I σ) y k) =
      dispOf (netMate I σ) y k := by
  show (preGraph (K := K) I σ).displacement (tgtOf ha (netMate I σ) y k) = _
  unfold tgtOf dispOf
  cases hs : PreGraph.slot4 (a := a) k with
  | none => simp only [hs, PreGraph.displacement]
  | some i =>
    cases hm : netMate I σ (y.1, i) with
    | none => simp only [hs, hm, PreGraph.displacement, preGraph]
    | some q =>
      obtain ⟨v', s'⟩ := q
      have hq := netMate_symm I σ hm
      simp only [hm, PreGraph.displacement, PreGraph.slot4_castLE, preGraph, hq, netDisp]
      exact add_comm _ _

theorem stateNet_width (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) (lane : BitWord h) :
    (stateNet (K := K) I σ ha Wc Ws Wt).width ((y, k), lane) = widthOf (netMate I σ) Wc Ws Wt y k lane := by
  show (preGraph (K := K) I σ).padWidth (netWidth I σ Wc Ws Wt) ((y, k), lane) = _
  unfold PreGraph.padWidth widthOf netWidth
  rfl

theorem stateNet_addr (z : (Fin I × Loc K h) × Bool) :
    P1P7.addr (stateNet (K := K) I σ ha Wc Ws Wt) z = addrL z := by
  obtain ⟨⟨ι, l⟩, t⟩ := z
  exact stateNet_baseIndex_val I σ ha Wc Ws Wt ι l t

theorem outNbr_eq (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    P1P7.outNbr (stateNet (K := K) I σ ha Wc Ws Wt) y k =
      (addrL (tgtOf ha (netMate I σ) y k).1, dispOf (netMate I σ) y k) := by
  unfold P1P7.outNbr
  erw [stateNet_target ha σ Wc Ws Wt y k, stateNet_disp ha σ Wc Ws Wt y k, stateNet_addr ha σ Wc Ws Wt]

theorem inNbr_eq (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    P1P7.inNbr (stateNet (K := K) I σ ha Wc Ws Wt) y k =
      (addrL (tgtOf ha (netMate I σ) y k).1, dispOf (netMate I σ) y k) := by
  unfold P1P7.inNbr
  erw [stateNet_target_symm ha σ Wc Ws Wt y k, stateNet_disp_symm ha σ Wc Ws Wt y k,
    stateNet_addr ha σ Wc Ws Wt]

theorem outFar_eq (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    P1P7.outFar (stateNet (K := K) I σ ha Wc Ws Wt) y k = ((tgtOf ha (netMate I σ) y k).2 : ℕ) := by
  unfold P1P7.outFar
  erw [stateNet_target ha σ Wc Ws Wt y k]

theorem inFar_eq (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) :
    P1P7.inFar (stateNet (K := K) I σ ha Wc Ws Wt) y k = ((tgtOf ha (netMate I σ) y k).2 : ℕ) := by
  unfold P1P7.inFar
  erw [stateNet_target_symm ha σ Wc Ws Wt y k]

theorem outWidths_eq (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) (lane : BitWord h) :
    P1P7.outWidths (stateNet (K := K) I σ ha Wc Ws Wt) y k lane = widthOf (netMate I σ) Wc Ws Wt y k lane := by
  unfold P1P7.outWidths
  erw [stateNet_width ha σ Wc Ws Wt y k lane]

/-- **The panel of the level-0 state** is `panelOf` of the network's half-edge partners. -/
theorem panelOf_eq (y : (Fin I × Loc K h) × Bool) :
    panelOf ha (netMate I σ) Wc Ws Wt y = P1P7.panel (stateNet (K := K) I σ ha Wc Ws Wt) y := by
  unfold panelOf P1P7.panel
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · funext k
    exact (outNbr_eq ha σ Wc Ws Wt y k).symm
  · funext k
    exact (outFar_eq ha σ Wc Ws Wt y k).symm
  · funext k
    exact (inNbr_eq ha σ Wc Ws Wt y k).symm
  · funext k
    exact (inFar_eq ha σ Wc Ws Wt y k).symm
  · funext k lane
    exact (outWidths_eq ha σ Wc Ws Wt y k lane).symm

/-- **C4, the mathematical content.** The panel computed from a TRUE directory (stored start blocks and owners
of `σ`) is the panel of base `y` in the level-0 state `stateNet I σ ha Wc Ws Wt`. -/
theorem panelD_eq (L : DirLayout K I (2 ^ h)) (u : List Bool)
    (hβ : ∀ ι k, L.betaS u ι k = some (betaT (2 ^ h) σ ι k))
    (hown : ∀ ι k δ, L.nextS u ι k δ = some (nextT (2 ^ h) σ ι k δ) ∧
      L.prevS u ι k δ = some (prevT (2 ^ h) σ ι k δ))
    (y : (Fin I × Loc K h) × Bool) :
    panelOf ha (netMateD L u) Wc Ws Wt y = P1P7.panel (stateNet (K := K) I σ ha Wc Ws Wt) y := by
  rw [← panelOf_eq ha σ Wc Ws Wt y]
  have : netMateD L u = netMate I σ := funext fun p => netMateD_eq L u σ hβ hown p
  rw [this]

end Panel

/-! ## C4 on the witness of lane P6 (level 0) -/

section P6

open P1Wit

variable {a : ℕ} (ha : 4 ≤ 2 ^ a)

/-- The number of a lane word (OpenAI `bitWordFinEquiv`; P6 numbers displacements and lanes this way). -/
def bwNum {g : ℕ} (w : BitWord g) : ℕ := (bitWordFinEquiv g w : ℕ)

/-- The level-0 panel fields of the witness `u` at base address `A` hold the numbers of the panel `P`
(out-slot and in-slot records (P1), widths (P2) at every lane). -/
def PanelStored (D : Dims) (u : List Bool) (A : ℕ)
    (P : (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) × (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) ×
      (Fin (2 ^ a) → BitWord h → ℕ)) : Prop :=
  ∀ k : Fin (2 ^ a), rdOutAddr D u 0 A k = (P.1 k).1 ∧ rdOutDisp D u 0 A k = bwNum (P.1 k).2 ∧
    rdOutFar D u 0 A k = P.2.1 k ∧ rdInAddr D u 0 A k = (P.2.2.1 k).1 ∧
    rdInDisp D u 0 A k = bwNum (P.2.2.1 k).2 ∧ rdInFar D u 0 A k = P.2.2.2.1 k ∧
    ∀ lane : BitWord h, rdWidth D u 0 A (bwNum lane) k = P.2.2.2.2 k lane

/-- **C4** at the level-0 base `y`: the stored panel of `y` is the panel computed from the stored directory
(`panelOf` of `netMateD`: the directory entries of the big interval of `y`, the owners named there and their start
blocks, and the fixed local structure). -/
def C4 (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ) (y : (Fin I × Loc K h) × Bool) :
    Prop :=
  PanelStored D u (addrL y) (panelOf ha (netMateD L u) Wc Ws Wt y)

/-- Family 3 of decision D5: index `i` = a level-0 address; it passes if no base has address `i`. -/
def C4F (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ) (i : ℕ) : Prop :=
  ∀ y : (Fin I × Loc K h) × Bool, addrL y = i → C4 ha D L u Wc Ws Wt y

theorem locNum_lt (l : Loc K h) : locNum K h l < locCount K h := by
  rw [← locEquiv_val K h l]
  exact (locEquiv K h l).isLt

theorem addrL_lt (y : (Fin I × Loc K h) × Bool) : addrL y < 2 * (I * locCount K h) := by
  obtain ⟨⟨ι, l⟩, t⟩ := y
  have h1 := locNum_lt (K := K) l
  have h2 := ι.isLt
  have h3 : locNum K h l + locCount K h * (ι : ℕ) + 1 ≤ I * locCount K h := by
    calc locNum K h l + locCount K h * (ι : ℕ) + 1 ≤ locCount K h + locCount K h * (ι : ℕ) := by omega
      _ = locCount K h * ((ι : ℕ) + 1) := by ring
      _ ≤ locCount K h * I := Nat.mul_le_mul_left _ h2
      _ = I * locCount K h := Nat.mul_comm _ _
  unfold addrL
  dsimp only
  split <;> omega

theorem C4F_out (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ) {i : ℕ}
    (hi : 2 * (I * locCount K h) ≤ i) : C4F ha D L u Wc Ws Wt i := by
  intro y hy
  have := addrL_lt y
  omega

theorem C4F_iff (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ) :
    (∀ i, C4F ha D L u Wc Ws Wt i) ↔ ∀ y, C4 ha D L u Wc Ws Wt y :=
  ⟨fun hF y => hF _ y rfl, fun hC _ y _ => hC y⟩

/-- **C4 once the directory is true.** At every base, C4 holds iff the stored panel fields hold the numbers of the
TRUE panel of `y` in the level-0 state `stateNet I σ(u)` of the stored skeleton. -/
theorem C4_iff [NeZero I] (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ)
    (hDir : DirTrue L u) (y : (Fin I × Loc K h) × Bool) :
    C4 ha D L u Wc Ws Wt y ↔
      PanelStored D u (addrL y) (P1P7.panel (stateNet (K := K) I (L.sigmaS u) ha Wc Ws Wt) y) := by
  unfold C4
  rw [panelD_eq ha (L.sigmaS u) Wc Ws Wt L u hDir.2.1 hDir.2.2 y]

/-- **Stage 2 (C4) of `P1Count.stages_iff`.** Once C1-C3 pass (the directory is true), every index of family C4
passes iff every level-0 panel field of the witness holds the true panel of the stored skeleton's network. -/
theorem C4_stage [NeZero I] (D : Dims) (L : DirLayout K I (2 ^ h)) (u : List Bool) (Wc Ws Wt : ℕ)
    (hDir : DirTrue L u) :
    (∀ i, C4F ha D L u Wc Ws Wt i) ↔
      ∀ y, PanelStored D u (addrL y) (P1P7.panel (stateNet (K := K) I (L.sigmaS u) ha Wc Ws Wt) y) := by
  rw [C4F_iff]
  exact forall_congr' fun y => C4_iff ha D L u Wc Ws Wt hDir y

end P6

end P1ChkDir
