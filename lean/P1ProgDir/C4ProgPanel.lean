import P1ProgDir.C4ProgLogic

namespace P1ProgDir.SolC4

open P1Net P1ChkDir P1Wit
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {I h a : ℕ}

/-- The lane-independent numeric row of a level-zero slot. -/
def slotFields (D : Dims) (i j target disp far width lanes : ℕ) : List (ℕ × ℕ × ℕ) :=
  let k := i * (D.lv 0).slots + j
  [(secLev 0 .outAddr, k, target), (secLev 0 .outDisp, k, disp), (secLev 0 .outFar, k, far),
   (secLev 0 .inAddr, k, target), (secLev 0 .inDisp, k, disp), (secLev 0 .inFar, k, far)] ++
  (List.range lanes).map fun lane =>
    (secLev 0 .width, (i * (D.lv 0).lanes + lane) * (D.lv 0).slots + j, width)

theorem slotFields_iff (D : Dims) (u : List Bool) (i j target disp far width lanes : ℕ) :
    (∀ p ∈ slotFields D i j target disp far width lanes, readField D u p.1 p.2.1 = p.2.2) ↔
      rdOutAddr D u 0 i j = target ∧ rdOutDisp D u 0 i j = disp ∧ rdOutFar D u 0 i j = far ∧
      rdInAddr D u 0 i j = target ∧ rdInDisp D u 0 i j = disp ∧ rdInFar D u 0 i j = far ∧
      ∀ lane < lanes, rdWidth D u 0 i lane j = width := by
  simp only [slotFields, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, and_true, List.forall_mem_map, List.mem_range, rdOutAddr, rdOutDisp, rdOutFar, rdInAddr,
    rdInDisp, rdInFar, rdWidth, and_assoc]

/-- Reconstruct the expected record from the mates at the queried base. -/
noncomputable def fieldsAt (ha : 4 ≤ 2 ^ a) (D : Dims)
    (mate : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (Wc Ws Wt : ℕ) (y : (Fin I × Loc K h) × Bool) : List (ℕ × ℕ × ℕ) :=
  (List.finRange (2 ^ a)).flatMap fun (k : Fin (2 ^ a)) =>
    slotFields D (addrL y) (k : ℕ) (addrL (tgtOf ha mate y k).1) (bwNum (dispOf mate y k))
      (tgtOf ha mate y k).2 (widthOf mate Wc Ws Wt y k 0) (2 ^ h)

theorem widthOf_independent
    (mate : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (Wc Ws Wt : ℕ) (y : (Fin I × Loc K h) × Bool) (k : Fin (2 ^ a)) (lane : BitWord h) :
    widthOf mate Wc Ws Wt y k lane = widthOf mate Wc Ws Wt y k 0 := rfl

theorem fieldsAt_iff (ha : 4 ≤ 2 ^ a) (D : Dims) (u : List Bool)
    (mate : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (Wc Ws Wt : ℕ) (y : (Fin I × Loc K h) × Bool) :
    (∀ p ∈ fieldsAt ha D mate Wc Ws Wt y, readField D u p.1 p.2.1 = p.2.2) ↔
      PanelStored D u (addrL y) (panelOf ha mate Wc Ws Wt y) := by
  simp only [fieldsAt, List.forall_mem_flatMap, List.mem_finRange, true_implies, slotFields_iff,
    PanelStored, panelOf, widthOf_independent, storedWidths_iff (h := h)]

/-- Read a start block using P6's tape numbering, even when the directory layout
has been transported along the equality of lane counts. -/
theorem p6_cast_beta {D : Dims} (ρ : K ≃ Fin D.r) {N : ℕ} (hn : D.N = N)
    (u : List Bool) (ι : Fin D.I) (k : K) :
    (hn ▸ dirP6 D ρ : DirLayout K D.I N).betaS u ι k =
      some (unzigzag (rdStart D u ι (ρ k))) := by
  subst N
  exact dirP6_betaS D ρ u ι k

theorem p6_cast_owner {D : Dims} (ρ : K ≃ Fin D.r) {N : ℕ} (hn : D.N = N)
    (u : List Bool) (ι : Fin D.I) (k : K) (δ : Fin 3) (nxt : Bool) :
    (if nxt then (hn ▸ dirP6 D ρ : DirLayout K D.I N).nextS u ι k δ
     else (hn ▸ dirP6 D ρ : DirLayout K D.I N).prevS u ι k δ) =
      ownOfN D.I (if nxt then rdNext D u ι (ρ k) δ else rdPrev D u ι (ρ k) δ) := by
  subst N
  cases nxt
  · exact dirP6_prevS D ρ u ι k δ
  · exact dirP6_nextS D ρ u ι k δ

end P1ProgDir.SolC4
