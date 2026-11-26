import P1SolF0R.RouteRead
import P1SolF0R.WitnessRead

namespace P1SolF0R.SolReader

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Net P1Wit P1ChkFinal.AstraC10

def smallAt {I h : ℕ} (i : Fin I) (j : Fin (2 ^ h)) : Fin (I * 2 ^ h) :=
  ⟨i.val * 2 ^ h + j.val, calc
    _ < i.val * 2 ^ h + 2 ^ h := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * 2 ^ h := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ I * 2 ^ h := Nat.mul_le_mul_right _ i.isLt⟩

structure ChunkFacts {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (σ : Fin (I * 2 ^ h) → K → Fin 3)
    (i : Fin I) (tape : K → ℕ) (w : ℕ) (fields : IntervalChunk) : Prop where
  trit : ∀ (j : Fin (2 ^ h)) (k : K),
    tritInChunk (Fintype.card K) (fields.1, j.val, tape k) = (σ (smallAt i j) k).val
  start : ∀ k,
    startInChunk (fields.2.1, w, tape k) = zigzag (betaOf σ k (i.val * 2 ^ h))
  prev : ∀ (k : K) (δ : Fin 3),
    ownerInChunk (fields.2.2.1, w, tape k, δ.val) =
      P1ChkDir.ownToN (prevOwner I σ k i (portQ I σ k i δ))
  next : ∀ (k : K) (δ : Fin 3),
    ownerInChunk (fields.2.2.2, w, tape k, δ.val) =
      P1ChkDir.ownToN (nextOwner I σ k i (portQ I σ k i δ))
  centers : ∀ k,
    chunkCenters (Fintype.card K) (tally (2 ^ h), fields, w, tape k) = trueCenters σ i k

theorem chunkFacts_of_directory {K : Type} [Fintype K] [DecidableEq K] {I h : ℕ}
    (D : Dims) (u : List Bool) (σ : Fin (I * 2 ^ h) → K → Fin 3) (i : Fin I) (tape : K → ℕ)
    (hN : D.N = 2 ^ h) (hr : D.r = Fintype.card K) (ht : ∀ k, tape k < D.r)
    (htrit : ∀ (j : Fin (I * 2 ^ h)) (k : K), rdTrit D u j (tape k) = (σ j k).val)
    (hstart : ∀ k, rdStart D u i (tape k) = zigzag (betaOf σ k (i.val * 2 ^ h)))
    (hprev : ∀ (k : K) (δ : Fin 3), rdPrev D u i (tape k) δ =
      P1ChkDir.ownToN (prevOwner I σ k i (portQ I σ k i δ)))
    (hnext : ∀ (k : K) (δ : Fin 3), rdNext D u i (tape k) δ =
      P1ChkDir.ownToN (nextOwner I σ k i (portQ I σ k i δ))) :
    ChunkFacts σ i tape D.bigW (witnessChunk D u i.val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j k
    rw [← hr, tritInChunk_eq D u i j (tape k) (by rw [hN]; exact j.isLt) (ht k), hN]
    exact htrit (smallAt i j) k
  · intro k
    exact (startInChunk_eq D u i (tape k) (ht k)).trans (hstart k)
  · intro k δ
    exact (prevInChunk_eq D u i (tape k) δ (ht k) δ.isLt).trans (hprev k δ)
  · intro k δ
    exact (nextInChunk_eq D u i (tape k) δ (ht k) δ.isLt).trans (hnext k δ)
  · intro k
    rw [← hr]
    apply chunkCenters_eq D u σ i k (tape k) hN (ht k) _ (hstart k)
    intro j
    rw [show i.val * 2 ^ h + j.val = (smallAt i j).val from rfl, htrit (smallAt i j) k]
    simp only [intervalMoves, readAt_ofFn, smallAt]

open P1Int P1Int.P11 P1Wit.SolWitfill in
/-- Package the decoded fields while the directory dimensions are abstract. -/
theorem chunks_of_records {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates)
    {F : Type} [CommRing F] [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ)
    (V : C1Challenge.Machine) (a : ℕ) (x : List Bool) (B I : ℕ) [NeZero B] [NeZero I]
    {h : ℕ} (T : ℕ) (hn : T * S.laneBits ≤ h) {D : Dims} {d : ℕ}
    (H : NetRecordInputs Bt κ hκ V B I T hn D d) (tape : (toOAI V).K → ℕ)
    (hTape : ∀ j, (H.tape_order j).val = tape j)
    (q : (netData Bt κ hκ V a x B I (h := h) T hn (netSiteOrder Bt κ hκ V B I (h := h) T hn)).toCountData.Tup d)
    (m : ℕ)
    (hm : D.fixedLen + (tuplePayload (p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H) q).length ≤ m)
    (hr : D.r = Fintype.card (toOAI V).K) :
    let u := List.ofFn (encTuple (p11TupleRecords Bt κ hκ V a x B I (h := h) T hn H) m q)
    ∀ i : Fin I, ChunkFacts q.1 i tape D.bigW (witnessChunk D u i.val) := by
  dsimp only
  obtain ⟨hmoves, hstart, hprev, hnext⟩ := genuine_directory Bt κ hκ V a x B I T hn H tape hTape q m hm
  have ht (j : (toOAI V).K) : tape j < D.r := by
    rw [← hTape]
    exact (H.tape_order j).isLt
  intro i
  exact chunkFacts_of_directory D _ q.1 i tape H.initial_lanes hr ht hmoves (hstart i) (hprev i) (hnext i)

end P1SolF0R.SolReader

#print axioms P1SolF0R.SolReader.chunkFacts_of_directory
#print axioms P1SolF0R.SolReader.chunks_of_records
