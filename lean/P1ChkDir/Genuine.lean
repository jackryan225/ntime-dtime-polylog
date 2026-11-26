import P1ChkDir.Stage
import P1Wit.Decode

/-!
# P1ChkDir.Genuine: the genuine witness of lane P6 passes the directory checks (D5 (d), `Ck_true`)

Lane P1-lean-W2-chkdir. For the P6 encoding `P1Wit.enc D m F z` whose directory fields hold the true values of a
skeleton `σ` (trits `σ`, start blocks `zigzag β`, owners `optCode`), the stored directory is TRUE and the stored
skeleton is `σ` (`dirTrue_enc`), so every index of the families C1, C2, C3 passes (`dirF_enc`). With the true least
owners in the guess section and `unownedCount = 0`, every index of family C14 passes (`C14F_enc`).
-/

namespace P1ChkDir

open P1Net P1Wit

variable {K : Type} (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D) (ρ : K ≃ Fin D.r)
  (σ : Fin (D.I * D.N) → K → Fin 3)

include hF in
/-- **The genuine directory is true.** -/
theorem dirTrue_enc (htrit : ∀ (i : Fin (D.I * D.N)) (k : K), F.trit i (ρ k) = (σ i k : ℕ))
    (hstart : ∀ (ι : Fin D.I) (k : K), F.start ι (ρ k) = zigzag (betaT D.N σ ι k))
    (hnext : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), F.nextOwn ι (ρ k) δ = ownToN (nextT D.N σ ι k δ))
    (hprev : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), F.prevOwn ι (ρ k) δ = ownToN (prevT D.N σ ι k δ)) :
    DirTrue (dirP6 D ρ) (enc D m F z) ∧ (dirP6 D ρ).sigmaS (enc D m F z) = σ := by
  have hrt : ∀ (i : Fin (D.I * D.N)) (k : K), rdTrit D (enc D m F z) i (ρ k) = (σ i k : ℕ) := fun i k => by
    rw [rdTrit_enc D m F z hF i.isLt (ρ k).isLt, htrit]
  have hσ : (dirP6 D ρ).sigmaS (enc D m F z) = σ := by
    funext i k
    simp only [dirP6_sigmaS, hrt, tritOfN_val, Option.getD_some]
  refine ⟨⟨fun i k => ?_, fun ι k => ?_, fun ι k δ => ⟨?_, ?_⟩⟩, hσ⟩
  · rw [dirP6_C1_iff, hrt]
    exact (σ i k).isLt
  · rw [dirP6_betaS, rdStart_enc D m F z hF ι.isLt (ρ k).isLt, hstart, unzigzag_zigzag, hσ]
  · rw [dirP6_nextS, rdNext_enc D m F z hF ι.isLt (ρ k).isLt δ.isLt, hnext, ownOfN_toN, hσ]
  · rw [dirP6_prevS, rdPrev_enc D m F z hF ι.isLt (ρ k).isLt δ.isLt, hprev, ownOfN_toN, hσ]

include hF in
/-- **`Ck_true` for families 0, 1, 2 (C1, C2, C3).** The genuine witness passes every index. -/
theorem dirF_enc (htrit : ∀ (i : Fin (D.I * D.N)) (k : K), F.trit i (ρ k) = (σ i k : ℕ))
    (hstart : ∀ (ι : Fin D.I) (k : K), F.start ι (ρ k) = zigzag (betaT D.N σ ι k))
    (hnext : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), F.nextOwn ι (ρ k) δ = ownToN (nextT D.N σ ι k δ))
    (hprev : ∀ (ι : Fin D.I) (k : K) (δ : Fin 3), F.prevOwn ι (ρ k) δ = ownToN (prevT D.N σ ι k δ)) :
    (∀ i, C1F D ρ (enc D m F z) i) ∧ (∀ i, C2F D ρ (enc D m F z) i) ∧ (∀ i, C3F D ρ (enc D m F z) i) :=
  (dirF_iff D ρ _).2 (dirTrue_enc D m F z hF ρ σ htrit hstart hnext hprev).1

section Challenge

open OAI.DepthThreeLowerBound

variable {M : FiniteMultiTapeMachine} {B : ℕ} [NeZero B] {g : ℕ}

/-- **`Ck_true` for family 14 (C14), Challenge input.** The genuine witness (true directory, true least owners in
the guess section) passes every index of C14 iff `unownedCount = 0`; in particular it passes when no guess cell is
unowned. -/
theorem C14F_enc (x : List Bool) (D : Dims) [NeZero (D.I * D.N)] (m : ℕ) (F : Fields) (z : List Bool)
    (hF : F.InRange D) (ρ : M.K ≃ Fin D.r) (σ : Fin (D.I * D.N) → M.K → Fin 3)
    (hP : 2 ≤ B * D.N) (hn : D.nGB = nGuessBlocks g (B * D.N))
    (htrit : ∀ (i : Fin (D.I * D.N)) (k : M.K), F.trit i (ρ k) = (σ i k : ℕ))
    (hstart : ∀ (ι : Fin D.I) (k : M.K), F.start ι (ρ k) = zigzag (betaT D.N σ ι k))
    (hnext : ∀ (ι : Fin D.I) (k : M.K) (δ : Fin 3), F.nextOwn ι (ρ k) δ = ownToN (nextT D.N σ ι k δ))
    (hprev : ∀ (ι : Fin D.I) (k : M.K) (δ : Fin 3), F.prevOwn ι (ρ k) δ = ownToN (prevT D.N σ ι k δ))
    (hguess : ∀ q : Fin D.nGB,
      F.guess q = ownToN (gOwnT (I := D.I) (guessP6 D M.inputTape fun q => ((q : ℕ) : ℤ)) D.N σ q)) :
    (∀ i, C14F D ρ M.inputTape (fun q => ((q : ℕ) : ℤ)) (enc D m F z) i) ↔
      unownedCount (B := B) (withGuessLayout (M := M) x g) σ D.N D.I = 0 := by
  obtain ⟨hDir, hσ⟩ := dirTrue_enc D m F z hF ρ σ htrit hstart hnext hprev
  rw [C14_stage (B := B) (g := g) x D hP hn ρ _ hDir, hσ]
  refine ⟨fun h => h.2, fun h => ⟨fun q => ?_, h⟩⟩
  rw [guessP6_gOwnS, rdGuess_enc D m F z hF q.isLt, hguess, ownOfN_toN]

end Challenge

section C4

open OAI.Computability.VPVNP Compression

variable {K' : Type} [Fintype K'] [DecidableEq K'] {h I a : ℕ} (ha : 4 ≤ 2 ^ a)

/-- The level-`ℓ` panel fields of the CONTENTS `F` at base address `A` are the numbers of the panel `P`. -/
def PanelFields (F : Fields) (ℓ A : ℕ)
    (P : (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) × (Fin (2 ^ a) → ℕ × BitWord h) × (Fin (2 ^ a) → ℕ) ×
      (Fin (2 ^ a) → BitWord h → ℕ)) : Prop :=
  ∀ k : Fin (2 ^ a), F.outAddr ℓ A k = (P.1 k).1 ∧ F.outDisp ℓ A k = bwNum (P.1 k).2 ∧
    F.outFar ℓ A k = P.2.1 k ∧ F.inAddr ℓ A k = (P.2.2.1 k).1 ∧
    F.inDisp ℓ A k = bwNum (P.2.2.1 k).2 ∧ F.inFar ℓ A k = P.2.2.2.1 k ∧
    ∀ lane : BitWord h, F.width ℓ A (bwNum lane) k = P.2.2.2.2 k lane

theorem bwNum_lt {g : ℕ} (w : BitWord g) : bwNum w < 2 ^ g := (bitWordFinEquiv g w).isLt

/-- **`Ck_true` for family 3 (C4).** If the P6 encoding has a true directory and its level-0 panel fields hold the
true panels of `stateNet I σ(u)` (and level 0 of `D` has room for all bases, slots and lanes), every index of C4
passes. -/
theorem C4F_enc [NeZero I] (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D)
    (L : DirLayout K' I (2 ^ h)) (Wc Ws Wt : ℕ)
    (hbases : 2 * (I * locCount K' h) ≤ (D.lv 0).bases) (hslots : 2 ^ a ≤ (D.lv 0).slots)
    (hlanes : 2 ^ h ≤ (D.lv 0).lanes) (hDir : DirTrue L (enc D m F z))
    (hpanel : ∀ y : (Fin I × Loc K' h) × Bool,
      PanelFields F 0 (addrL y) (P1P7.panel (stateNet (K := K') I (L.sigmaS (enc D m F z)) ha Wc Ws Wt) y)) :
    ∀ i, C4F ha D L (enc D m F z) Wc Ws Wt i := by
  rw [C4_stage ha D L _ Wc Ws Wt hDir]
  intro y k
  have hy : addrL y < (D.lv 0).bases := lt_of_lt_of_le (addrL_lt y) hbases
  have hk : (k : ℕ) < (D.lv 0).slots := lt_of_lt_of_le k.isLt hslots
  have h0 : (0 : ℕ) ≤ D.top := Nat.zero_le _
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hpanel y k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun lane => ?_⟩
  · rw [rdOutAddr_enc D m F z hF h0 hy hk, e1]
  · rw [rdOutDisp_enc D m F z hF h0 hy hk, e2]
  · rw [rdOutFar_enc D m F z hF h0 hy hk, e3]
  · rw [rdInAddr_enc D m F z hF h0 hy hk, e4]
  · rw [rdInDisp_enc D m F z hF h0 hy hk, e5]
  · rw [rdInFar_enc D m F z hF h0 hy hk, e6]
  · rw [rdWidth_enc D m F z hF h0 hy (lt_of_lt_of_le (bwNum_lt lane) hlanes) hk, e7 lane]

end C4

end P1ChkDir
