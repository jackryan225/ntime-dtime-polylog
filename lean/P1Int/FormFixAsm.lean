import P1Int.FormGroups
import P1Int.FormDir
import P1Int.FormLev
import P1Int.FormC11

noncomputable section

namespace P1Int.P11.SolFormFix

open P1Wit

private theorem sections_except_chain (D : Dims) (Q : ℕ → Prop)
    (hTrit : Q secTrit) (hStart : Q secStart) (hPrev : Q secPrev)
    (hNext : Q secNext) (hGuess : Q secGuess)
    (hLevel : ∀ lv < D.top + 1, ∀ kk : Mem, Q (secLev lv kk))
    (hOmega : Q D.secOmega) :
    ∀ s < D.nSec, s ≠ D.secChain → Q s := by
  intro s hs hChain
  by_cases hSmall : s < 5
  · have h : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact hTrit
    · exact hStart
    · exact hPrev
    · exact hNext
    · exact hGuess
  by_cases hBelow : s < D.secOmega
  · change s < 5 + 12 * (D.top + 1) at hBelow
    have hLv : (s - 5) / 12 < D.top + 1 := by omega
    have hCode : (s - 5) % 12 < 12 := Nat.mod_lt _ (by decide)
    have hSec : secLev ((s - 5) / 12) (Mem.ofCode ((s - 5) % 12)) = s := by
      rw [secLev, Mem.toNat_ofNat _ hCode]
      omega
    exact Eq.subst (motive := Q) hSec (hLevel _ hLv _)
  · change s < 7 + 12 * (D.top + 1) at hs
    change s ≠ 6 + 12 * (D.top + 1) at hChain
    change ¬ s < 5 + 12 * (D.top + 1) at hBelow
    have hSec : D.secOmega = s := by
      change 5 + 12 * (D.top + 1) = s
      omega
    exact Eq.subst (motive := Q) hSec hOmega

end P1Int.P11.SolFormFix

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
theorem P1Int.P11.formFix_asm {k : Type*} [Field k] {S : BlockSchedule k} (Bt : S.Templates) {F : Type} [CommRing F]
    [Algebra (ZMod 2) F] (κ : Bt.Entry → F) (hκ : Bt.IsSolution κ) (V : C1Challenge.Machine) (a b : ℕ)
    (x : List Bool) (d bigBias termBias : ℕ) (H : P1Int.P11.FixedRecords Bt κ hκ V a b x d bigBias termBias) :
    P1Int.P11.FormFixAsmTarget Bt κ hκ V a b x d bigBias termBias H := by
  intro hC14Fix bs l Wof cnt u hu
  let D := fixedDims Bt V a b x d bigBias termBias
  let G := fixedGroups Bt κ hκ V a b x d bigBias termBias H bs l Wof
  change ∀ j < 7 + 2 * D.top, G.P D.top j u at hu
  have hDir : G.dir u := Eq.mp (G.P_one D.top u) (hu 1 (by omega))
  have hC14 : G.c14 u := Eq.mp (G.P_two D.top u) (hu 2 (by omega))
  have hC11 : G.c11 u := Eq.mp (G.P_c11 D.top u) (hu (4 + 2 * D.top) (by omega))
  have hTuple : ∃ t : (fixedCD Bt κ hκ V a b x).Tup d,
      SecEq Bt κ hκ V a b x d bigBias termBias H u t P1Wit.secTrit ∧
      LevUpTo Bt κ hκ V a b x d bigBias termBias H u t D.top ∧
      ∀ kk : P1Wit.Mem, panelKind kk = true →
        SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev D.top kk) := by
    by_cases hTop : D.top = 0
    · have hC4 : G.c4 u := Eq.mp (G.P_three D.top u) (hu 3 (by omega))
      exact Exists.elim hC4 fun t ht =>
        ⟨t, ht.1, fun lv hLv _ => False.elim (Nat.not_lt_zero lv (hTop ▸ hLv)),
          fun kk hPanel =>
            Eq.subst (motive := fun lv =>
              SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev lv kk))
              hTop.symm (ht.2 kk hPanel)⟩
    · have hPrev : D.top - 1 < D.top := by omega
      have hSucc : D.top - 1 + 1 = D.top := by omega
      have hC10 : G.c10 (D.top - 1) u :=
        Eq.mp (G.P_c10 hPrev u) (hu (5 + 2 * (D.top - 1)) (by omega))
      exact Exists.elim hC10 fun t ht =>
        ⟨t, ht.1,
          Eq.subst (motive := LevUpTo Bt κ hκ V a b x d bigBias termBias H u t) hSucc ht.2.1,
          fun kk hPanel =>
            Eq.subst (motive := fun lv =>
              SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev lv kk))
              hSucc (ht.2.2 kk hPanel)⟩
  exact Exists.elim hTuple fun t ht => by
    have hLevel : LevUpTo Bt κ hκ V a b x d bigBias termBias H u t (D.top + 1) := by
      intro lv hLv kk
      by_cases hEarlier : lv < D.top
      · exact ht.2.1 lv hEarlier kk
      have hLast : D.top = lv := by omega
      have hTop : SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev D.top kk) := by
        cases hPanel : panelKind kk with
        | true => exact ht.2.2 kk hPanel
        | false =>
            intro i hi
            have hCount : D.count (P1Wit.secLev D.top kk) = 0 :=
              finalPanelOnly Bt V a b x d bigBias termBias kk hPanel
            exact False.elim (Nat.not_lt_zero i (hCount ▸ hi))
      exact Eq.subst (motive := fun lv =>
        SecEq Bt κ hκ V a b x d bigBias termBias H u t (P1Wit.secLev lv kk)) hLast hTop
    have hDirectory := dir_fix Bt κ hκ V a b x d bigBias termBias H u t hDir ht.1
    exact ⟨t, SolFormFix.sections_except_chain D (SecEq Bt κ hκ V a b x d bigBias termBias H u t)
      ht.1 hDirectory.1 hDirectory.2.1 hDirectory.2.2
      (hC14Fix u t hDir hC14 ht.1) hLevel
      (c11_fix Bt κ hκ V a b x d bigBias termBias H u t hLevel hC11)⟩

#print axioms P1Int.P11.formFix_asm
