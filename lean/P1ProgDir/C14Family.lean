import P1ChkDir.Stage
import P1ProgDir.Readbacks
import P1ProgDir.C14Reply

namespace P1ProgDir.SolC14Family

open P1ChkDir P1Wit P1ProgDir.SolReadbacks
open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits
open P1ProgDir.SolSigned P1ProgDir.SolC14Reply

theorem c14_family_readback {K : Type} (D : Dims) (tape : K ≃ Fin D.r)
    (kIn : K) (blk : Fin D.nGB → ℤ) (u : List Bool) (q : Fin D.nGB) :
    C14F D tape kIn blk u q ↔
      let owner := rdGuess D u q
      let delta := guessDelta D (tape kIn) u (blk q) owner
      0 < owner ∧ owner ≤ D.I ∧ 0 ≤ delta ∧ delta < 3 ∧
        rdPrev D u (owner - 1) (tape kIn) delta.toNat = 0 := by
  have hf : C14F D tape kIn blk u q ↔
      C14 (dirP6 D tape) (guessP6 D kIn blk) u q :=
    ⟨fun h => h q.isLt, fun h _ => h⟩
  exact hf.trans (c14_bounded_readback D tape u kIn blk q)

theorem in_range {K : Type} (D : Dims) (tape : K ≃ Fin D.r)
    (kIn : K) (u : List Bool) (q : Fin D.nGB)
    (Q beta prev₀ prev₁ prev₂ : Word)
    (hq : signedValue Q = ((q : ℕ) : ℤ))
    (hlo : 0 < rdGuess D u q) (hhi : rdGuess D u q ≤ D.I)
    (hb : signedValue beta = bigOf D.N
        (unzigzag (rdStart D u (rdGuess D u q - 1) (tape kIn))))
    (hp₀ : value prev₀ = rdPrev D u (rdGuess D u q - 1) (tape kIn) 0)
    (hp₁ : value prev₁ = rdPrev D u (rdGuess D u q - 1) (tape kIn) 1)
    (hp₂ : value prev₂ = rdPrev D u (rdGuess D u q - 1) (tape kIn) 2) :
    windowTest (Q, beta, prev₀, prev₁, prev₂) = true ↔
      C14F D tape kIn (fun j => ((j : ℕ) : ℤ)) u q := by
  rw [windowTest_eq, c14_family_readback]
  simp only [hq, hlo, hhi, true_and, guessDelta, ← hb]
  let d := ((q : ℕ) : ℤ) - signedValue beta + 1
  change (∃ δ : Fin 3, ((q : ℕ) : ℤ) = signedValue beta - 1 + (δ : ℤ) ∧
      value (if δ.val = 0 then prev₀ else if δ.val = 1 then prev₁ else prev₂) = 0) ↔
    0 ≤ d ∧ d < 3 ∧ rdPrev D u (rdGuess D u q - 1) (tape kIn) d.toNat = 0
  have hprev (δ : Fin 3) :
      value (if δ.val = 0 then prev₀ else if δ.val = 1 then prev₁ else prev₂) =
        rdPrev D u (rdGuess D u q - 1) (tape kIn) δ := by
    fin_cases δ
    · exact hp₀
    · exact hp₁
    · exact hp₂
  simp only [hprev]
  constructor
  · rintro ⟨δ, he, hp⟩
    have hd : d = (δ : ℤ) := by unfold d; omega
    rw [hd]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast δ.isLt, by simpa only [Int.toNat_natCast] using hp⟩
  · rintro ⟨h₀, h₃, hp⟩
    have hd : (d.toNat : ℤ) = d := Int.toNat_of_nonneg h₀
    let δ : Fin 3 := ⟨d.toNat, by exact_mod_cast (hd.trans_lt h₃)⟩
    refine ⟨δ, ?_, hp⟩
    change ((q : ℕ) : ℤ) = signedValue beta - 1 + (d.toNat : ℤ)
    rw [hd]
    unfold d
    omega

end P1ProgDir.SolC14Family
