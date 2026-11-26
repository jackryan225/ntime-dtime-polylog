import P1ProgDir.C1Batch
import P1ProgDir.Geometry
import P1ProgDir.Readbacks

namespace P1ProgDir.SolC1

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open OAI.Computability.IntegerMultiplication.Bits OAI.Computability.IntegerMultiplication.Carry
open P1ChkDir P1Wit
open P1ProgDir.SolGeometry P1ProgDir.SolReadbacks P1ProgDir.SolC1Batch

set_option maxHeartbeats 1500000

def capFrame (a b aM r : ℕ) (p : Word × Word) : Word × Word :=
  (tritCountWord a b aM r p.1, p.2)

theorem poly_capFrame (a b aM r : ℕ) : Poly (capFrame a b aM r) :=
  (Poly.identity.fstCompose.compose (poly_tritCountWord a b aM r)).pair Poly.identity.sndCompose

open Classical in
theorem c1_task_polynomial {X K : Type} (raw : X → List Bool × List Bool × List Bool)
    (a b aM r : ℕ) (D : ℕ → Dims) (tape : ∀ n, K ≃ Fin (D n).r)
    (hd : ∀ x : X, let n := (raw x).1.length
      (D n).I * (D n).N * (D n).r = bigCount a b aM n * laneCount a b n * r)
    (hfit : ∀ x : X, let d := D (raw x).1.length
      2 * (d.I * d.N * d.r) ≤ (raw x).2.1.length) :
    ∃ β : X → ℕ, Dom (fun x => size (lengthHeader (raw x)).1) β ∧
      Task (fun x => size (raw x) + (raw x).2.1.length + β x) (fun x => send (raw x))
        (fun x => send (decide (C1F (D (raw x).1.length) (tape (raw x).1.length)
          (raw x).2.1 (P1Batch.bval (raw x).2.2)))) := by
  let hdr (x : X) := (lengthHeader (raw x)).1
  let w (x : X) := (raw x).2.1
  let frame (x : X) := capFrame a b aM r (hdr x)
  have hcap (x : X) : value (frame x).1 =
      (D (raw x).1.length).I * (D (raw x).1.length).N * (D (raw x).1.length).r := by
    change value (tritCountWord a b aM r (born (raw x).1.length)) = _
    rw [tritCountWord_value, birthValue]
    exact (hd x).symm
  let p (x : X) : ValidInput := ⟨(frame x, w x), by
    change 2 * value (frame x).1 ≤ (w x).length
    rw [hcap]
    exact hfit x⟩
  obtain ⟨t₁, ht₁, h₁⟩ := poly_capFrame a b aM r
  obtain ⟨t₂, ht₂, h₂⟩ := SolC1Batch.task
  let β (x : X) := t₁ (hdr x) + t₂ (frame x)
  have hdom : Dom (fun x => size (hdr x)) β :=
    (ht₁.map hdr).add (((ht₂.map (capFrame a b aM r)).sub
      (poly_capFrame a b aM r).length).map hdr)
  have hs (x : X) : reply (p x).val =
      decide (C1F (D (raw x).1.length) (tape (raw x).1.length)
        (w x) (P1Batch.bval (raw x).2.2)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, reply_iff, c1_readback]
    change value (frame x).1 ≤ value (frame x).2 ∨
      bitsVal (((w x).drop (2 * value (frame x).2)).take 2) < 3 ↔ _
    rw [hcap, P1Batch.bval_eq_value]
    have ho : (D (raw x).1.length).off secTrit = 0 := rfl
    simp only [readField, readNat, width_trit, ho, Nat.zero_add]
    change _ ∨ bitsVal (((w x).drop (2 * value (raw x).2.2)).take 2) < 3 ↔
      _ ∨ bitsVal (((w x).drop (value (raw x).2.2 * 2)).take 2) < 3
    have hselector : (frame x).2 = (raw x).2.2 := rfl
    rw [Nat.mul_comm 2, hselector]
  refine ⟨β, hdom, ?_⟩
  have hdata := (h₁.on hdr).left (fun x => send (w x))
  have htotal := ((easy_lengthHeader.on raw).compose hdata).compose (h₂.on p)
  refine htotal.conform (fun x => ?_) (fun _ => rfl) (fun x => congrArg send (hs x))
  change size (raw x) + t₁ (hdr x) + ((w x).length + t₂ (frame x)) = _
  unfold β w
  omega

end P1ProgDir.SolC1
