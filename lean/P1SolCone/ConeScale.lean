import P1SolCone.ConeTaskSupport
import P1SolCone.Wof

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code Carry
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1ChkFinal P1Int P1Int.P11 P1Wrap Module

theorem coneBin_eq_born (n : ℕ) : bin n = Carry.born n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [Carry.born0, P1ChkFinal.bin]
    | succ n =>
      rw [Carry.birth (Nat.succ_pos _), P1ChkFinal.bin,
        ih ((n+1)/2) (Nat.div_lt_self (Nat.succ_pos _) (by decide))]
      rfl

def coneQuerySize (q : Qry) : ℕ := Nat.log 2 (q.1.length + 1) + q.2.2.length + 1

theorem coneQuerySize_pos (q : Qry) : 1 ≤ coneQuerySize q := by unfold coneQuerySize; omega

def smallQuery (q : Qry) : List Bool × List Bool × List Bool :=
  (bin q.1.length, bin q.2.1.length, q.2.2)

theorem smallQuery_size (q : Qry) :
    size (smallQuery q) ≤ 2 * coneQuerySize q + size (Carry.born q.2.1.length) + 4 := by
  have hn : (bin q.1.length).length ≤ Nat.log 2 (q.1.length + 1) + 1 :=
    length_bin_le _ _ (lt_of_le_of_lt (Nat.le_succ _) (Nat.lt_pow_succ_log_self (by decide) _))
  unfold smallQuery
  simp only [size_prod]
  rw [coneBin_eq_born q.2.1.length]
  rw [P1ChkFinal.size_listBool (bin q.1.length), P1ChkFinal.size_listBool q.2.2]
  unfold coneQuerySize
  omega

section Concrete

variable {k : Type} [Field k] {S : BlockSchedule k} (Bt : S.Templates) (V : C1Challenge.Machine) (a b : ℕ)

noncomputable def coneScan (q : Qry) : ℕ :=
  ((S.steps + 1) * Params.T (portConsts Bt) (lpTime a b q.1.length) + 1) *
    (q.1.length + q.2.1.length + q.2.2.length + 1)

noncomputable def pureConeScale (q : Qry) : ℕ :=
  2 ^ (Bt.growthConstant * Mbar Bt V a b q.1.length) * coneQuerySize q

noncomputable def coneScale (q : Qry) : ℕ := pureConeScale Bt V a b q + size (Carry.born q.2.1.length)

theorem smallQuery_dom : Dom (coneScale Bt V a b) (fun q => size (smallQuery q)) := by
  refine ⟨1, 4, fun q => ?_⟩
  have hp : coneQuerySize q ≤ pureConeScale Bt V a b q :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hs := smallQuery_size q
  simp only [coneScale, pow_one]
  omega

theorem coneScale_padSize : Dom (coneScale Bt V a b)
    (fun q => size (conePad Bt.growthConstant (Mbar Bt V a b q.1.length))) := by
  let scale (q : Qry) := 2 ^ (Bt.growthConstant * Mbar Bt V a b q.1.length)
  have h : Dom (coneScale Bt V a b) scale := (Dom.base _).mono (fun q => by
    unfold coneScale pureConeScale
    exact (Nat.le_mul_of_pos_right _ (coneQuerySize_pos q)).trans (Nat.le_add_right _ _))
  have hpad := (conePad_dom Bt.growthConstant (fun q : Qry => Mbar Bt V a b q.1.length)
    (fun q => Mbar_pos Bt V a b q.1.length)).sub h
  exact (((Dom.const _ 2).mul hpad).add (Dom.const _ 1)).mono (fun q => by rw [size_tally])

/-- Convert the composed task on raw queries to all query domains with one exponent. -/
theorem coneTask_interface {F : Type} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ}
    (bs : Basis (Fin Dd) (ZMod 2) F) (w : List Bool → List Bool → ℕ → F)
    (cost : Qry → ℕ) (hcost : Dom (coneScale Bt V a b) cost)
    (run : Task (fun q => coneScan Bt a b q + cost q) (fun q => send q)
      (fun q => send (coords bs (w q.1 q.2.1 (P1Batch.bval q.2.2))))) :
    ∃ c : ℕ, ∀ M K : ℕ → ℕ, WHyp bs w M K (P1SolCone.βW Bt V a b c) := by
  have hscan (q : Qry) : q.2.1.length + 1 ≤ coneScan Bt a b q := by
    unfold coneScan
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    omega
  obtain ⟨tail, htail, go⟩ := witnessMetadata_task _ _ (coneScan Bt a b)
    (fun q : Qry => q.2.1.length) (pureConeScale Bt V a b) cost hscan hcost run
  obtain ⟨c,_,final⟩ := d14_task _ _ (coneScan Bt a b)
    (fun q : Qry => Bt.growthConstant * Mbar Bt V a b q.1.length)
    coneQuerySize tail coneQuerySize_pos htail go
  refine ⟨c, fun M K => ?_⟩
  unfold WHyp
  refine (final.on (fun p : QDom M K => p.val)).conform (fun p => ?_) (fun _ => rfl) (fun _ => rfl)
  simp only [P1SolCone.βW, coneQuerySize, coneScan, Nat.mul_assoc]

end Concrete

end P1SolCone.SolCone
