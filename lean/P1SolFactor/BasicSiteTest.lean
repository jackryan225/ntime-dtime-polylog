import P1SolFactor.SiteHeader
import P1SolFactor.SiteDispatch
import P1SolFactor.Decision
import P1SolFactor.FieldCleanup

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.IntegerMultiplication
open P1ProgEng SolRows
open scoped Classical

noncomputable section

variable {R : Type} {V : FiniteMultiTapeMachine}

def IsBasicRule : SiteRule V → Prop
  | .free | .copy .. | .fixed .. => True
  | _ => False

def inFieldReg (a : ℕ) (i : Fin 4) : ℕ := fieldReg (2 ^ a + i.val)

def outFieldReg (o : Fin 4) : ℕ := fieldReg o.val

def basicRegOK (a : ℕ) (r : Reg (P1P5.EvalSym R)) : SiteRule V → Prop
  | .free => True
  | .copy o i => paddedAgree decodeInputBit (r (inFieldReg a i)) (r (outFieldReg o))
  | .fixed word => paddedAgree decodeInputBit (r (outFieldReg 0)) (word.map inputBit)
  | _ => False

private def copyPorts (a : ℕ) (ha : 4 ≤ 2 ^ a) (o i : Fin 4) : Ports where
  table := inFieldReg a i
  output := 7
  index := outFieldReg o
  table_ne_output := by
    have h : 8 ≤ inFieldReg a i := Nat.le_add_right _ _
    omega
  table_ne_index := by
    have h := (o.isLt.trans_le ha).trans_le (Nat.le_add_right (2 ^ a) i.val)
    exact fun he => (Nat.ne_of_lt (Nat.add_lt_add_left h 8)) he.symm
  output_ne_index := by
    have h : 8 ≤ outFieldReg o := Nat.le_add_right _ _
    omega

private def fieldSlot (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

private theorem fieldSlot_val (s : Fin 4) : fieldSlot s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

private def compareCopy (a : ℕ) (ha : 4 ≤ 2 ^ a) (o i : ℕ) : Prog (P1P5.EvalSym R) :=
  comparePadded (copyPorts a ha (fieldSlot o) (fieldSlot i)) decodeInputBit (inputBit true) (inputBit false)

private def readCopyBody (a : ℕ) (ha : 4 ≤ 2 ^ a) : Prog (P1P5.EvalSym R) :=
  readSmallPtr 6 3 fun o => readSmallPtr 6 3 (compareCopy a ha o)

private theorem readCopyBody_runs {Γ : Scope (P1P5.EvalSym R)} (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (r : Reg (P1P5.EvalSym R)) (o i : Fin 4) (W : ℕ) (h6 : r 6 = [])
    (hi : (r (inFieldReg a i)).length ≤ W) (ho : (r (outFieldReg o)).length ≤ W) :
    Runs Γ (readCopyBody a ha) (Function.update r 6 (P1P5.encPtr o.val ++ P1P5.encPtr i.val))
      (putDecision 7 r (basicRegOK a r (.copy o i : SiteRule V))) (32 * W + 49) := by
  let mid := Function.update r 6 (P1P5.encPtr (R := R) i.val)
  let ok := basicRegOK a r (.copy o i : SiteRule V)
  have hback : Function.update mid 6 [] = r := by
    simp only [mid, Function.update_idem, ← h6, Function.update_eq_self]
  have htest : Runs Γ (compareCopy a ha o.val i.val) (Function.update mid 6 []) (putDecision 7 r ok)
      (32 * W + 17) := by
    rw [hback]
    have h := compareDecision_runs (Γ := Γ) (copyPorts a ha o i) r
    unfold compareCopy
    rw [fieldSlot_val, fieldSlot_val]
    exact h.mono (by dsimp only [copyPorts]; omega)
  have hm : mid 6 = P1P5.encPtr i.val ++ [] := by simp only [mid, Function.update_self, List.append_nil]
  have hread := readSmallPtr_runs 6 3 i.val (by omega : i.val ≤ 3) (compareCopy a ha o.val) [] hm htest
  have htotal := readSmallPtr_runs 6 3 o.val (by omega : o.val ≤ 3)
    (fun n => readSmallPtr 6 3 (compareCopy a ha n)) (P1P5.encPtr i.val)
    (Function.update_self 6 _ r) (by simpa only [mid, Function.update_idem] using hread)
  exact htotal.mono (by have := o.isLt; have := i.isLt; omega)

private def fixedPorts : Ports := ⟨outFieldReg 0, 7, 6, by decide, by decide, by decide⟩

private def readFixedBody : Prog (P1P5.EvalSym R) :=
  .join (comparePadded fixedPorts decodeInputBit (inputBit true) (inputBit false))
    (SolOrbit.clearTo 6 (fun _ => false))

private theorem readFixedBody_runs {Γ : Scope (P1P5.EvalSym R)} (a : ℕ) (r : Reg (P1P5.EvalSym R))
    (word : List Bool) (W : ℕ) (h6 : r 6 = []) (hword : word.length ≤ W)
    (hout : (r (outFieldReg 0)).length ≤ W) :
    Runs Γ readFixedBody (Function.update r 6 (word.map inputBit))
      (putDecision 7 r (basicRegOK a r (.fixed word : SiteRule V))) (39 * W + 23) := by
  let mid := Function.update r 6 (word.map inputBit)
  let ok := basicRegOK a r (.fixed word : SiteRule V)
  have htest := compareDecision_runs (Γ := Γ) fixedPorts mid
  have hm : mid 6 = word.map inputBit := Function.update_self 6 _ _
  have ho : mid (outFieldReg 0) = r (outFieldReg 0) := Function.update_of_ne (by decide) ..
  dsimp only [fixedPorts] at htest
  rw [hm, ho, List.length_map] at htest
  have hclear := SolOrbit.clearAll_runs (Γ := Γ) (r := putDecision 7 mid ok) 6
  have hlen : ((putDecision 7 mid ok) 6).length = word.length := by
    rw [putDecision, Function.update_of_ne (by decide : (6 : ℕ) ≠ 7), hm, List.length_map]
  have hback : Function.update (putDecision 7 mid ok) 6 [] = putDecision 7 r ok := by
    simp only [putDecision, mid, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6)]
    rw [Function.update_comm (by decide : (7 : ℕ) ≠ 6), Function.update_idem, ← h6, Function.update_eq_self]
  rw [hlen, hback] at hclear
  exact (htest.join hclear).mono (by omega)

/-- Interpret the free, copy, and fixed-word payloads of a site header. -/
def basicBranch (a : ℕ) (ha : 4 ≤ 2 ^ a) : ℕ → Prog (P1P5.EvalSym R)
  | 0 => .push 7 (inputBit true)
  | 4 => readCopyBody a ha
  | 6 => readFixedBody
  | _ => .pass

def runBasicHeader (a : ℕ) (ha : 4 ≤ 2 ^ a) : Prog (P1P5.EvalSym R) :=
  readSiteHeader (basicBranch a ha)

theorem runBasicHeader_runs {Γ : Scope (P1P5.EvalSym R)} (a : ℕ) (ha : 4 ≤ 2 ^ a)
    (r : Reg (P1P5.EvalSym R)) (rule : SiteRule V) (W : ℕ)
    (hbasic : IsBasicRule rule) (h6 : r 6 = []) (hheader : r 2 = encRule V rule)
    (hin : ∀ i, (r (inFieldReg a i)).length ≤ W) (hout : ∀ o, (r (outFieldReg o)).length ≤ W)
    (hfixed : ∀ word, rule = .fixed word → word.length ≤ W) :
    Runs Γ (runBasicHeader a ha) r (putDecision 7 r (basicRegOK a r rule)) (51 * W + 230) := by
  cases rule with
  | free =>
    have hh : r 2 = P1P5.encPtr 0 ++ [] := hheader.trans (by simp [encRule]; rfl)
    have hpush : Runs Γ (basicBranch a ha 0) (Function.update r 6 []) (putDecision 7 r True) 1 := by
      rw [← h6, Function.update_eq_self]
      simpa only [basicBranch, putDecision, decide_true] using
        (Runs.push (Γ := Γ) (r := r) 7 (inputBit true))
    have h := readSiteHeader_runs (basicBranch a ha) 0 [] (by decide) h6 hh hpush
    have hlen : (r 2).length = 1 := by rw [hh]; rfl
    exact h.mono (by rw [hlen]; omega)
  | copy o i =>
    have hh : r 2 = P1P5.encPtr 4 ++ (P1P5.encPtr o.val ++ P1P5.encPtr i.val) := hheader.trans (by rfl)
    have hc := readCopyBody_runs (Γ := Γ) (V := V) a ha r o i W h6 (hin i) (hout o)
    have h := readSiteHeader_runs (basicBranch a ha) 4 _ (by decide) h6 hh hc
    have hlen : (r 2).length ≤ 13 := by
      rw [hh]
      simp only [P1P5.encPtr, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      have := o.isLt
      have := i.isLt
      omega
    exact h.mono (by omega)
  | fixed word =>
    have hh : r 2 = P1P5.encPtr 6 ++ word.map inputBit := hheader.trans (by rfl)
    have hW := hfixed word rfl
    have hc := readFixedBody_runs (Γ := Γ) (V := V) a r word W h6 hW (hout 0)
    have h := readSiteHeader_runs (basicBranch a ha) 6 _ (by decide) h6 hh hc
    have hlen : (r 2).length ≤ W + 7 := by
      rw [hh]
      simp only [P1P5.encPtr, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
        List.length_map]
      omega
    exact h.mono (by omega)
  | table _ _ _ | path _ _ | pins _ | route _ _ => exact False.elim hbasic

end

end P1SolFactor.SolHalf
