import P1SolCone.ConeTraceBounds

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1Wit.SolSpace P1ChkFinal P1ChkFinal.AstraC10 P1Int P1Int.P11
open scoped P1ChkFinal.AstraC10
open private slotCap from P1Wit.SpaceFacts

def halfCount (slots width : ℕ) : ℕ := 2 ^ (2 * slots * width)

def keyCountBound (slots width : ℕ) : ℕ := width * halfCount slots width

def levelCodeBound (slots width parents ringSize : ℕ) : ℕ :=
  let n := keyCountBound slots width
  let entry := 2 * ringSize + 2 + (parents * (2 * n + 2) + 1)
  n * (halfCount slots width ^ parents * (entry+1) + 2) + 1

theorem keyCountBound_pos (slots : ℕ) {width : ℕ} (hw : 0 < width) :
    1 ≤ keyCountBound slots width :=
  Nat.mul_pos hw (Nat.two_pow_pos _)

theorem needKeys_origin {pre : PositionCode → List PositionCode} {halves : PositionCode → List HalfCode}
    {keys : List KeyCode} {q : KeyCode} (hq : q ∈ needKeys pre halves keys) :
    ∃ v ∈ keys, q.1 ∈ pre v.1 ∧ q.2 ∈ halves q.1 := by
  simp only [needKeys, List.mem_flatMap, List.mem_dedup] at hq
  obtain ⟨p,⟨y,hy,hp⟩,hr⟩ := hq
  obtain ⟨q',hq',eq⟩ := List.mem_map.mp hy
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
  exact ⟨q',hq',eq ▸ hp,hz⟩

noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (V : C1Challenge.Machine) (a b d bigBias termBias : ℕ)

local notation "Dobs" w => coneDims B V a b d bigBias termBias (P1Batch.bval w)
local notation "Clock" w => coneReadClock B V a b bigBias termBias w
local notation "Wobs" w => Mbar B V a b (P1Batch.bval w)

set_option maxHeartbeats 1600000 in
theorem checkedTrace_bounds {F : Type} [CommRing F] [Fintype F]
    (w : Bits.Word) (u : List Bool) (addr : ℕ) (haddr : (Dobs w).bigW ≤ addr)
    (final : KeyCode) (hfinal : keyFits addr (Clock w).length (slotCap S) (Wobs w) final)
    (kernel : ℕ → KeyCode → List KeyCode → F)
    (ls : List ℕ) (hValid : ∀ l ∈ ls, l < (Dobs w).top) (hLen : ls.length ≤ (Dobs w).top)
    (ks : List KeyCode) (levels : List (P1P5.Level F))
    (h : assembleCheckedChain (phaseAllowed (Dobs w) u B.recordLimit (Wobs w))
      (phasePreimages (Dobs w) u) (phaseHalves (Dobs w) u) kernel ls [final] = some (ks,levels)) :
    ks.length ≤ keyCountBound (slotCap S) (Wobs w) ∧
    (∀ q ∈ ks, keyFits addr ((ls.length+1)*(Clock w).length) (slotCap S) (Wobs w) q) ∧
    levels.length = ls.length ∧
    (∀ L ∈ levels, size (P1P5.encLevel L) ≤ levelCodeBound (slotCap S) (Wobs w) B.recordLimit (Fintype.card F)) := by
  let D := Dobs w
  let width := Wobs w
  let slots := slotCap S
  let C := B.recordLimit
  let allow := phaseAllowed D u C width
  let pre := phasePreimages D u
  let half := phaseHalves D u
  let H := halfCount slots width
  let N := keyCountBound slots width
  have boundHist (j : ℕ) (hj : j ≤ D.top) : C ^ j ≤ width := by
    apply coneHistory_frontier B V a b (P1Batch.bval w) j
    change j ≤ (S.steps + 1) * _ 
    rw [← genuine_top B (portConsts B) (toOAI V) 1 (lpTime a b (P1Batch.bval w))
      (a * (P1Batch.bval w ^ 2 + 1)) d bigBias termBias]
    exact hj
  change assembleCheckedChain allow pre half kernel ls [final] = some (ks,levels) at h
  change ks.length ≤ N ∧
    (∀ q ∈ ks, keyFits addr ((ls.length+1)*(Clock w).length) slots width q) ∧
    levels.length = ls.length ∧ _
  induction ls generalizing ks levels with
  | nil =>
    simp only [assembleCheckedChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp only [List.mem_singleton, List.length_nil, List.length_cons, Nat.zero_add, Nat.one_mul,
      forall_eq, List.not_mem_nil, false_implies, implies_true, true_and, and_true]
    exact ⟨keyCountBound_pos slots (Mbar_pos B V a b _),hfinal⟩
  | cons l ls ih =>
    have hl : l < D.top := hValid _ List.mem_cons_self
    have ht : ls.length ≤ D.top := le_trans (Nat.le_succ _) hLen
    cases oldRun : assembleCheckedChain allow pre half kernel ls [final] with
    | none =>
      rw [assembleCheckedChain, oldRun] at h
      contradiction
    | some result =>
      obtain ⟨old, tabs⟩ := result
      obtain ⟨hOldSize,hOldFit,hTabs,hTableSize⟩ :=
        ih (fun j hj => hValid j (List.mem_cons_of_mem _ hj)) ht old tabs oldRun
      have hist := checkedFrontier_le allow pre half kernel C
        (fun j q ok => (phaseAllowed_limits D u C width j q ok).1) ls [final] old tabs oldRun
      have hf : positionCount [final] = 1 := rfl
      have fBound : positionCount old ≤ width := by
        rw [hf, Nat.one_mul] at hist
        exact hist.trans (boundHist _ ht)
      rw [assembleCheckedChain, oldRun] at h
      let next := assembleLevel (pre l) (half l) (kernel l) old
      change (if old.all (allow l) then some (next.1,next.2 :: tabs) else none) = _ at h
      split at h
      next yes =>
        have e : next.1 = ks ∧ next.2 :: tabs = levels := Prod.mk.inj (Option.some.inj h)
        obtain ⟨rfl,rfl⟩ := e
        have hGood (q : KeyCode) (hq : q ∈ old) :=
          phaseAllowed_limits D u C width l q (List.all_eq_true.mp yes _ hq)
        have hParents (q : KeyCode) (hq : q ∈ old) : (pre l q.1).length ≤ C := (hGood q hq).1
        have hslots : (D.lv l).slots ≤ slots :=
          (coneDims_rowBounds B V a b d bigBias termBias (P1Batch.bval w) l hl.le).slots_le
        have hHalf (q : KeyCode) (hq : q ∈ old) (p : PositionCode) (hp : p ∈ pre l q.1) :
            (half l p).length ≤ H := by
          obtain ⟨ho,hi⟩ := readHalfWidths_lengths D u l p
          obtain ⟨wo,wi⟩ := widthsWithin_fields _ _ ((hGood q hq).2 p hp)
          exact halfCodeCount_le _ _ _ (ho.le.trans hslots) (hi.le.trans hslots) wo wi
        have nsize : next.1.length ≤ N := by
          have hn := needKeys_count_le (pre l) (half l) old C H hParents hHalf
          change next.1.length ≤ (positionCount old * C) * H at hn
          have hhist : positionCount old * C ≤ width := by
            have he := hist
            rw [hf, Nat.one_mul] at he
            have e := Nat.mul_le_mul_right C he
            rw [← pow_succ] at e
            exact e.trans (boundHist _ hLen)
          exact hn.trans (Nat.mul_le_mul_right _ hhist)
        refine ⟨nsize,?_,?_,?_⟩
        · intro q hq
          obtain ⟨v,hv,hp,hz⟩ := needKeys_origin (pre := pre l) (halves := half l) hq
          have vfit := hOldFit v hv
          obtain ⟨ha,hlane⟩ :=
            phasePreimages_address_bounds B V a b d bigBias termBias u w l hl addr _ haddr v.1 q.1
              ⟨vfit.1,vfit.2.1⟩ hp
          obtain ⟨ho,hi,hw⟩ := halfCode_limits _ _ ((hGood v hv).2 q.1 hp) q.2 hz
          obtain ⟨e₁,e₂⟩ := readHalfWidths_lengths D u l q.1
          refine ⟨ha,?_,(ho.trans e₁).le.trans hslots,(hi.trans e₂).le.trans hslots,hw⟩
          simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc] using hlane
        · simp only [List.length_cons,hTabs]
        · intro L hL
          rcases List.mem_cons.mp hL with rfl | hL
          · have hs : 1 ≤ H := Nat.two_pow_pos _
            have tb := assembledLevel_size (pre l) (half l) (kernel l) old C (H ^ C) hParents
              (fun q hq => placedCodeCount_le (half l) (pre l q.1) C H (hParents q hq) hs (hHalf q hq))
            dsimp only at tb
            unfold levelCodeBound
            dsimp only
            change size (P1P5.encLevel next.2) ≤ _
            apply tb.trans
            gcongr <;> first | exact hOldSize | exact nsize
          · exact hTableSize L hL
      next => contradiction

end

end P1SolCone.SolCone
