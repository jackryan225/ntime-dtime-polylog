import P1C10.Fmt10Defs
import P1SolFmt.Genuine
import P1ChkFinal.BinBits

namespace P1SolC10F.Sol

open OAI.Computability.IntegerMultiplication Code Carry Staff Strip
open OAI.DepthThreeLowerBound
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1C10 P1Wit P1Wit.SolSpace P1Wrap
open P1SolFmt.SolFigure P1SolFmt.SolFormat P1SolFmt.SolParameters

open private levelDims layoutRows runPhases slotCap slotCap_ge CalendarOK
  runPhases_OK levelConstant levelDims_bounds from P1Wit.SpaceFacts

private theorem row_form {k : Type*} [Field k] (S : BlockSchedule k)
    (P H i : ℕ) (phases : List Phase) (ready : Bool) (ok : CalendarOK S ready phases) :
    ∃ a h Q shrink, ((layoutRows S P H phases)[i]?).getD (levelDims S.expanderExponent 0 0 0 none) =
      levelDims S.expanderExponent a h Q shrink ∧ 2 ^ a ≤ slotCap S ∧ h ≤ H := by
  induction phases generalizing P H i ready with
  | nil =>
    cases i with
    | zero => exact ⟨S.degreeExponent 0, H, P, none, rfl, slotCap_ge S 0, le_rfl⟩
    | succ i =>
      have hcap := (Nat.two_pow_pos (S.degreeExponent 0)).trans_le (slotCap_ge S 0)
      exact ⟨0, 0, 0, none, by simp only [layoutRows, List.getElem?_cons_succ, List.getElem?_nil,
        Option.getD_none], hcap, Nat.zero_le _⟩
  | cons ph phases ih =>
    have ok' : 2 ^ ph.exponent ≤ slotCap S ∧
        (if ph.shrink then 2 ≤ ph.divisor ∧ CalendarOK S true phases
        else ready = true ∧ ph.divisor = 1 ∧ CalendarOK S false phases) := ok
    cases i with
    | zero => exact ⟨ph.exponent, H, P, some ph.shrink, rfl, ok'.1, le_rfl⟩
    | succ i =>
      have ⟨next, ht⟩ : ∃ next, CalendarOK S next phases := by
        by_cases hs : ph.shrink = true
        · rw [ite_eq_left hs] at ok'
          exact ⟨true, ok'.2.2⟩
        · rw [ite_eq_right hs] at ok'
          exact ⟨false, ok'.2.2.2⟩
      obtain ⟨a, h, Q, shrink, he, ha, hh⟩ := ih (P / ph.divisor) (H - ph.laneLoss) i next ht
      refine ⟨a, h, Q, shrink, ?_, ha, hh.trans (Nat.sub_le _ _)⟩
      simpa only [layoutRows, List.getElem?_cons_succ] using he

private theorem lane_radix_le (t : ℕ) : 2 ^ Params.h t ≤ (Params.lam t + 1) ^ 10 := by
  have hh : Params.h t ≤ 10 * Params.p t := by unfold Params.h; omega
  have hp : 2 ^ Params.p t ≤ Params.lam t + 1 := by
    unfold Params.p
    rcases Nat.eq_zero_or_pos (Params.lam t) with h | h
    · rw [h]
      decide
    · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ _)
  calc
    _ ≤ 2 ^ (10 * Params.p t) := Nat.pow_le_pow_right (by decide) hh
    _ = (2 ^ Params.p t) ^ 10 := by rw [Nat.mul_comm 10, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left hp _

private theorem packing_le {a b g : ℕ} (hab : a ≤ b) :
    packingLaneBits a g ≤ packingLaneBits b g := by
  have hp : 2 ^ a ≤ (2 : ℕ) ^ b := Nat.pow_le_pow_right (by decide) hab
  have ht : packingTagBits (2 ^ a) ≤ packingTagBits (2 ^ b) := by
    unfold packingTagBits
    apply Nat.add_le_add_right (Nat.log_mono_right ?_)
    gcongr
  unfold packingLaneBits
  omega

private theorem sum_map_le {M : Type*} (ms : List M) (f : M → ℕ) (W : ℕ)
    (hw : ∀ m ∈ ms, f m ≤ W) : (ms.map f).sum ≤ ms.length * W := by
  induction ms with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_rfl]
  | cons m ms ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm _ W]
    exact Nat.add_le_add (hw m List.mem_cons_self) (ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)))

private theorem foldr_max_le {xs : List ℕ} {u : ℕ} (h : ∀ x ∈ xs, x ≤ u) :
    xs.foldr max 0 ≤ u := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem size_bounds (D : Dims) (C L W : ℕ)
    (hwidth : ∀ s, D.width s ≤ W)
    (hrow : ∀ i, let R := D.lv i
      R.slots ≤ C ∧ slotBits D i ≤ C ∧ R.lanes ≤ L ∧ 2 ^ R.laneW ≤ L ∧
        R.termKeys ≤ C * L ∧ R.termArity ≤ C) :
    c10Size D ≤
      C * (6 * W) + L * C * W + W + W + 2 * W + (C * L) * (C + 1) * W + W +
        ((2 ^ packingLaneBits C 0 + 2 ^ C + 1) * L + 2 ^ C + 12 * W + 12 * W) := by
  have hbase (i : ℕ) : baseBits D i ≤
      C * (6 * W) + L * C * W + W + W + 2 * W + (C * L) * (C + 1) * W + W := by
    obtain ⟨hs, _, hl, _, hk, ha⟩ := hrow i
    have harcs : ([Mem.outAddr, .outDisp, .outFar, .inAddr, .inDisp, .inFar].map fun k =>
        D.width (secLev i k)).sum ≤ 6 * W := by
      exact sum_map_le _ _ W (fun m _ => hwidth (secLev i m))
    unfold baseBits
    gcongr <;> exact hwidth _
  have hfields (i : ℕ) : fieldW D i ≤ 12 * W :=
    sum_map_le _ _ W (fun m _ => hwidth (secLev i m))
  have hlanes (i : ℕ) : lanesUsed D i ≤ (2 ^ packingLaneBits C 0 + 2 ^ C + 1) * L + 2 ^ C := by
    obtain ⟨_, hs, _, _, _, _⟩ := hrow i
    obtain ⟨_, hn, _, hl, _, _⟩ := hrow (i + 1)
    have hpack : 2 ^ packingLaneBits (slotBits D i) 0 ≤ (2 : ℕ) ^ packingLaneBits C 0 :=
      Nat.pow_le_pow_right (by decide) (packing_le hs)
    have hslot : 2 ^ slotBits D i ≤ (2 : ℕ) ^ C := Nat.pow_le_pow_right (by decide) hs
    have hslotNext : 2 ^ slotBits D (i + 1) ≤ (2 : ℕ) ^ C := Nat.pow_le_pow_right (by decide) hn
    let g := (D.lv (i + 1)).laneW
    have hsplit : (2 : ℕ) ^ packingLaneBits (slotBits D i) g =
        2 ^ packingLaneBits (slotBits D i) 0 * 2 ^ g :=
      (congrArg (fun e : ℕ => (2 : ℕ) ^ e) (packingLaneBits_add (slotBits D i) g).symm).trans
        (pow_add 2 _ _)
    unfold lanesUsed
    rw [hsplit, pow_add 2 (slotBits D i) g]
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hpack hl)
      (Nat.mul_le_mul hslot hl)) hl) hslotNext
  unfold c10Size maxBaseBits
  apply Nat.add_le_add
  · apply foldr_max_le
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact hbase i
  · apply foldr_max_le
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact Nat.add_le_add (Nat.add_le_add (hlanes i) (hfields i)) (hfields (i + 1))

private theorem genuine_size_dom {k : Type} [Field k] {S : BlockSchedule k}
    (A : S.Templates) (K : Consts) (V : FiniteMultiTapeMachine) (aM d bigBias termBias : ℕ)
    {t : Bits.Word → ℕ} (ht : Figure (inputRegime Bits.Word) t) (g : Bits.Word → ℕ) :
    Dom size (fun w => c10Size (genuineDims A K V aM (t w) (g w) d bigBias termBias)) := by
  let C := levelConstant S
  have hc : slotCap S ≤ C := by unfold C levelConstant; omega
  let D (w : Bits.Word) := genuineDims A K V aM (t w) (g w) d bigBias termBias
  let L (w : Bits.Word) := (Params.lam (t w) + 1) ^ 10
  let W (w : Bits.Word) := 2 + (D w).bigW + (D w).wW + (D w).chainW + C + Params.h (t w)
  have fields (w : Bits.Word) (i : ℕ) :
      let R := (D w).lv i
      R.slots ≤ C ∧ slotBits (D w) i ≤ C ∧ R.lanes = 2 ^ R.laneW ∧ R.laneW ≤ Params.h (t w) ∧
        R.slotW ≤ C ∧ R.colW ≤ C ∧ R.tagW ≤ C ∧ R.termKeys ≤ C * R.lanes ∧ R.termArity ≤ C := by
    let phases := runPhases S (Params.T K (t w))
    obtain ⟨a, h, Q, shrink, he, ha, hh⟩ := row_form S (initialPositions V aM (t w))
      (Params.h (t w)) i phases true (runPhases_OK S _ true)
    change (D w).lv i = _ at he
    have hslot : ((D w).lv i).slots = 2 ^ a := by rw [he]; rfl
    have hbits := slotBits_eq hslot
    obtain ⟨hl, hw, hcol, htag, hkey, harity⟩ := levelDims_bounds S shrink ha
    dsimp only
    rw [hbits, he]
    exact ⟨ha.trans hc, hw, hl, hh, hw, hcol, htag,
      hkey.trans (Nat.mul_le_mul_right _ hc), harity⟩
  have hwidth (w : Bits.Word) (s : ℕ) : (D w).width s ≤ W w := by
    cases he : (D w).kind s <;> simp only [Dims.width, he, W]
    case lev i m =>
      obtain ⟨_, _, _, hh, hs, hc', ht', _, _⟩ := fields w i
      cases m <;> simp only [Dims.levWidth] <;> omega
    all_goals omega
  have hrows (w : Bits.Word) (i : ℕ) :
      let R := (D w).lv i
      R.slots ≤ C ∧ slotBits (D w) i ≤ C ∧ R.lanes ≤ L w ∧ 2 ^ R.laneW ≤ L w ∧
        R.termKeys ≤ C * L w ∧ R.termArity ≤ C := by
    obtain ⟨hs, hb, he, hh, _, _, _, hk, ha⟩ := fields w i
    have hp := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hh).trans (lane_radix_le (t w))
    have hl : ((D w).lv i).lanes ≤ L w := he.trans_le hp
    exact ⟨hs, hb, hl, hp, hk.trans (Nat.mul_le_mul_left C hl), ha⟩
  let fix := fun n => Staff.Realizes.fix (r := inputRegime Bits.Word) n
  let num := fun n => Figure.natural (r := inputRegime Bits.Word) n
  have hbig : Realizes (inputRegime Bits.Word) (fun w => (D w).bigW) :=
    (fix bigBias).plus ((fix 6).times (realizes_lam ht))
  have htuple := figure_tuple_width (Fintype.card (P1Net.Ext V.K))
    (Fintype.card V.Γ) (Fintype.card V.Q) (Fintype.card V.K) ht
  have hgrowth := (num A.growthConstant).repeated (realizes_T K ht)
  have hsmall : Realizes (inputRegime Bits.Word) (fun w => (D w).wW) :=
    (fix termBias).plus (((hgrowth.multiplied (htuple.added (num 1))).added (num 1)).short_log)
  have hw : Dom size W :=
    diameter W (((((fix 2).plus hbig).plus hsmall).plus (fix (Nat.clog 2 d))).plus
      (fix C) |>.plus (realizes_h ht))
  let constant := fun n => Dom.const (size : Bits.Word → ℕ) n
  have hl : Dom size L := ((diameter _ (realizes_lam ht)).add (constant 1)).pow 10
  have hbase := (((((((constant C).mul ((constant 6).mul hw)).add ((hl.mul (constant C)).mul hw)).add
    hw).add hw).add ((constant 2).mul hw)).add
      ((((constant C).mul hl).mul (constant (C + 1))).mul hw)).add hw
  have hcodes := ((((constant (2 ^ packingLaneBits C 0 + 2 ^ C + 1)).mul hl).add
    (constant (2 ^ C))).add ((constant 12).mul hw)).add ((constant 12).mul hw)
  exact (hbase.add hcodes).mono (fun w => size_bounds (D w) C (L w) (W w) (hwidth w) (hrows w))

theorem size10_cut_proof : Size10CutTarget := by
  intro k _ S A K V aM a b d bigBias termBias n₀
  let G := genD A K V aM a b d bigBias termBias
  let logSize := fun n : ℕ => Nat.log 2 (n + 1)
  have ht : Figure (inputRegime Bits.Word) (fun w => P1Int.lpTime a b (P1Batch.bval w)) := by
    simpa only [P1Wrap.W3.lpTime_eq] using figure_time a b figure_bval
  have hword : Dom size (fun w : Bits.Word => c10Size (G (P1Batch.bval w))) :=
    genuine_size_dom A K V aM d bigBias termBias ht _
  have hn : Dom logSize (fun n => size (P1ChkFinal.bin n)) := by
    refine ⟨1, 3, fun n => ?_⟩
    change size (P1ChkFinal.bin n) ≤ 3 * (logSize n + 1) ^ 1
    rw [Bits.size_word, pow_one]
    have h : (P1ChkFinal.bin n).length ≤ Nat.log 2 (n + 1) + 1 :=
      (P1ChkFinal.length_bin_log n).trans (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ n)) 1)
    dsimp only [logSize]
    omega
  have hG : Dom logSize (fun n => c10Size (G n)) := by
    simpa only [P1ChkFinal.bval_bin] using (hword.map P1ChkFinal.bin).sub hn
  apply (hG.add (Dom.const logSize 1)).mono
  intro n
  by_cases h : n₀ ≤ n
  · rw [cutDims_of_le G h]
    exact Nat.le_succ _
  · rw [cutDims_of_lt G (by omega), c10Size_zeroDims]
    exact Nat.le_add_left _ _

end P1SolC10F.Sol

theorem P1SolC10F.size10Cut : P1C10.Size10CutTarget :=
  P1SolC10F.Sol.size10_cut_proof

#print axioms P1SolC10F.size10Cut
