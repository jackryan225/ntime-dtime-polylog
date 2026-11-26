import P1SolCone.PhaseWalk

namespace P1SolCone.SolCone

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.MultitapeWeakETH.StackInterpreter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1ChkFinal P1ChkFinal.AstraC10
open scoped P1ChkFinal.AstraC10

attribute [local fun_prop] Easy.fst Easy.snd Easy.poly

@[fun_prop] theorem poly_testBitNat {A : Type} [Codec A] {f i : A → ℕ} (hf : Poly f) (hi : Poly i) :
    Poly (fun x => (f x).testBit (i x)) := by
  have h := poly_readAt false (poly_bin hf) hi
  convert h using 1
  funext x
  rw [bin_eq_bits, Nat.testBit_eq_inth]
  rfl

def phaseChildLanes (h : PhaseHeader) : ℕ := packetNat h.2.2.2.2 12

@[fun_prop] theorem phaseChildLanes_poly : Poly phaseChildLanes := by unfold phaseChildLanes; fun_prop

theorem phaseChildLanes_actual (D : Dims) (u : List Bool) (l y : ℕ) (clock : Tally) :
    phaseChildLanes (actualPhaseHeader D u l y clock) = (D.lv (l+1)).lanes := by
  unfold phaseChildLanes
  change packetNat (phaseFormat D l) 12 = _
  rw [packetNat_phaseFormat]
  rfl

theorem rawRoundCache_color_offset (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y : ℕ) (clock : Tally) (ys : List ℕ) (z : ℕ) (hz : z ∈ ys)
    (hw : ∀ m, D.width (secLev l m) ≤ clock.length) :
    let h := actualPhaseHeader D u l y clock
    let C := rawRoundCache extra u h ys
    rawRead h C .colour z = rdColour D u l z ∧ rawRead h C .offset z = rdOffset D u l z := by
  let h := actualPhaseHeader D u l y clock
  have col := mem_rawRoundKeys_base extra hz (List.mem_cons_self :
    phaseFieldKey false .colour h z ∈ rawBaseFields h z)
  have off := mem_rawRoundKeys_base extra hz (List.mem_cons_of_mem _ List.mem_cons_self :
    phaseFieldKey false .offset h z ∈ rawBaseFields h z)
  dsimp only
  unfold rawRead rdColour rdOffset
  rw [rawRoundCache_read _ _ _ _ _ col, rawRoundCache_read _ _ _ _ _ off]
  exact ⟨read_phaseFieldKey D u l y clock false .colour z (hw _),
    read_phaseFieldKey D u l y clock false .offset z (hw _)⟩

/-- Exact numerical projection of the shrinking placement row, even for arbitrary field values. -/
def rawShrinkOwner (a : ℕ) (h : PhaseHeader) (cache : FieldCache) (old : PositionCode) : ℕ :=
  let d := 2 ^ a
  let c := colors a
  let lowRadix := 2 ^ J a * phaseChildLanes h
  let n := old.1 * (2 ^ c * (d * lowRadix)) + old.2
  let hival := n / lowRadix
  let high := hival / d
  let base := high / 2 ^ c
  let slot := hival % d
  let low := n % lowRadix
  let thick := (high % 2 ^ c).testBit (c - 1 - rawRead h cache .colour base)
  let laneA := low ^^^ (rawRead h cache .offset base * phaseChildLanes h)
  let dst := (rawIncidence h cache .outAddr base slot * d + rawIncidence h cache .outFar base slot) / d
  let laneB := laneA ^^^ (rawIncidence h cache .outDisp base slot % lowRadix)
  bif thick then base * lowRadix + low
  else bif decide (rawRead h cache .layout 0 = 1) then dst * lowRadix + laneB
    else base * lowRadix + laneA

theorem rawShrinkOwner_poly (a : ℕ) :
    Poly (fun p : PhaseHeader × FieldCache × PositionCode => rawShrinkOwner a p.1 p.2.1 p.2.2) := by
  let Q := PhaseHeader × FieldCache × PositionCode
  let d := 2 ^ a
  let c := colors a
  let lowRadix (p : Q) := 2 ^ J a * phaseChildLanes p.1
  let ord (p : Q) := p.2.2.1 * (2 ^ c * (d * lowRadix p)) + p.2.2.2
  let hi (p : Q) := ord p / lowRadix p
  let high (p : Q) := hi p / d
  let base (p : Q) := high p / 2 ^ c
  let slot (p : Q) := hi p % d
  let low (p : Q) := ord p % lowRadix p
  have hrad : Poly lowRadix := by unfold lowRadix Q; fun_prop
  have hn : Poly ord := by unfold ord Q; fun_prop
  have hhi : Poly hi := by unfold hi; fun_prop
  have hhigh : Poly high := by unfold high; fun_prop
  have hbase : Poly base := by unfold base; fun_prop
  have hslot : Poly slot := by unfold slot; fun_prop
  have hlo : Poly low := by unfold low; fun_prop
  have read (m : Mem) : Poly (fun p : Q => rawRead p.1 p.2.1 m (base p)) :=
    ((show Poly (fun p : Q => p.1) from Easy.fst.poly).pair
      ((show Poly (fun p : Q => p.2.1) from by unfold Q; fun_prop).pair hbase)).compose (rawRead_poly m)
  have hlayout : Poly (fun p : Q => decide (rawRead p.1 p.2.1 .layout 0 = 1)) := by
    have h : Poly (fun p : Q => (p.1,p.2.1,0)) := by unfold Q; fun_prop
    exact poly_eqNat (h.compose (rawRead_poly .layout)) (Code.Poly.const 1)
  have hthick : Poly (fun p : Q => (high p % 2 ^ c).testBit (c - 1 - rawRead p.1 p.2.1 .colour (base p))) :=
    poly_testBitNat (by fun_prop) (poly_subNat (Code.Poly.const (c - 1)) (read .colour))
  let laneA (p : Q) := low p ^^^ (rawRead p.1 p.2.1 .offset (base p) * phaseChildLanes p.1)
  have ha : Poly laneA := by
    unfold laneA
    exact poly_xorNat hlo (poly_mulNat (read .offset) (Easy.fst.poly.compose phaseChildLanes_poly))
  have atSlot (m : Mem) : Poly (fun p : Q => rawIncidence p.1 p.2.1 m (base p) (slot p)) :=
    ((show Poly (fun p : Q => (p.1,p.2.1)) from by unfold Q; fun_prop).pair
      (hbase.pair hslot)).compose (rawIncidence_poly m)
  let dst (p : Q) := (rawIncidence p.1 p.2.1 .outAddr (base p) (slot p) * d +
    rawIncidence p.1 p.2.1 .outFar (base p) (slot p)) / d
  have hd : Poly dst := by
    unfold dst
    exact poly_divNat (poly_addNat (poly_mulNat (atSlot .outAddr) (Code.Poly.const d)) (atSlot .outFar))
      (Code.Poly.const d)
  let lb (p : Q) := laneA p ^^^ (rawIncidence p.1 p.2.1 .outDisp (base p) (slot p) % lowRadix p)
  have hb : Poly lb := poly_xorNat ha (poly_modNat (atSlot .outDisp) hrad)
  exact Poly.choose hthick (poly_addNat (poly_mulNat hbase hrad) hlo)
    (Poly.choose hlayout (poly_addNat (poly_mulNat hd hrad) hb) (poly_addNat (poly_mulNat hbase hrad) ha))

theorem rawShrinkOwner_eq (extra : PhaseHeader × ℕ → List FieldKey) (D : Dims) (u : List Bool)
    (l y a g : ℕ) (clock : Tally) (ys : List ℕ) (p : PositionCode) (hp : p.1 ∈ ys)
    (hc : (D.lv l).slots ≤ clock.length) (hw : ∀ m, D.width (secLev l m) ≤ clock.length)
    (hs : (D.lv l).slots = 2 ^ a) (hg : (D.lv (l+1)).lanes = 2 ^ g)
    (hlane : p.2 < 2 ^ packingLaneBits a g) :
    let h := actualPhaseHeader D u l y clock
    rawShrinkOwner a h (rawRoundCache extra u h ys) p = shrinkOwner D u l a g p := by
  let h := actualPhaseHeader D u l y clock
  let C := rawRoundCache extra u h ys
  let N := p.1 * 2 ^ packingLaneBits a g + p.2
  let A := 2 ^ (J a + g)
  let j := N / A % 2 ^ a
  have q : phaseChildLanes h = 2 ^ g := (phaseChildLanes_actual D u l y clock).trans hg
  have hrad : 2 ^ J a * 2 ^ g = A := (pow_add (2 : ℕ) (J a) g).symm
  have hfull : 2 ^ colors a * (2 ^ a * A) = 2 ^ packingLaneBits a g := by
    change 2 ^ colors a * (2 ^ a * 2 ^ (J a + g)) = 2 ^ (colors a + (a + (J a + g)))
    rw [pow_add (2 : ℕ) (colors a), pow_add (2 : ℕ) a (J a + g)]
  have hbase : N / A / 2 ^ a / 2 ^ colors a = p.1 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    rw [show A * (2 ^ a * 2 ^ colors a) = 2 ^ packingLaneBits a g by
      rw [← hfull]; ac_rfl]
    exact idx_div hlane
  have hj : j < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
  have hout (m : Mem) (hm : m ∈ [Mem.outAddr,.outDisp,.outFar,.inAddr,.inDisp,.inFar]) :
      rawIncidence h C m p.1 j = readField D u (secLev l m) (p.1 * (D.lv l).slots + j) :=
    rawRoundCache_incidence extra D u l y clock ys p.1 j hp hc (hs ▸ hj) m hm (hw m)
  have hcol := (rawRoundCache_color_offset extra D u l y clock ys p.1 hp hw).1
  have hoff := (rawRoundCache_color_offset extra D u l y clock ys p.1 hp hw).2
  have hlay := rawRoundCache_layout extra D u l y clock ys (hw .layout)
  have hdiv : (p.1 * 2 ^ a + j) / 2 ^ a = p.1 := idx_div hj
  have hmod : (p.1 * 2 ^ a + j) % 2 ^ a = j := idx_mod hj
  change rawShrinkOwner a h C p = _
  unfold rawShrinkOwner shrinkOwner row layoutOf decode join
  dsimp only
  rw [q, hrad, hfull]
  change (bif _ then _ else _) = if _ then _ else _
  rw [hbase, hdiv, hmod, hcol, hoff, hlay, hout .outAddr (by simp), hout .outFar (by simp), hout .outDisp (by simp)]
  cases (N / A / 2 ^ a % 2 ^ colors a).testBit (colors a - 1 - rdColour D u l p.1) <;>
    cases decide (rdLayout D u l = 1) <;> rfl

end P1SolCone.SolCone
