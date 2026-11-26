import P1ChkFinal.C10Bits
import P1P7.KernelPos
import P1Wit.WitSiteOrder
import OAI.Computability.VPVNP.CompressorRecordsShrink
import Mathlib.Data.List.Dedup

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.CompressorRecords.Shrink
open P1Wit P1ChkFinal P1P7

theorem positionCode_injective {a g : ℕ} (X : State a g) :
    Function.Injective (fun s : X.network.Site => (addr X s.1, bwNum s.2)) := by
  intro s t h
  exact Prod.ext (P1P7.addr_injective X (congrArg Prod.fst h))
    ((bitWordFinEquiv _).injective (Fin.ext (congrArg Prod.snd h)))

/-- The D9 ordinal of the owner of one old position in a shrinking pass.
The inputs are the old base and lane numbers and the corresponding P6 fields. -/
def shrinkOwner (D : Dims) (u : List Bool) (ℓ a g : ℕ) (old : ℕ × ℕ) : ℕ :=
  let color := rdColour D u ℓ
  let offset := rdOffset D u ℓ
  let mate := fun i => join a (rdOutAddr D u ℓ (i / 2 ^ a) (i % 2 ^ a))
    (rdOutFar D u ℓ (i / 2 ^ a) (i % 2 ^ a))
  let shift := fun i => rdOutDisp D u ℓ (i / 2 ^ a) (i % 2 ^ a)
  (row a (colors a) (J a) g (layoutOf D u ℓ) color offset mate shift
    (join (packingLaneBits a g) old.1 old.2)).owner

theorem shrinkOwner_of_readers {a g : ℕ} (X : State a (packingLaneBits a g))
    (D : Dims) (u : List Bool) (ℓ : ℕ)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hColor : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y).val)
    (hOffset : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (old : X.network.Site) :
    let owner := oplace X (layoutOf D u ℓ) old
    shrinkOwner D u ℓ a g (addr X old.1, bwNum old.2) =
      (addr X owner.1.1 * 2 ^ J a + bwNum owner.1.2) * 2 ^ g + bwNum owner.2 := by
  let mate := fun i => join a (rdOutAddr D u ℓ (i / 2 ^ a) (i % 2 ^ a))
    (rdOutFar D u ℓ (i / 2 ^ a) (i % 2 ^ a))
  let shift := fun i => rdOutDisp D u ℓ (i / 2 ^ a) (i % 2 ^ a)
  have directory : Directory (g := g) X.slots X.baseIndex (rdColour D u ℓ) (rdOffset D u ℓ) mate shift := by
    refine ⟨hColor, hOffset, ?_, ?_⟩
    · intro y k
      have hdiv : join a (addr X y) k.val / 2 ^ a = addr X y := idx_div k.isLt
      have hmod : join a (addr X y) k.val % 2 ^ a = k.val := idx_mod k.isLt
      change join a (rdOutAddr D u ℓ (join a (addr X y) k.val / 2 ^ a)
        (join a (addr X y) k.val % 2 ^ a)) (rdOutFar D u ℓ (join a (addr X y) k.val / 2 ^ a)
        (join a (addr X y) k.val % 2 ^ a)) = _
      rw [hdiv, hmod, (hPanel y k).1, (hPanel y k).2.2.1]
      rfl
    · intro y k
      change rdOutDisp D u ℓ (join a (addr X y) k.val / 2 ^ a)
        (join a (addr X y) k.val % 2 ^ a) = _
      rw [show join a (addr X y) k.val / 2 ^ a = addr X y from idx_div k.isLt,
        show join a (addr X y) k.val % 2 ^ a = k.val from idx_mod k.isLt,
        (hPanel y k).2.1]
      rfl
  let old' := (packingInputSites X.Base a g).symm old
  have hOld : oldNumber X.baseIndex old' = join (packingLaneBits a g) (addr X old.1) (bwNum old.2) := by
    rw [oldNumber_original]
    have he : packingInputSites X.Base a g old' = old :=
      (packingInputSites X.Base a g).apply_symm_apply old
    have hb : old'.1.1 = old.1 := congrArg Prod.fst he
    have hl := congrArg Prod.snd he
    change _ * _ + bwNum (packingInputSites X.Base a g old').2 = _
    rw [hb, hl]
    rfl
  have h := congrArg (fun r : Row ℕ => r.owner)
    (row_exact X.slots X.baseIndex directory (layoutOf D u ℓ) old')
  change (row a (colors a) (J a) g (layoutOf D u ℓ) (rdColour D u ℓ) (rdOffset D u ℓ) mate shift
    (join (packingLaneBits a g) (addr X old.1) (bwNum old.2))).owner = _
  rw [← hOld, h]
  simp only [packedNumber, lowNumber, join, pow_add]
  change addr X (oplace X (layoutOf D u ℓ) old).1.1 * (2 ^ J a * 2 ^ g) +
      (bwNum (oplace X (layoutOf D u ℓ) old).1.2 * 2 ^ g + bwNum (oplace X (layoutOf D u ℓ) old).2) = _
  ring

/-- All possible predecessors are read from the parent and its neighbors.
The subsequent test keeps exactly the sites that are placed at the query site. -/
def shrinkCandidates (D : Dims) (u : List Bool) (ℓ a g parent : ℕ) : List (ℕ × ℕ) :=
  let slots := List.range (2 ^ a)
  let bases := parent :: (slots.map (rdOutAddr D u ℓ parent) ++ slots.map (rdInAddr D u ℓ parent))
  (bases.flatMap fun y => (List.range (2 ^ packingLaneBits a g)).map (fun lane => (y, lane))).dedup

def shrinkPreimages (D : Dims) (u : List Bool) (ℓ a g : ℕ) (site : ℕ × ℕ) :
    List (ℕ × ℕ) :=
  (shrinkCandidates D u ℓ a g (site.1 / 2 ^ J a)).filter
    fun old => shrinkOwner D u ℓ a g old == site.1 * 2 ^ g + site.2

private theorem mem_candidateBase {a G : ℕ} (X : State a G) (D : Dims) (u : List Bool) (ℓ : ℕ)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y)) (x y : X.Base)
    (hNear : (baseGraph X).edist x y ≤ 1) :
    addr X y ∈ addr X x :: ((List.range (2 ^ a)).map (rdOutAddr D u ℓ (addr X x)) ++
      (List.range (2 ^ a)).map (rdInAddr D u ℓ (addr X x))) := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq] at hNear
  rcases hNear with ha | he
  · rw [baseGraph, SimpleGraph.fromRel_adj] at ha
    apply List.mem_cons_of_mem
    rcases ha.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · apply List.mem_append_left
      refine List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, ?_⟩
      rw [(hPanel x k).1]
      exact congrArg (addr X) hk
    · let i := (X.slots.base.target (y, k)).2
      have hs : X.slots.base.target.symm (x, i) = (y, k) := by
        apply X.slots.base.target.injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext hk.symm rfl
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
      rw [(hPanel x i).2.2.2.1]
      exact congrArg (fun a => addr X a.1) hs
  · subst y
    exact List.mem_cons_self ..

private theorem shrinkCode_injective {a g : ℕ} (X : State a (packingLaneBits a g)) :
    Function.Injective (fun w : (X.Base × TagW a) × BitWord g =>
      ((addr X w.1.1 * 2 ^ J a + bwNum w.1.2) * 2 ^ g + bwNum w.2)) := by
  intro w w' h
  have ht (v : (X.Base × TagW a) × BitWord g) : bwNum v.1.2 < 2 ^ J a :=
    (bitWordFinEquiv _ v.1.2).isLt
  have hl (v : (X.Base × TagW a) × BitWord g) : bwNum v.2 < 2 ^ g :=
    (bitWordFinEquiv _ v.2).isLt
  have hBaseTag := congrArg (fun n => n / 2 ^ g) h
  rw [idx_div (hl w), idx_div (hl w')] at hBaseTag
  have hBase := congrArg (fun n => n / 2 ^ J a) hBaseTag
  rw [idx_div (ht w), idx_div (ht w')] at hBase
  have hTag := congrArg (fun n => n % 2 ^ J a) hBaseTag
  rw [idx_mod (ht w), idx_mod (ht w')] at hTag
  have hLane := congrArg (fun n => n % 2 ^ g) h
  rw [idx_mod (hl w), idx_mod (hl w')] at hLane
  exact Prod.ext (Prod.ext (X.baseIndex.injective (Fin.ext hBase))
    ((bitWordFinEquiv _).injective (Fin.ext hTag))) ((bitWordFinEquiv _).injective (Fin.ext hLane))

/-- The computed predecessor list has exactly the genuine old positions placed at this site. -/
theorem mem_shrinkPreimages {a g : ℕ} (X : State a (packingLaneBits a g))
    (D : Dims) (u : List Bool) (ℓ : ℕ)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (hColor : ∀ y, rdColour D u ℓ (addr X y) = (X.packingData.color y).val)
    (hOffset : ∀ y, rdOffset D u ℓ (addr X y) = bwNum (X.packingData.offset y))
    (x : X.Base) (j : TagW a) (l : BitWord g) (old : X.network.Site) :
    (addr X old.1, bwNum old.2) ∈ shrinkPreimages D u ℓ a g
      (addr X x * 2 ^ J a + bwNum j, bwNum l) ↔
      ((x, j), l) = oplace X (layoutOf D u ℓ) old := by
  have hj : bwNum j < 2 ^ J a := (bitWordFinEquiv _ j).isLt
  have hl : bwNum old.2 < 2 ^ packingLaneBits a g := (bitWordFinEquiv _ old.2).isLt
  unfold shrinkPreimages
  rw [List.mem_filter, beq_iff_eq, shrinkOwner_of_readers X D u ℓ hPanel hColor hOffset old]
  constructor
  · intro h
    exact (shrinkCode_injective X h.2).symm
  · intro h
    refine ⟨?_, ?_⟩
    · have hn := oplace_near (layoutOf D u ℓ) old
      rw [← h] at hn
      simp only [shrinkCandidates, idx_div hj, List.mem_dedup, List.mem_flatMap]
      refine ⟨addr X old.1, mem_candidateBase X D u ℓ hPanel x old.1 hn,
        List.mem_map.mpr ⟨bwNum old.2, List.mem_range.mpr hl, rfl⟩⟩
    · rw [← h]

theorem shrinkPreimages_nodup (D : Dims) (u : List Bool) (ℓ a g : ℕ) (site : ℕ × ℕ) :
    (shrinkPreimages D u ℓ a g site).Nodup := by
  unfold shrinkPreimages shrinkCandidates
  exact List.Nodup.filter _ (List.nodup_dedup _)

/-- Every numerical predecessor code returned by a genuine panel represents an actual site. -/
theorem shrinkPreimages_valid {a g : ℕ} (X : State a (packingLaneBits a g))
    (D : Dims) (u : List Bool) (ℓ : ℕ)
    (hPanel : ∀ y, PanelMatch D u ℓ (addr X y) (panel X y))
    (x : X.Base) (j : TagW a) (l : BitWord g) {p : ℕ × ℕ}
    (hp : p ∈ shrinkPreimages D u ℓ a g (addr X x * 2 ^ J a + bwNum j, bwNum l)) :
    ∃ old : X.network.Site, (addr X old.1, bwNum old.2) = p := by
  have hj : bwNum j < 2 ^ J a := (bitWordFinEquiv _ j).isLt
  have hmem := (List.mem_filter.mp hp).1
  simp only [shrinkCandidates, idx_div hj, List.mem_dedup, List.mem_flatMap] at hmem
  obtain ⟨α, hα, hp⟩ := hmem
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
  have hbase : ∃ y : X.Base, addr X y = α := by
    rcases List.mem_cons.mp hα with rfl | h
    · exact ⟨x, rfl⟩
    rcases List.mem_append.mp h with ho | hi
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ho
      let i : Fin (2 ^ a) := ⟨k, List.mem_range.mp hk⟩
      exact ⟨(X.slots.base.target (x, i)).1, (hPanel x i).1.symm⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      let i : Fin (2 ^ a) := ⟨k, List.mem_range.mp hk⟩
      exact ⟨(X.slots.base.target.symm (x, i)).1, (hPanel x i).2.2.2.1.symm⟩
  obtain ⟨y, hy⟩ := hbase
  let lane : Fin (2 ^ packingLaneBits a g) := ⟨n, List.mem_range.mp hn⟩
  refine ⟨(y, (bitWordFinEquiv _).symm lane), Prod.ext hy ?_⟩
  change ((bitWordFinEquiv _) ((bitWordFinEquiv _).symm lane)).val = n
  rw [Equiv.apply_symm_apply]

/-- A refresh promotes the first a lane bits to the low digit of the base address.
Its inverse demotes them back to the front of the lane. -/
def refreshPreimage (a g : ℕ) (site : ℕ × ℕ) : ℕ × ℕ :=
  (site.1 / 2 ^ a, join g (site.1 % 2 ^ a) site.2)

theorem refreshPreimage_split {a g : ℕ} (X : State a (a + g)) (old : X.network.Site) :
    let split := splitBitWord a g old.2
    refreshPreimage a g (addr X old.1 * 2 ^ a + bwNum split.1, bwNum split.2) =
      (addr X old.1, bwNum old.2) := by
  let split := splitBitWord a g old.2
  have h : bwNum split.1 < 2 ^ a := (bitWordFinEquiv _ split.1).isLt
  change ( (addr X old.1 * 2 ^ a + bwNum split.1) / 2 ^ a,
    join g ((addr X old.1 * 2 ^ a + bwNum split.1) % 2 ^ a) (bwNum split.2)) = _
  rw [idx_div h, idx_mod h]
  exact Prod.ext rfl (splitBitWord_number a g old.2).symm

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.mem_shrinkPreimages
#print axioms P1SolCone.SolCone.shrinkPreimages_valid
