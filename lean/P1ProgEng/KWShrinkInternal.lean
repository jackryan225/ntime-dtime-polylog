import P1ProgEng.KWShrinkWidths
import P1ProgEng.KWShrinkWordLayout

namespace P1ProgEng.SolKWS

open OAI.Computability.IntegerMultiplication Code
open OAI.Computability.VPVNP
open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.ShrinkMotif
open OAI.Computability.VPVNP.MotifBlocks
open OAI.Computability.VPVNP.MotifGrid
open OAI.Computability.VPVNP.NetworkKernel
open P1P7 P1P5.KW
open C10
open scoped P1ChkFinal.AstraC10

theorem pairEq_poly {A D : Type} [Codec A] [Codec D] [DecidableEq A] [DecidableEq D]
    (ha : Poly (fun p : A × A => decide (p.1 = p.2)))
    (hd : Poly (fun p : D × D => decide (p.1 = p.2))) :
    Poly (fun p : (A × D) × (A × D) => decide (p.1 = p.2)) := by
  have h₁ : Poly (fun p : (A × D) × (A × D) => (p.1.1,p.2.1)) := by fun_prop
  have h₂ : Poly (fun p : (A × D) × (A × D) => (p.1.2,p.2.2)) := by fun_prop
  convert ((h₁.compose ha).pair (h₂.compose hd)).compose bool_and_poly using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact Prod.ext_iff

theorem ownerEq_poly : Poly (fun p : (ℕ × ArcRow) × (ℕ × ArcRow) => decide (p.1 = p.2)) :=
  pairEq_poly eq_poly (pairEq_poly (pairEq_poly
    (pairEq_poly eq_poly (pairEq_poly eq_poly eq_poly)) eq_poly) (pairEq_poly eq_poly eq_poly))

noncomputable section

variable {k : Type} [Field k] {factor : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)

def ownerWidth (a : ℕ) (p : RoleArgs × (ℕ × ArcRow)) : ℕ :=
  let e := p.2
  let ws := List.ofFn fun t : Fin 4 =>
    bif p.1.2.2 then codedSupply B a (false,t) (p.1,e.2)
      else codedSupply B a (true,t) (p.1,e.2)
  read 0 ws e.1

theorem ownerWidth_poly (a : ℕ) : Poly (ownerWidth B a) := by
  unfold ownerWidth
  dsimp only
  have hw (t : Fin 4) : Poly (fun p : RoleArgs × (ℕ × ArcRow) =>
    bif p.1.2.2 then codedSupply B a (false,t) (p.1,p.2.2)
      else codedSupply B a (true,t) (p.1,p.2.2)) :=
    Code.Poly.choose (by fun_prop) (by fun_prop) (by fun_prop)
  exact ((fixedList_poly _ hw).pair (by fun_prop)).compose (read_poly 0)

def ownerWidths (a : ℕ) (p : ResidentFrame) : List ℕ :=
  (ownerRows a p).map fun e => ownerWidth B a (p.1,e)

@[fun_prop] theorem ownerWidths_poly (a : ℕ) : Poly (ownerWidths B a) :=
  (Easy.fst.poly.pair (ownerRows_poly a)).compose
    (mapWith_poly _ (ownerWidth_poly B a))

/-- Read the absorbed label named by its old motif and supply type. -/
def absorbedWord (a : ℕ) (t : Fin 4)
    (p : ResidentFrame × Bits.Word × ArcRow) : Bits.Word :=
  let i := rowOrdinal (ownerRows a p.1,(t.val,p.2.2))
  let ws := ownerWidths B a p.1
  (p.2.1.drop (widthPrefix (ws,i))).take (read 0 ws i)

theorem absorbedWord_poly (a : ℕ) (t : Fin 4) : Poly (absorbedWord B a t) := by
  unfold absorbedWord
  dsimp only
  have hi : Poly (fun p : ResidentFrame × Bits.Word × ArcRow =>
      rowOrdinal (ownerRows a p.1,(t.val,p.2.2))) := by
    apply Code.Poly.compose _ (rowOrdinal_poly ownerEq_poly)
    fun_prop
  exact P1ProgEng.SolKWR.poly_take (by fun_prop)
    (P1ProgEng.SolKWR.poly_drop (by fun_prop) (by fun_prop))

section Spec

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (s : X.ShrinkSelection B)
variable {x : X.Base} {db : BallRows} (hdb : PayloadRows B X s x db)
variable (layout : Bool) (j : TagW a) (l : BitWord g)

local notation "v" => ((x,j),l)
local notation "p" => ((2 ^ g,db,layout), siteCode X (x,j,l))
local notation "Owners" => {u : X.packingData.Motif × Fin 4 // v = X.packingData.shrinkInternalOwner layout u}
local notation "OwnerWords" =>
  (Placed (X.packingData.shrinkInternalOwner layout) (internalLabel (selW B X s) layout) v)

def encodeIndex {n : ℕ} (u : X.packingData.Motif × Fin n) : ℕ × ArcRow :=
  (u.2.val,arcCode X u.1.val)

theorem encodeIndex_injective {n : ℕ} : Function.Injective (encodeIndex X (n := n)) := by
  intro u t h
  exact Prod.ext (Subtype.ext (arcCode_injective X (congrArg Prod.snd h)))
    (Fin.ext (congrArg Prod.fst h))

include hdb in
theorem ownerRows_spec (row : ℕ × ArcRow) :
    row ∈ ownerRows a p ↔ ∃ u : Owners, encodeIndex X u.val = row := by
  rw [ownerRows_eq, roleRows_spec X hdb.toLocalRows]
  constructor
  · rintro ⟨⟨u,hu⟩,rfl⟩
    exact ⟨⟨u,(congrArg packedSiteEquiv hu).symm⟩,rfl⟩
  · rintro ⟨⟨u,hu⟩,rfl⟩
    exact ⟨⟨u,packedSiteEquiv.injective hu.symm⟩,rfl⟩

noncomputable def ownerOrder : Fin (ownerRows a p).length ≃ Owners :=
  rowEquiv (by rw [ownerRows_eq]; exact roleRows_nodup _ _ _)
    ((encodeIndex_injective X).comp Subtype.val_injective) (ownerRows_spec B X s hdb layout j l)

theorem ownerOrder_encode (i : Fin (ownerRows a p).length) :
    encodeIndex X (ownerOrder B X s hdb layout j l i).val = (ownerRows a p)[i.val] :=
  rowEquiv_encode _ _ (ownerRows_spec B X s hdb layout j l) i

theorem ownerWidths_spec :
    ownerWidths B a p = List.ofFn fun i =>
      let u := (ownerOrder B X s hdb layout j l i).val
      selW B X s u.1 (!layout,u.2) := by
  unfold ownerWidths
  have tab := congrArg (List.map (fun e => ownerWidth B a (p.1,e)))
    (List.ofFn_getElem (xs := ownerRows a p)).symm
  rw [List.map_ofFn] at tab
  rw [tab]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [← ownerOrder_encode B X s hdb layout j l i]
  let u := ownerOrder B X s hdb layout j l i
  have hu : (X.packingData.survivingRole layout (internalRole layout u.val.2) u.val.1).1 = x :=
    (congrArg (fun w => w.1.1) u.property).symm
  unfold ownerWidth encodeIndex
  dsimp only
  rw [read_ofFn_num]
  have hb := bundle_near_of_role (x := x) X layout u.val.1 (internalRole layout u.val.2) hu
  cases layout <;> exact codedSupply_spec B X s hdb _ u.val.1 hb _

abbrev internalWidth (u : X.packingData.Motif × Fin 4) : ℕ :=
  selW B X s u.1 (!layout,u.2)

include hdb in
theorem ownerWords_card :
    Nat.card OwnerWords = 2 ^ (ownerWidths B a p).sum := by
  rw [ownerWidths_spec B X s hdb layout j l, List.sum_ofFn]
  exact internalEquiv_card (ownerOrder B X s hdb layout j l) (internalWidth B X s layout)

def internalOrder : OwnerWords ≃
    Fin (2 ^ ∑ i, internalWidth B X s layout (ownerOrder B X s hdb layout j l i).val) :=
  internalEquiv (ownerOrder B X s hdb layout j l) (internalWidth B X s layout)

def assignmentCode (h : OwnerWords) : Bits.Word :=
  List.ofFn (RAMSerialization.wordBits _ (internalOrder B X s hdb layout j l h))

theorem absorbedWord_spec (h : OwnerWords) (m : X.packingData.Motif) (t : Fin 4)
    (hh : v = X.packingData.shrinkInternalOwner layout (m,t)) :
    absorbedWord B a t (p,assignmentCode B X s hdb layout j l h,arcCode X m.val) =
      List.ofFn (RAMSerialization.wordBits _ (h (m,t) hh)) := by
  let u : Owners := ⟨(m,t),hh⟩
  let e := ownerOrder B X s hdb layout j l
  let i := e.symm u
  have he : e i = u := Equiv.apply_symm_apply _ _
  have hc : (t.val,arcCode X m.val) = (ownerRows a p)[i.val] :=
    (congrArg (fun u : Owners => encodeIndex X u.val) he).symm.trans
      (ownerOrder_encode B X s hdb layout j l i)
  have hd : rowOrdinal (ownerRows a p,(t.val,arcCode X m.val)) = i.val := by
    rw [hc]
    apply rowOrdinal_eq
    rw [ownerRows_eq]
    exact roleRows_nodup _ _ _
  have hw : ownerWidths B a p = List.ofFn (fun i => internalWidth B X s layout (e i).val) :=
    ownerWidths_spec B X s hdb layout j l
  unfold absorbedWord
  dsimp only
  rw [hd, hw, widthPrefix_ofFn, read_ofFn_num]
  change P1ProgEng.SolKWR.listSlice (fun i => internalWidth B X s layout (e i).val) i
    (List.ofFn (RAMSerialization.wordBits _ (internalEquiv e _ h))) = _
  rw [listSlice_internal e, he]

end Spec

end
end P1ProgEng.SolKWS
