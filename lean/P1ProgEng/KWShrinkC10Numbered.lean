import P1ProgEng.KWShrinkC10Motifs
import P1P7.ShrinkFiber

namespace P1ProgEng.SolKWS.C10

open OAI.Computability.VPVNP.Compression
open OAI.Computability.VPVNP.Compression.SurvivingSlots
open OAI.Computability.IntegerMultiplication Code

abbrev IdRow := ℕ × ArcRow × ℕ
abbrev RolesRow := BundleRow × SiteRow × SiteRow
abbrev RoleArgs := ℕ × BallRows × Bool

def roleCode : PackedRole → ℕ
  | .a => 0
  | .b => 1
  | .d => 2

def roleAt (r : RolesRow) (i : ℕ) : SiteRow :=
  bif decide (i = 0) then r.1.1 else bif decide (i = 1) then r.2.1 else r.2.2

/-- Select a fixed role table for outgoing (`false`) or incoming (`true`) slots. -/
def roleTable (incoming layout : Bool) : List ℕ :=
  List.ofFn fun t : Fin 4 => roleCode ((bif incoming then targetRole else sourceRole) layout t)

def endRoleCode (incoming layout : Bool) (t : ℕ) : ℕ :=
  read 0 (bif layout then roleTable incoming true else roleTable incoming false) t

def idEnd (a : ℕ) (incoming : Bool) (args : RoleArgs) (z : IdRow) : SiteRow :=
  roleAt (rolesRow a args.1 args.2.1 args.2.2 z.2.1) (endRoleCode incoming args.2.2 z.1)

def attachId (sd : Fin 4 → ℕ) (m : ArcRow) (ti : Σ t : Fin 4, Fin (sd t)) : IdRow :=
  (ti.1.val, m, ti.2.val)

noncomputable def idRowsAt (sd : Fin 4 → ℕ) (m : ArcRow) : List IdRow :=
  List.ofFn fun i => attachId sd m ((Fintype.equivFin (Σ t : Fin 4, Fin (sd t))).symm i)

noncomputable def idRows (sd : Fin 4 → ℕ) (ms : List ArcRow) : List IdRow :=
  ms.flatMap (idRowsAt sd)

def childCode (a : ℕ) (s : SiteRow) : ℕ := tagCount a * s.1 + s.2.1

def idFibre (a : ℕ) (incoming : Bool) (args : RoleArgs) (x : ℕ) (zs : List IdRow) : List IdRow :=
  zs.filter fun z => decide (childCode a (idEnd a incoming args z) = x)

def idKey (a total : ℕ) (z : IdRow) : ℕ × ℕ :=
  (z.1, z.2.2 + total * motifKey a z.2.1)

def keyLT (p : (ℕ × ℕ) × (ℕ × ℕ)) : Bool :=
  decide (p.1.1 < p.2.1) || (decide (p.1.1 = p.2.1) && decide (p.1.2 < p.2.2))

def idRank (a total : ℕ) (zs : List IdRow) (z : IdRow) : ℕ :=
  (zs.filter fun w => keyLT (idKey a total w, idKey a total z)).length

@[fun_prop] theorem roleAt_poly : Poly (fun p : RolesRow × ℕ => roleAt p.1 p.2) := by
  unfold roleAt
  apply Code.Poly.choose (eqOn_poly poly_snd (Code.Poly.const 0))
  · fun_prop
  apply Code.Poly.choose (eqOn_poly poly_snd (Code.Poly.const 1)) <;> fun_prop

@[fun_prop] theorem endRoleCode_poly (incoming : Bool) :
    Poly (fun p : Bool × ℕ => endRoleCode incoming p.1 p.2) := by
  unfold endRoleCode
  fun_prop

@[fun_prop] theorem idEnd_poly (a : ℕ) (incoming : Bool) :
    Poly (fun p : RoleArgs × IdRow => idEnd a incoming p.1 p.2) := by
  unfold idEnd
  fun_prop

@[fun_prop] theorem idRowsAt_poly (sd : Fin 4 → ℕ) : Poly (idRowsAt sd) := by
  unfold idRowsAt
  apply fixedList_poly
  intro i
  unfold attachId
  fun_prop

@[fun_prop] theorem idRows_poly (sd : Fin 4 → ℕ) : Poly (idRows sd) :=
  (Code.Poly.maps _ (idRowsAt_poly sd)).compose flatten_poly

@[fun_prop] theorem childCode_poly (a : ℕ) : Poly (childCode a) := by
  unfold childCode
  fun_prop

@[fun_prop] theorem idFibre_poly (a : ℕ) (incoming : Bool) :
    Poly (fun p : RoleArgs × ℕ × List IdRow => idFibre a incoming p.1 p.2.1 p.2.2) := by
  have hf : Poly (fun p : (RoleArgs × ℕ) × IdRow =>
      decide (childCode a (idEnd a incoming p.1.1 p.2) = p.1.2)) :=
    eqOn_poly (by fun_prop) (by fun_prop)
  exact ((poly_fst.pair poly_snd.fstCompose).pair poly_snd.sndCompose).compose
    (filterWith_poly _ hf)

@[fun_prop] theorem idKey_poly (a total : ℕ) : Poly (idKey a total) := by unfold idKey; fun_prop

@[fun_prop] theorem keyLT_poly : Poly keyLT := by
  unfold keyLT
  have htypeLess : Poly (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.1 < p.2.1)) :=
    ltOn_poly (by fun_prop) (by fun_prop)
  have htypeEq : Poly (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.1 = p.2.1)) :=
    eqOn_poly (by fun_prop) (by fun_prop)
  have hinner : Poly (fun p : (ℕ × ℕ) × (ℕ × ℕ) => decide (p.1.2 < p.2.2)) :=
    ltOn_poly (by fun_prop) (by fun_prop)
  exact (htypeLess.pair ((htypeEq.pair hinner).compose bool_and_poly)).compose bool_or_poly

@[fun_prop] theorem idRank_poly (a total : ℕ) :
    Poly (fun p : List IdRow × IdRow => idRank a total p.1 p.2) := by
  have hp : Poly (fun p : IdRow × IdRow => keyLT (idKey a total p.2, idKey a total p.1)) := by
    fun_prop
  exact (Easy.exchange.poly.compose (filterWith_poly _ hp)).compose length_poly

end P1ProgEng.SolKWS.C10
