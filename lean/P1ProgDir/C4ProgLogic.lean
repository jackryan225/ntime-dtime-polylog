import P1ChkDir.C4
import P1Batch.Statement
import P1ProgDir.C4ProgLength

namespace P1ProgDir.SolC4

open P1Net P1ChkDir P1Wit
open OAI.Computability.VPVNP Compression

variable {K : Type} [Fintype K] [DecidableEq K] {I h a : ℕ}

/-- The address order of level zero, including its padding bit. -/
noncomputable def baseEquiv (K : Type) [Fintype K] [DecidableEq K] (I h : ℕ) :
    ((Fin I × Loc K h) × Bool) ≃ Fin ((I * locCount K h) * 2) :=
  (((Equiv.refl (Fin I)).prodCongr (locEquiv K h)).trans finProdFinEquiv
    |>.prodCongr finTwoEquiv.symm).trans finProdFinEquiv

theorem baseEquiv_val (y : (Fin I × Loc K h) × Bool) :
    (baseEquiv K I h y).val = addrL y := by
  rcases y with ⟨⟨ι, l⟩, t⟩
  have ht : ((finTwoEquiv.symm t : Fin 2) : ℕ) = if t then 1 else 0 := by cases t <;> rfl
  simp only [baseEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    finProdFinEquiv_apply_val, locEquiv_val, addrL, ht]

theorem addrL_injective : Function.Injective (addrL (K := K) (I := I) (h := h)) := by
  intro y z hyz
  apply (baseEquiv K I h).injective
  apply Fin.ext
  simpa only [baseEquiv_val] using hyz

noncomputable def baseAt (K : Type) [Fintype K] [DecidableEq K] (I h i : ℕ) :
    Option ((Fin I × Loc K h) × Bool) :=
  if hi : i < (I * locCount K h) * 2 then some ((baseEquiv K I h).symm ⟨i, hi⟩) else none

theorem baseAt_eq_some_iff {i : ℕ} {y : (Fin I × Loc K h) × Bool} :
    baseAt K I h i = some y ↔ addrL y = i := by
  unfold baseAt
  split
  · rw [Option.some.injEq, Equiv.symm_apply_eq]
    constructor
    · intro hy
      simpa only [baseEquiv_val] using (congrArg Fin.val hy).symm
    · exact fun hy => Fin.ext (by simpa only [baseEquiv_val] using hy.symm)
  · rename_i hi
    have hy := addrL_lt y
    simp only [Nat.mul_comm 2 (I * locCount K h)] at hy
    have : addrL y ≠ i := by omega
    simp only [reduceCtorEq, this]

theorem c4f_at (ha : 4 ≤ 2 ^ a) (D : Dims) (L : DirLayout K I (2 ^ h))
    (u : List Bool) (Wc Ws Wt i : ℕ) :
    C4F ha D L u Wc Ws Wt i ↔
      (match baseAt K I h i with
       | none => True
       | some y => C4 ha D L u Wc Ws Wt y) := by
  cases hy : baseAt K I h i with
  | none =>
    refine ⟨fun _ => trivial, fun _ y he => ?_⟩
    rw [baseAt_eq_some_iff.mpr he] at hy
    contradiction
  | some y =>
    refine ⟨fun hh => hh y (baseAt_eq_some_iff.mp hy), fun hh z hz => ?_⟩
    have hyz : y = z := addrL_injective ((baseAt_eq_some_iff.mp hy).trans hz.symm)
    subst z
    exact hh

theorem addrL_div_two (ι : Fin I) (l : Loc K h) (t : Bool) :
    addrL ((ι, l), t) / 2 = locNum K h l + locCount K h * (ι : ℕ) := by
  unfold addrL
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.fst, Prod.snd] <;> omega

theorem addrL_mod_two (ι : Fin I) (l : Loc K h) (t : Bool) :
    addrL ((ι, l), t) % 2 = t.toNat := by
  unfold addrL
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat, Bool.cond_false, Bool.cond_true] <;> omega

/-- The two binary divisions used for addressing yield the interval and the
offset inside it, including when the number of locations varies with height. -/
theorem addrL_split (ι : Fin I) (l : Loc K h) (t : Bool) :
    addrL ((ι, l), t) / 2 / locCount K h = (ι : ℕ) ∧
      (addrL ((ι, l), t) / 2) % locCount K h = locNum K h l := by
  have hp : 0 < locCount K h := (Nat.zero_le _).trans_lt (locNum_lt l)
  rw [addrL_div_two, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (locNum_lt l), Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (locNum_lt l)]
  exact ⟨rfl, rfl⟩

/-- The same finite lane test indexed by the natural numbers stored by P6. -/
theorem storedWidths_iff {D : Dims} {u : List Bool} {y k w : ℕ} :
    (∀ lane : BitWord h, rdWidth D u 0 y (bwNum lane) k = w) ↔
      ∀ j < 2 ^ h, rdWidth D u 0 y j k = w := by
  constructor
  · intro hs j hj
    have ht := hs ((bitWordFinEquiv h).symm ⟨j, hj⟩)
    simpa only [bwNum, Equiv.apply_symm_apply] using ht
  · intro hs lane
    exact hs (bwNum lane) ((bitWordFinEquiv h) lane).isLt

theorem bval_eq_bitsVal (l : List Bool) : P1Batch.bval l = bitsVal l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp only [P1Batch.bval, bitsVal, ih] <;> rfl

/-- A request with its address clamped to the witness length. The layout readers
and the batched reader both return value zero for a field past the end. -/
def fieldReq (m : ℕ) (D : Dims) (s j : ℕ) : P1Batch.Req :=
  let offset := min m (D.off s + j * D.width s)
  (Length.born offset, Length.born (D.width s))

theorem bval_canonical (n : ℕ) : P1Batch.bval (Length.born n) = n :=
  (P1Batch.bval_eq_value _).trans (Length.birthValue n)

theorem fieldReq_address (m : ℕ) (D : Dims) (s j : ℕ) :
    P1Batch.bval (fieldReq m D s j).1 ≤ m := by
  simp only [fieldReq, bval_canonical, Nat.min_le_left]

theorem fieldReq_value (u : List Bool) (D : Dims) (s j : ℕ) :
    P1Batch.bval (P1Batch.fetch u (fieldReq u.length D s j)) = readField D u s j := by
  unfold P1Batch.fetch fieldReq readField readNat
  rw [bval_eq_bitsVal ((u.drop _).take _)]
  simp only [bval_canonical]
  rcases le_total (D.off s + j * D.width s) u.length with h | h
  · rw [Nat.min_eq_right h]
  · rw [Nat.min_eq_left h, List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (le_refl u.length)]

/-- Tape and displacement of the only directory-dependent half-edge at a site.
The flag selects the next-owner or previous-owner section. -/
def portQuery : Loc K h → Option (Bool × K × Fin 3)
  | .portIn k δ => some (false, k, δ)
  | .portOut k δ => some (true, k, δ)
  | _ => none

/-- Every local mate is fixed. Only a port's slot 1 depends on the directory. -/
theorem netMateD_congr_port (L L' : DirLayout K I (2 ^ h)) (u u' : List Bool)
    (ι : Fin I) (l : Loc K h)
    (hp : ∀ nxt k δ, portQuery l = some (nxt, k, δ) →
      let owner := if nxt then nD L u ι k δ else pD L u ι k δ
      owner = (if nxt then nD L' u' ι k δ else pD L' u' ι k δ) ∧
      bD L u ι k = bD L' u' ι k ∧
      ∀ j, owner = some j → bD L u j k = bD L' u' j k)
    (s : Fin 4) : netMateD L u ((ι, l), s) = netMateD L' u' ((ι, l), s) := by
  have e : interMateD L u ι l s = interMateD L' u' ι l s := by
    cases l with
    | portIn k δ =>
      have hh := hp false k δ rfl
      dsimp only [Bool.false_eq_true, ↓reduceIte] at hh
      obtain ⟨ho, hb, hf⟩ := hh
      change pD L u ι k δ = pD L' u' ι k δ at ho
      simp only [interMateD]
      split
      · rw [← ho]
        cases he : pD L u ι k δ with
        | none => rfl
        | some j => simp only [Option.map_some, slotD, portQD, hb, hf j he]
      · rfl
    | portOut k δ =>
      have hh := hp true k δ rfl
      dsimp only [↓reduceIte] at hh
      obtain ⟨ho, hb, hf⟩ := hh
      change nD L u ι k δ = nD L' u' ι k δ at ho
      simp only [interMateD]
      split
      · rw [← ho]
        cases he : nD L u ι k δ with
        | none => rfl
        | some j => simp only [Option.map_some, slotD, portQD, hb, hf j he]
      · rfl
    | _ => rfl
  simp only [netMateD, e]

theorem c4_congr_mate (ha : 4 ≤ 2 ^ a) (D : Dims) (u : List Bool) (Wc Ws Wt : ℕ)
    (y : (Fin I × Loc K h) × Bool)
    (m₁ m₂ : (Fin I × Loc K h) × Fin 4 → Option ((Fin I × Loc K h) × Fin 4))
    (hm : ∀ s, m₁ (y.1, s) = m₂ (y.1, s)) :
    PanelStored D u (addrL y) (panelOf ha m₁ Wc Ws Wt y) ↔
      PanelStored D u (addrL y) (panelOf ha m₂ Wc Ws Wt y) := by
  have he (k : Fin (2 ^ a)) :
      tgtOf ha m₁ y k = tgtOf ha m₂ y k ∧ dispOf m₁ y k = dispOf m₂ y k ∧
        ∀ lane, widthOf m₁ Wc Ws Wt y k lane = widthOf m₂ Wc Ws Wt y k lane := by
    cases hk : PreGraph.slot4 k <;> simp only [tgtOf, dispOf, widthOf, hk, hm, and_self, forall_const]
  simp only [PanelStored, panelOf]
  exact forall_congr' fun k => by simp only [(he k).1, (he k).2.1, (he k).2.2]


end P1ProgDir.SolC4
