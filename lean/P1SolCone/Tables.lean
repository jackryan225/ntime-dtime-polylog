import P1P5.EvalOrder
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Dedup

namespace P1SolCone.SolCone

/-- List of assignments to an ordered family of finite domains. -/
def assignments {A : Type*} : List (List A) → List (List A)
  | [] => [[]]
  | axis :: axes => axis.flatMap fun v => (assignments axes).map (v :: ·)

theorem mem_assignments {A : Type*} (axes : List (List A)) (v : List A) :
    v ∈ assignments axes ↔ List.Forall₂ (fun x xs => x ∈ xs) v axes := by
  induction axes generalizing v with
  | nil => cases v <;> simp [assignments]
  | cons axis axes ih =>
    cases v with
    | nil => simp [assignments]
    | cons x v => simp [assignments, ih]

theorem assignments_nodup {A : Type*} (axes : List (List A))
    (h : ∀ axis ∈ axes, axis.Nodup) : (assignments axes).Nodup := by
  induction axes with
  | nil => simp [assignments]
  | cons axis axes ih =>
    simp only [assignments, List.nodup_flatMap]
    have htail := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨fun _ _ => htail.map (fun _ _ e => (List.cons.inj e).2), ?_⟩
    apply (h axis List.mem_cons_self).imp
    intro x y hxy
    apply List.disjoint_left.mpr
    intro z hx hy
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ys, _, he⟩ := List.mem_map.mp hy
    exact hxy (List.cons.inj he).1.symm

/-- Length of the mixed-radix assignment table, including a single empty assignment
when there are no domains. -/
theorem length_assignments {A : Type*} (axes : List (List A)) :
    (assignments axes).length = (axes.map List.length).prod := by
  induction axes with
  | nil => rfl
  | cons axis axes ih =>
    have step (s : List A) :
        (s.flatMap fun v => (assignments axes).map (v :: ·)).length =
          s.length * (assignments axes).length := by
      induction s with
      | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
      | cons x s h =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, h,
          Nat.succ_mul, Nat.add_comm]
    simpa only [assignments, List.map_cons, List.prod_cons, ih] using step axis

/-- All Boolean words of the given width. -/
def bitWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitWords n).map (false :: ·) ++ (bitWords n).map (true :: ·)

theorem mem_bitWords (n : ℕ) (v : List Bool) : v ∈ bitWords n ↔ v.length = n := by
  induction n generalizing v with
  | zero => cases v <;> simp [bitWords]
  | succ n ih =>
    cases v with
    | nil => simp [bitWords]
    | cons hd tl => cases hd <;> simp [bitWords, ih]

theorem bitWords_nodup (n : ℕ) : (bitWords n).Nodup := by
  induction n with
  | zero => simp [bitWords]
  | succ n ih =>
    rw [bitWords, List.nodup_append]
    refine ⟨ih.map (fun _ _ h => (List.cons.inj h).2), ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
    intro v h0 w h1 eq
    obtain ⟨xs, _, rfl⟩ := List.mem_map.mp h0
    obtain ⟨ys, _, rfl⟩ := List.mem_map.mp h1
    cases (List.cons.inj eq).1

theorem length_bitWords (n : ℕ) : (bitWords n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bitWords, List.length_append, List.length_map, ih, pow_succ, Nat.mul_two]

/-- Lift a numerical enumeration to a typed enumeration while preserving the order.
The existence hypothesis guarantees that every code in the input has a typed preimage. -/
theorem enum_of_codes {A : Type} {B : Type*} (encode : A → B) (he : Function.Injective encode)
    (codes : List B) (hn : codes.Nodup) (hcover : ∀ a, encode a ∈ codes)
    (hvalid : ∀ b ∈ codes, ∃ a, encode a = b) :
    ∃ typed : List A, P1P5.IsEnum typed ∧ codes = typed.map encode := by
  classical
  let decode (b : {b // b ∈ codes}) := Classical.choose (hvalid b.val b.property)
  let typed := codes.attach.map decode
  have encDec (b : {b // b ∈ codes}) : encode (decode b) = b.val :=
    Classical.choose_spec (hvalid b.val b.property)
  have hmap : typed.map encode = codes := by
    simp only [typed, List.map_map, Function.comp_def, encDec, List.attach_map_subtype_val]
  refine ⟨typed, ⟨List.Nodup.of_map encode (hmap.symm ▸ hn), ?_⟩, hmap.symm⟩
  intro a
  obtain ⟨a', hmem, heq⟩ := List.mem_map.mp (hmap.symm ▸ hcover a)
  exact he heq ▸ hmem

abbrev PositionCode := ℕ × ℕ
abbrev HalfCode := List (List Bool) × List (List Bool)
abbrev KeyCode := PositionCode × HalfCode

/-- At a single position enumerate the outgoing and incoming words of their stored widths. -/
def halfCodes (widths : List ℕ × List ℕ) : List HalfCode :=
  (assignments (widths.1.map bitWords)).flatMap fun outs =>
    (assignments (widths.2.map bitWords)).map (outs, ·)

private theorem mem_wordAssignments (widths : List ℕ) (zs : List (List Bool)) :
    zs ∈ assignments (widths.map bitWords) ↔ zs.map List.length = widths := by
  induction widths generalizing zs with
  | nil => cases zs <;> simp [assignments]
  | cons w ws ih =>
    cases zs with
    | nil => simp [assignments]
    | cons z zs => simp [assignments, mem_bitWords, ih]

theorem mem_halfCodes (widths : List ℕ × List ℕ) (z : HalfCode) :
    z ∈ halfCodes widths ↔ z.1.map List.length = widths.1 ∧ z.2.map List.length = widths.2 := by
  obtain ⟨a, b⟩ := z
  simp only [halfCodes, List.mem_flatMap, List.mem_map, mem_wordAssignments, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha, b', hb, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

theorem halfCodes_nodup (widths : List ℕ × List ℕ) : (halfCodes widths).Nodup := by
  have h (ws : List ℕ) : (assignments (ws.map bitWords)).Nodup := by
    apply assignments_nodup
    intro axis haxis
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp haxis
    exact bitWords_nodup w
  exact (h widths.1).product (h widths.2)

private theorem length_wordAssignments (widths : List ℕ) :
    (assignments (widths.map bitWords)).length = 2 ^ widths.sum := by
  simp only [length_assignments, List.map_map, Function.comp_def, length_bitWords]
  induction widths with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, ih]

theorem length_halfCodes (widths : List ℕ × List ℕ) :
    (halfCodes widths).length = 2 ^ (widths.1.sum + widths.2.sum) := by
  unfold halfCodes
  rw [pow_add, ← length_wordAssignments widths.1, ← length_wordAssignments widths.2]
  generalize assignments (widths.1.map bitWords) = src
  induction src with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, Nat.succ_mul, ih,
      Nat.add_comm]

/-- Enumerate the placed assignments in the order of the explicit predecessors. -/
def placedCodes (halves : PositionCode → List HalfCode) (pre : List PositionCode) : List (List KeyCode) :=
  (assignments (pre.map halves)).map (pre.zip ·)

theorem length_placedCodes (halves : PositionCode → List HalfCode) (pre : List PositionCode) :
    (placedCodes halves pre).length = (pre.map fun p => (halves p).length).prod := by
  simp only [placedCodes, List.length_map, length_assignments, List.map_map, Function.comp_def]

/-- Generate input keys once per predecessor site. The same site's output assignments
must share one predecessor set so the number of keys does not multiply across phases. -/
def needKeys (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (keys : List KeyCode) : List KeyCode :=
  let sites := ((keys.map Prod.fst).dedup.flatMap pre).dedup
  sites.flatMap fun p => (halves p).map (p, ·)

theorem mem_needKeys (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    {keys : List KeyCode} {key : KeyCode} (hkey : key ∈ keys) {u : PositionCode} (hu : u ∈ pre key.1)
    {z : HalfCode} (hz : z ∈ halves u) : (u, z) ∈ needKeys pre halves keys := by
  simp only [needKeys, List.mem_flatMap, List.mem_dedup]
  exact ⟨u, ⟨key.1, List.mem_map_of_mem hkey, hu⟩, List.mem_map.mpr ⟨z, hz, rfl⟩⟩

/-- Compile the encoded key lists into one level in the D11 order. -/
def assembleLevel {F : Type} (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F) (keys : List KeyCode) : List KeyCode × P1P5.Level F :=
  let old := needKeys pre halves keys
  (old, keys.map fun key => (placedCodes halves (pre key.1)).map (fun ps =>
    (kernel key ps, ps.map old.idxOf)))

private theorem idxOf_map_of_injective {A B : Type*} [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (f : A → B) (hf : Function.Injective f) (k : A) (s : List A) :
    (s.map f).idxOf (f k) = s.idxOf k := by
  classical
  induction s with
  | nil => rfl
  | cons a as ih =>
    by_cases he : a = k
    · subst a
      simp only [List.map_cons, List.idxOf_cons_self]
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun h => he (hf h)), List.idxOf_cons_ne _ he, ih]

open OAI.Computability.VPVNP.NetworkKernel
open scoped Classical

private theorem assignment_encode {A B : Type} {V : A → Type}
    (e : ∀ a, V a → B) (axes : A → List B) (h : ∀ a v, e a v ∈ axes a)
    (us : List A) (q : ∀ a, V a) :
    us.map (fun a => e a (q a)) ∈ assignments (us.map axes) := by
  rw [mem_assignments]
  induction us with
  | nil => exact List.Forall₂.nil
  | cons a us ih => exact List.Forall₂.cons (h a (q a)) ih

private theorem assignment_decode {A B : Type} {V : A → Type}
    (e : ∀ a, V a → B) (axes : A → List B) (hvalid : ∀ a b, b ∈ axes a → ∃ v, e a v = b)
    (us : List A) (hu : P1P5.IsEnum us) (xs : List B) (hx : xs ∈ assignments (us.map axes)) :
    ∃ q : ∀ a, V a, us.map (fun a => e a (q a)) = xs := by
  classical
  have relation := (mem_assignments _ _).mp hx
  have hlen : xs.length = us.length := relation.length_eq.trans (List.length_map axes)
  have ordLt (a : A) : us.idxOf a < us.length := List.idxOf_lt_length_iff.mpr (hu.2 a)
  have witness (a : A) : ∃ val, e a val = xs[us.idxOf a]'(hlen.symm ▸ ordLt a) := by
    apply hvalid
    have slot := relation.get (hlen.symm ▸ ordLt a) (by simpa only [List.length_map] using ordLt a)
    simpa only [List.get_eq_getElem, List.getElem_map, List.getElem_idxOf (ordLt a)] using slot
  let q (a : A) := Classical.choose (witness a)
  refine ⟨q, List.ext_getElem (by rw [List.length_map, hlen]) ?_⟩
  intro i hi hi'
  have hi'' : i < us.length := by simpa only [List.length_map] using hi
  rw [List.getElem_map]
  change e us[i] (q us[i]) = xs[i]
  have hq := Classical.choose_spec (witness us[i])
  have index := hu.1.idxOf_getElem i hi''
  apply Option.some.inj
  rw [hq]
  simpa only [List.getElem?_eq_getElem, index] using congrArg (fun j => xs[j]?) index

private theorem zip_map_codes {A : Type} (us : List A) (pos : A → PositionCode) (half : A → HalfCode) :
    (us.map pos).zip (us.map half) = us.map fun a => (pos a, half a) := by
  induction us with
  | nil => rfl
  | cons a us ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The list of numeric placed assignments is the encoding of an exact enumeration of
dependent half-assignments on the given predecessor list. -/
theorem placedCodes_enum {A : Type} {V : A → Type}
    (us : List A) (hu : P1P5.IsEnum us) (pos : A → PositionCode)
    (enc : ∀ a, V a → HalfCode) (hinj : ∀ a, Function.Injective (enc a))
    (halves : PositionCode → List HalfCode)
    (hnd : ∀ a, (halves (pos a)).Nodup)
    (hcover : ∀ a v, enc a v ∈ halves (pos a))
    (hvalid : ∀ a h, h ∈ halves (pos a) → ∃ v, enc a v = h) :
    ∃ order : List (∀ a, V a), P1P5.IsEnum order ∧
      placedCodes halves (us.map pos) = order.map (fun q => us.map fun a => (pos a, enc a (q a))) := by
  let code (q : ∀ a, V a) := us.map fun a => (pos a, enc a (q a))
  let axes := us.map (fun a => halves (pos a))
  have same : (us.map pos).length = axes.length := by simp only [axes, List.length_map]
  have hlen (ys : List HalfCode) (hy : ys ∈ assignments axes) : ys.length = (us.map pos).length :=
    ((mem_assignments _ _).mp hy).length_eq.trans same.symm
  have result : placedCodes halves (us.map pos) = (assignments axes).map ((us.map pos).zip ·) := by
    simp only [placedCodes, List.map_map, Function.comp_def, axes]
  apply enum_of_codes code
  · intro q q' he
    funext a
    apply hinj a
    have i : us.idxOf a < us.length := List.idxOf_lt_length_iff.mpr (hu.2 a)
    have left : us.idxOf a < (code q).length := by simpa only [code, List.length_map] using i
    have eq := List.getElem_of_eq he left
    simp only [code, List.getElem_map] at eq
    let u := us[us.idxOf a]'i
    have hu : u = a := List.getElem_idxOf i
    change (pos u, enc u (q u)) = (pos u, enc u (q' u)) at eq
    rw [hu] at eq
    exact congrArg Prod.snd eq
  · rw [result]
    have hd : (assignments axes).Nodup := assignments_nodup _ (fun a ha => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
      exact hnd p)
    apply hd.map_on
    intro ys hy zs hz he
    have h := congrArg (List.map Prod.snd) he
    simpa only [List.map_snd_zip (hlen ys hy).le, List.map_snd_zip (hlen zs hz).le] using h
  · intro q
    rw [result]
    apply List.mem_map.mpr
    exact ⟨us.map (fun a => enc a (q a)), assignment_encode enc _ hcover us q, zip_map_codes ..⟩
  · rw [result]
    intro row hrow
    obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨q, hq⟩ := assignment_decode enc _ hvalid us hu ys hy
    rw [← hq, zip_map_codes]
    exact ⟨q, rfl⟩

/-- If the numeric predecessor and assignment lists represent an order, the generated entries
use exactly that order's kernel values and pointers. -/
theorem assembleLevel_eq {F : Type} [CommRing F] {N : Network} (t : Term F N)
    (o : P1P5.LevelOrd t)
    (site : t.output.Site → PositionCode) (half : ∀ w, t.output.Half w → HalfCode)
    (oldCode : P1P5.Key N → KeyCode) (hInj : Function.Injective oldCode)
    (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F)
    (hOld : needKeys pre halves (o.new.map (fun k => (site k.1, half k.1 k.2))) = o.old.map oldCode)
    (hChoices : ∀ w, placedCodes halves (pre (site w)) =
      (o.plc w).map fun p => (o.pre w).map (fun u => oldCode ⟨u.1, p u.1 u.2⟩))
    (hKernel : ∀ w z (p : Placed t.place N.Half w),
      kernel (site w, half w z) ((o.pre w).map fun u => oldCode ⟨u.1, p u.1 u.2⟩) = t.kernel w p z) :
    assembleLevel pre halves kernel (o.new.map (fun k => (site k.1, half k.1 k.2))) =
      (o.old.map oldCode, P1P5.levelDataO t o) := by
  classical
  simp only [assembleLevel, hOld, P1P5.levelDataO, List.map_map]
  apply congrArg (fun l => (o.old.map oldCode, l))
  apply List.map_congr_left
  intro key _
  simp only [Function.comp_apply, P1P5.levelEntryO, hChoices, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, hKernel, P1P5.pointersO, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  simpa only [Function.comp_apply] using idxOf_map_of_injective oldCode hInj ⟨u.1, p u.1 u.2⟩ o.old

/-- Numeric site and half-assignment encodings for one network in the selected chain. -/
structure KeyCoding (N : Network) where
  position : N.Site → PositionCode
  half : ∀ u, N.Half u → HalfCode
  position_injective : Function.Injective position
  half_injective : ∀ u, Function.Injective (half u)

def KeyCoding.key {N : Network} (c : KeyCoding N) (k : P1P5.Key N) : KeyCode :=
  (c.position k.1, c.half k.1 k.2)

theorem KeyCoding.key_injective {N : Network} (c : KeyCoding N) : Function.Injective c.key := by
  rintro ⟨u, z⟩ ⟨v, y⟩ h
  have huv : u = v := c.position_injective (congrArg Prod.fst h)
  subst v
  have hzy : z = y := c.half_injective u (congrArg Prod.snd h)
  subst y
  rfl

private theorem liftCodes {A : Type} {B : Type*} (encode : A → B) (hinj : Function.Injective encode)
    (codes : List B) (hvalid : ∀ b ∈ codes, ∃ a, encode a = b) :
    ∃ typed : List A, codes = typed.map encode ∧ ∀ a, encode a ∈ codes ↔ a ∈ typed := by
  let decode (b : {b // b ∈ codes}) := Classical.choose (hvalid b.val b.property)
  let typed := codes.attach.map decode
  have hmap : typed.map encode = codes := by
    have he (b : {b // b ∈ codes}) : encode (decode b) = b.val :=
      Classical.choose_spec (hvalid b.val b.property)
    simp only [typed, List.map_map, Function.comp_def, he, List.attach_map_subtype_val]
  refine ⟨typed, hmap.symm, ?_⟩
  intro a
  rw [← hmap]
  exact List.mem_map_of_injective hinj

/-- Correctness requirements for the three numeric inputs of a level. They are discharged
by the local P6 reads at the shrink and refresh phases. -/
structure NumericLevelOK {F : Type} [CommRing F] {N : Network} (t : Term F N)
    (src : KeyCoding N) (dst : KeyCoding t.output)
    (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F) : Prop where
  predecessors : ∀ w, ∃ us : List (t.Preimage w), P1P5.IsEnum us ∧
    pre (dst.position w) = us.map fun u => src.position u.val
  half_nodup : ∀ u, (halves (src.position u)).Nodup
  half_cover : ∀ u z, src.half u z ∈ halves (src.position u)
  half_valid : ∀ u z, z ∈ halves (src.position u) → ∃ a, src.half u a = z
  kernel_eq : ∀ w z (p : Placed t.place N.Half w) (us : List (t.Preimage w)), P1P5.IsEnum us →
    kernel (dst.key ⟨w, z⟩) (us.map fun u => src.key ⟨u.val, p u.val u.property⟩) = t.kernel w p z

/-- Numeric level assembly determines a good D11 order on its actual input and output keys. -/
theorem assembleLevel_good {F : Type} [CommRing F] {N : Network} (t : Term F N)
    (src : KeyCoding N) (dst : KeyCoding t.output)
    (pre : PositionCode → List PositionCode) (halves : PositionCode → List HalfCode)
    (kernel : KeyCode → List KeyCode → F) (h : NumericLevelOK t src dst pre halves kernel)
    (ks : List (P1P5.Key t.output)) :
    ∃ o : P1P5.LevelOrd t, o.Good ∧ o.new = ks ∧
      assembleLevel pre halves kernel (ks.map dst.key) = (o.old.map src.key, P1P5.levelDataO t o) := by
  classical
  choose us hus hpre using h.predecessors
  have choiceFor (w : t.output.Site) : ∃ order : List (Placed t.place N.Half w), P1P5.IsEnum order ∧
      placedCodes halves (pre (dst.position w)) =
        order.map fun q => (us w).map fun a => src.key ⟨a.val, q a.val a.property⟩ := by
    obtain ⟨ord, ho, he⟩ := placedCodes_enum (us w) (hus w) (fun a => src.position a.val)
      (fun a => src.half a.val) (fun a => src.half_injective a.val) halves
      (fun a => h.half_nodup a.val) (fun a => h.half_cover a.val) (fun a => h.half_valid a.val)
    let lift (p : (a : t.Preimage w) → N.Half a.val) : Placed t.place N.Half w := fun u hu => p ⟨u, hu⟩
    refine ⟨ord.map lift, ⟨ho.1.map ?_, fun q => ?_⟩, ?_⟩
    · intro p r e
      funext a
      exact congrFun (congrFun e a.val) a.property
    · exact List.mem_map.mpr ⟨fun a => q a.val a.property, ho.2 _, rfl⟩
    · rw [hpre, he]
      simp only [List.map_map, Function.comp_def, lift, KeyCoding.key]
  choose plc hplc hchoice using choiceFor
  have valid (code : KeyCode) (hc : code ∈ needKeys pre halves (ks.map dst.key)) :
      ∃ k, src.key k = code := by
    simp only [needKeys, List.mem_flatMap, List.mem_dedup] at hc
    obtain ⟨p, ⟨w, hw, hp⟩, hv⟩ := hc
    obtain ⟨key, hkey, rfl⟩ := List.mem_map.mp hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hkey
    change p ∈ pre (dst.position k.1) at hp
    rw [hpre k.1] at hp
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha⟩ := h.half_valid s.val z hz
    exact ⟨⟨s.val, a⟩, congrArg (src.position s.val, ·) ha⟩
  obtain ⟨old, hold, hmem⟩ := liftCodes src.key src.key_injective _ valid
  let o : P1P5.LevelOrd t := ⟨old, ks, us, plc⟩
  refine ⟨o, ⟨hus, hplc, ?_⟩, rfl, ?_⟩
  · intro k hk u z
    apply (hmem ⟨u.val, z⟩).mp
    apply mem_needKeys pre halves (key := dst.key k) (List.mem_map_of_mem hk) _ (h.half_cover u.val z)
    rw [show (dst.key k).1 = dst.position k.1 from rfl, hpre]
    exact List.mem_map_of_mem ((hus k.1).2 u)
  · exact assembleLevel_eq t o dst.position dst.half src.key src.key_injective pre halves kernel
      hold hchoice (fun w z p => h.kernel_eq w z p (us w) (hus w))

/-- Traverse the chronological levels backwards to discover the needed keys. Return the
level-zero keys and the tables in evaluation order. -/
def assembleChain {F : Type} (pre : ℕ → PositionCode → List PositionCode)
    (halves : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → F)
    (phases : List ℕ) (final : List KeyCode) : List KeyCode × List (P1P5.Level F) :=
  phases.foldr (fun ℓ acc =>
    let level := assembleLevel (pre ℓ) (halves ℓ) (kernel ℓ) acc.1
    (level.1, level.2 :: acc.2)) (final, [])

theorem assembleChain_cons {F : Type} (pre : ℕ → PositionCode → List PositionCode)
    (halves : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → F)
    (ℓ : ℕ) (phases : List ℕ) (final : List KeyCode) (keys : List KeyCode) (levels : List (P1P5.Level F))
    (hTail : assembleChain pre halves kernel phases final = (keys, levels))
    (next : List KeyCode) (level : P1P5.Level F)
    (hHead : assembleLevel (pre ℓ) (halves ℓ) (kernel ℓ) keys = (next, level)) :
    assembleChain pre halves kernel (ℓ :: phases) final = (next, level :: levels) := by
  unfold assembleChain at hTail ⊢
  rw [List.foldr_cons, hTail, hHead]

/-- The numerical inputs of all phases, aligned with the actual term chain. -/
def NumericChainOK {F : Type} [CommRing F] (pre : ℕ → PositionCode → List PositionCode)
    (halves : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → F) :
    {N Y : Network} → TermChain F N Y → KeyCoding N → KeyCoding Y → List ℕ → Prop
  | _, _, .done _, src, dst, phases => phases = [] ∧ src = dst
  | _, _, .more t _ tail, src, dst, phases =>
    ∃ (ℓ : ℕ) (next : List ℕ) (mid : KeyCoding t.output), phases = ℓ :: next ∧
      NumericLevelOK t src mid (pre ℓ) (halves ℓ) (kernel ℓ) ∧
      NumericChainOK pre halves kernel tail mid dst next

/-- The backward numeric traversal supplies a good order for the full selected term chain. -/
theorem assembleChain_good {F : Type} [CommRing F] (pre : ℕ → PositionCode → List PositionCode)
    (halves : ℕ → PositionCode → List HalfCode) (kernel : ℕ → KeyCode → List KeyCode → F) :
    ∀ {N Y : Network} (c : TermChain F N Y) (src : KeyCoding N) (dst : KeyCoding Y)
      (phases : List ℕ) (fin : List (P1P5.Key Y)),
      NumericChainOK pre halves kernel c src dst phases →
      ∃ ord : P1P5.ChainOrd c, P1P5.ChainOrd.Good c ord fin ∧
        assembleChain pre halves kernel phases (fin.map dst.key) =
          ((P1P5.ChainOrd.first c ord fin).map src.key, P1P5.encLevelsO c ord) := by
  intro N Y c
  induction c with
  | done N =>
    intro src dst phases fin h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨PUnit.unit, True.intro, rfl⟩
  | more t rec tail ih =>
    intro src dst phases fin h
    rcases h with ⟨ℓ, next, mid, rfl, hhead, htail⟩
    obtain ⟨ord, hgood, hnum⟩ := ih mid dst next fin htail
    obtain ⟨level, hlevel, hnew, htable⟩ := assembleLevel_good t src mid _ _ _ hhead
      (P1P5.ChainOrd.first tail ord fin)
    exact ⟨(level, ord), ⟨hlevel, hnew, hgood⟩,
      assembleChain_cons _ _ _ _ _ _ _ _ hnum _ _ htable⟩

end P1SolCone.SolCone

#print axioms P1SolCone.SolCone.enum_of_codes
#print axioms P1SolCone.SolCone.length_assignments
#print axioms P1SolCone.SolCone.assembleLevel_eq
#print axioms P1SolCone.SolCone.assembleChain_good
