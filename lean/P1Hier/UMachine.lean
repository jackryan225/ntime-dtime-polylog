import P1Hier.EasyBits

/-!
# P1Hier.UMachine: the universal verifier of W2 as ONE stack task (copy B of lane hier)

Target: `P1Hier.accU_machine` (statement of `Hierarchy.lean`, copy A). This file proves it from
SIX explicit hypotheses (`accU_machine_of`); everything else is proved here:

* the machine has NO control flow: on the input `withGuess u x` it computes
  `E1` (linear) → `arith` on the two numbers → `E2` (linear) → the W1 check → `E3` (finite),
  and the answer is a Boolean combination (`accUb`). The code and the row limit are replaced by
  a default when the guard fails, so the W1 check always runs within the budget;
* `accUb_iff`: this Boolean function is `accU` (for guesses of length `gU n`);
* `budget_bound`: the total budget is `D (n² + 1)`;
* `accU_machine_of_task`: `compile_task` + `ofOAI` + the time bound.

The six hypotheses (open tasks, all stated with the Codecs of `Universal.lean`):
* `h1 : Easy unGuess`               split `withGuess u x` into `(u, x)`;
* `h2 : Easy (px2 d)`               parse the machine code from a prefix of `x` (linear time);
* `h5 : Easy decT2`                 parse `serT τ ++ zeros` (linear time);
* `h6 : Computes (n² + s²) (arith q)`  guard, `G q n` and `n² / (s+1)²` on unary numbers;
* `h7`                              the W1 check task (`check_task_of_phases`, copy A);
* `h8 : size c ≤ 4 csz c + 4`       tree size against bit size of a machine code.
-/

namespace P1Hier.UM

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open C1Challenge (withGuess HaltsWithin)

/-! ## The functions -/

/-- Split a verifier input into guess and input. -/
def unGuess : List Bool → List Bool × List Bool
  | true :: b :: r => (b :: (unGuess r).1, (unGuess r).2)
  | false :: r => ([], r)
  | _ => ([], [])

theorem unGuess_withGuess (u x : List Bool) : unGuess (withGuess u x) = (u, x) := by
  induction u with
  | nil => simp [withGuess, unGuess]
  | cons b r ih =>
    have h : withGuess (b :: r) x = true :: b :: withGuess r x := by simp [withGuess]
    rw [h]
    simp [unGuess, ih]

/-- The parsed code with a flag (and a default). -/
noncomputable def px2 (d : MCode) (x : List Bool) : Bool × MCode := ((px x).isSome, (px x).getD d)

theorem px_some {x : List Bool} {c : MCode} (h : px x = some c) : ∃ r, x = serCode c ++ r := by
  by_cases hex : ∃ c r, x = serCode c ++ r
  · rw [px, dif_pos hex] at h
    obtain ⟨r, hr⟩ := Classical.choose_spec hex
    rw [Option.some.inj h] at hr
    exact ⟨r, hr⟩
  · rw [px, dif_neg hex] at h
    cases h

def allFalse (l : List Bool) : Bool := (l.map fun b => !b).all id

theorem allFalse_iff (l : List Bool) : allFalse l = true ↔ ∀ b ∈ l, b = false := by
  simp [allFalse, List.all_eq_true]

open Classical in
/-- Parse a transcript followed by zeros. -/
noncomputable def decT (r : List Bool) : Option (List Entry) :=
  if h : ∃ τ z, r = serT τ ++ z ∧ ∀ b ∈ z, b = false then some (Classical.choose h) else none

noncomputable def decT2 (r : List Bool) : Bool × List Entry := ((decT r).isSome, (decT r).getD [])

theorem decT_eq (τ : List Entry) (z : List Bool) (hz : ∀ b ∈ z, b = false) :
    decT (serT τ ++ z) = some τ := by
  have h : ∃ τ' z', serT τ ++ z = serT τ' ++ z' ∧ ∀ b ∈ z', b = false := ⟨τ, z, rfl, hz⟩
  rw [decT, dif_pos h]
  obtain ⟨z', hz', -⟩ := Classical.choose_spec h
  exact congrArg some ((pf_serL pf_serEntry) _ _ _ _ hz').1.symm

theorem decT_some (r : List Bool) (τ : List Entry) (h : decT r = some τ) :
    ∃ z, r = serT τ ++ z ∧ ∀ b ∈ z, b = false := by
  by_cases hex : ∃ τ z, r = serT τ ++ z ∧ ∀ b ∈ z, b = false
  · rw [decT, dif_pos hex] at h
    obtain ⟨z, hz⟩ := Classical.choose_spec hex
    rw [Option.some.inj h] at hz
    exact ⟨z, hz⟩
  · rw [decT, dif_neg hex] at h
    cases h

/-- The arithmetic of the universal verifier on `(n, s)`: the guard, `G q n`, the row limit. -/
def arith (q : ℕ) (i : ℕ × ℕ) : Bool × ℕ × ℕ :=
  (decide ((i.2 + 1) ^ 2 ≤ rootLog q i.1), G q i.1, i.1 ^ 2 / (i.2 + 1) ^ 2)

open Classical in
/-- The W1 check as a bit. -/
noncomputable def chk (i : MCode × List Bool × ℕ × List Entry) : Bool :=
  decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2)

/-- State after the arithmetic: `((guard, G, row limit), (parsed?, code), u, x)`. -/
abbrev S2 := (Bool × ℕ × ℕ) × (Bool × MCode) × List Bool × List Bool

/-- State after the first linear stage: `((n, s), (parsed?, code), u, x)`. -/
noncomputable def E1 (d : MCode) (y : List Bool) : (ℕ × ℕ) × (Bool × MCode) × List Bool × List Bool :=
  (((unGuess y).2.length, csz (px2 d (unGuess y).2).2), px2 d (unGuess y).2, (unGuess y).1,
    (unGuess y).2)

def cutOf (s : S2) : List Bool × List Bool :=
  cutLists (List.replicate s.1.2.1 (), s.2.2.1.tail)

/-- Second linear stage: the input of the W1 check (sanitized) and four bits. -/
noncomputable def E2 (d : MCode) (s : S2) :
    (MCode × List Bool × ℕ × List Entry) × (Bool × Bool × Bool × Bool) :=
  ((bif (s.2.1.1 && s.1.1) then s.2.1.2 else d, withGuess (cutOf s).1 s.2.2.2,
      bif (s.2.1.1 && s.1.1) then s.1.2.2 else 0, (decT2 (cutOf s).2).2),
   (s.2.1.1 && s.1.1, s.2.2.1.headD false, allFalse s.2.2.1.tail, (decT2 (cutOf s).2).1))

/-- The final Boolean combination. -/
def E3 (p : Bool × (Bool × Bool × Bool × Bool)) : Bool :=
  p.2.1 && (bif p.2.2.1 then p.2.2.2.1 else (p.2.2.2.2 && p.1))

noncomputable def stateB (q : ℕ) (d : MCode) (x u : List Bool) : S2 :=
  (arith q (x.length, csz (px2 d x).2), px2 d x, u, x)

/-- The answer of the universal verifier. -/
noncomputable def accUb (q : ℕ) (d : MCode) (x u : List Bool) : Bool :=
  E3 (chk (E2 d (stateB q d x u)).1, (E2 d (stateB q d x u)).2)

/-! ## The answer is `accU` -/

theorem accUb_iff (q : ℕ) (d : MCode) (x u : List Bool) (hu : u.length = gU x.length) :
    accUb q d x u = true ↔ accU q x u := by
  classical
  obtain ⟨fl, t, rfl⟩ : ∃ fl t, u = fl :: t := by
    cases u with
    | nil => simp [gU] at hu
    | cons a r => exact ⟨a, r, rfl⟩
  have ht : t.length = gU x.length - 1 := by
    simp only [List.length_cons] at hu
    omega
  have hg : G q x.length ≤ t.length := by
    have h1 : G q x.length ≤ x.length ^ 2 := Nat.div_le_self _ _
    rw [ht, gU]
    omega
  have hcut : cutOf (stateB q d x (fl :: t)) =
      (t.take (G q x.length), t.drop (G q x.length)) := by
    simp [cutOf, stateB, arith, cutLists]
  have hE : accUb q d x (fl :: t) =
      (((px x).isSome && decide ((csz ((px x).getD d) + 1) ^ 2 ≤ rootLog q x.length)) &&
        (bif fl then allFalse t else
          ((decT2 (t.drop (G q x.length))).1 &&
            chk (bif ((px x).isSome &&
                    decide ((csz ((px x).getD d) + 1) ^ 2 ≤ rootLog q x.length))
                  then (px x).getD d else d,
                withGuess (t.take (G q x.length)) x,
                bif ((px x).isSome &&
                    decide ((csz ((px x).getD d) + 1) ^ 2 ≤ rootLog q x.length))
                  then x.length ^ 2 / (csz ((px x).getD d) + 1) ^ 2 else 0,
                (decT2 (t.drop (G q x.length))).2)))) := by
    simp only [accUb, E3, E2, hcut]
    rfl
  rw [hE]
  cases hpx : px x with
  | none =>
    simp only [Option.isSome_none, Bool.false_and]
    constructor
    · intro h
      cases h
    · rintro ⟨c, hc, -⟩
      rw [hpx] at hc
      cases hc
  | some c =>
    simp only [Option.isSome_some, Option.getD_some, Bool.true_and]
    by_cases hgd : (csz c + 1) ^ 2 ≤ rootLog q x.length
    · have hd : decide ((csz c + 1) ^ 2 ≤ rootLog q x.length) = true := decide_eq_true hgd
      rw [hd]
      simp only [cond_true, Bool.true_and]
      cases fl with
      | true =>
        simp only [cond_true]
        rw [allFalse_iff]
        constructor
        · intro hz
          exact ⟨c, hpx, hgd,
            Or.inl (congrArg (List.cons true) (List.eq_replicate_iff.mpr ⟨ht, hz⟩))⟩
        · rintro ⟨c', -, -, h | ⟨w, τ, z, -, -, h, -⟩⟩
          · rw [(List.cons.inj h).2]
            intro b hb
            exact List.eq_of_mem_replicate hb
          · exact absurd (List.cons.inj h).1 (by simp)
      | false =>
        simp only [cond_false]
        rw [Bool.and_eq_true]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h1
          have hτ2 : (decT2 (t.drop (G q x.length))).2 = τ := by simp [decT2, hτ]
          rw [hτ2] at h2
          obtain ⟨z, hz1, hz2⟩ := decT_some _ _ hτ
          have h2' : decide (Check c (withGuess (t.take (G q x.length)) x)
              (x.length ^ 2 / (csz c + 1) ^ 2) τ) = true := h2
          have hchk := of_decide_eq_true h2'
          refine ⟨c, hpx, hgd, Or.inr ⟨t.take (G q x.length), τ, z, ?_, hz2, ?_, hchk⟩⟩
          · rw [List.length_take]
            exact Nat.min_eq_left hg
          · congr 1
            rw [List.append_assoc, ← hz1, List.take_append_drop]
        · rintro ⟨c', hc', -, h | ⟨w, τ, z, hw, hz, h, hchk⟩⟩
          · exact absurd (List.cons.inj h).1 (by simp)
          · have hcc : c' = c := by
              rw [hpx] at hc'
              exact (Option.some.inj hc').symm
            subst hcc
            have ht' : t = w ++ (serT τ ++ z) := by
              rw [← List.append_assoc]
              exact (List.cons.inj h).2
            have htake : t.take (G q x.length) = w := by
              rw [ht']
              exact List.take_left' hw
            have hdrop : t.drop (G q x.length) = serT τ ++ z := by
              rw [ht']
              exact List.drop_left' hw
            have hdec : decT (serT τ ++ z) = some τ := decT_eq τ z hz
            have h2 : (decT2 (serT τ ++ z)).2 = τ := by simp [decT2, hdec]
            refine ⟨by rw [hdrop]; simp [decT2, hdec], ?_⟩
            rw [htake, hdrop, h2]
            exact decide_eq_true hchk
    · have hd : decide ((csz c + 1) ^ 2 ≤ rootLog q x.length) = false := decide_eq_false hgd
      rw [hd]
      simp only [Bool.false_and]
      constructor
      · intro h
        cases h
      · rintro ⟨c', hc', hg', -⟩
        have hcc : c' = c := by
          rw [hpx] at hc'
          exact (Option.some.inj hc').symm
        subst hcc
        exact absurd hg' hgd

/-! ## Linear-time pieces -/

theorem size_nat' (n : ℕ) : size n = 2 * n + 1 := by
  show size (List.replicate n () : Tally) = 2 * n + 1
  rw [size_tally, List.length_replicate]

theorem size_bits' (l : List Bool) : size l = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [size_cons, ih, size_bit, List.length_cons]
    omega

theorem easy_congr {X Y Y' : Type*} [Codec X] [Codec Y] [Codec Y'] {f : X → Y} {g : X → Y'}
    (h : Easy f) (e : ∀ x, send (f x) = send (g x)) : Easy g :=
  Task.conform h (fun _ => rfl) (fun _ => rfl) e

theorem easy_length : Easy (fun x : List Bool => x.length) := by
  have h : Easy (fun x : List Bool => x.map (fun _ => ())) := easy_map easy_id (Easy.const ())
  refine easy_congr h (fun x => ?_)
  show send (x.map fun _ => ()) = send (List.replicate x.length ())
  rw [List.map_const']

theorem easy_headD : Easy (fun l : List Bool => l.headD false) := by
  have h := Easy.listCase (X := Bool) (f := fun i : Bool × List Bool => i.1) false Easy.fst
  exact Task.conform h (fun _ => rfl) (fun _ => rfl) (fun l => by cases l <;> rfl)

theorem easy_tail : Easy (fun l : List Bool => l.tail) := by
  have h := Easy.listCase (X := Bool) (f := fun i : Bool × List Bool => i.2) ([] : List Bool)
    Easy.snd
  exact Task.conform h (fun _ => rfl) (fun _ => rfl) (fun l => by cases l <;> rfl)

theorem easy_and {X : Type*} [Codec X] {f g : X → Bool} (hf : Easy f) (hg : Easy g) :
    Easy (fun x => f x && g x) :=
  (hf.pair hg).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2))

theorem easy_bif {X Y : Type*} [Codec X] [Codec Y] {b : X → Bool} {f g : X → Y} (hb : Easy b)
    (hf : Easy f) (hg : Easy g) : Easy (fun x => bif b x then f x else g x) :=
  (hb.pair (hf.pair hg)).compose
    (Easy.ifst (f := fun i : Y × Y => i.2) (g := fun i : Y × Y => i.1) Easy.snd Easy.fst)

theorem easy_withGuess : Easy (fun i : List Bool × List Bool => withGuess i.1 i.2) := by
  have hb : Easy (fun b : Bool => [true, b]) := Easy.finite _
  have h : Easy (fun i : List Bool × List Bool =>
      (i.1.map (fun b => [true, b])).flatten ++ false :: i.2) :=
    easy_append (easy_flatten (easy_map Easy.fst hb))
      (((Easy.const false).pair Easy.snd).compose Easy.cons)
  exact easy_congr h (fun i => rfl)

theorem easy_allFalse : Easy allFalse :=
  (easy_map easy_id (Easy.finite (fun b : Bool => !b))).compose easy_all

theorem easy_serCode : Easy serCode := by
  have hcode : Easy (fun c : MCode => (c.nK, c.inp, c.sym0, c.sym1, c.init, c.table)) :=
    (Task.self (b := size) (p := send)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have s1 : Easy (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × List Entry => t.2) := Easy.snd
  have s2 : Easy (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × List Entry => t.2.2) := Easy.sndCompose s1
  have s3 : Easy (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × List Entry => t.2.2.2) := Easy.sndCompose s2
  have s4 : Easy (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × List Entry => t.2.2.2.2) := Easy.sndCompose s3
  have a1 : Easy (fun t : ℕ × ℕ × ℕ × ℕ × ℕ × List Entry => serN t.1) :=
    Easy.fst.compose easy_serN
  have a2 := (Easy.fstCompose s1).compose easy_serN
  have a3 := (Easy.fstCompose s2).compose easy_serN
  have a4 := (Easy.fstCompose s3).compose easy_serN
  have a5 := (Easy.fstCompose s4).compose easy_serN
  have a6 := (Easy.sndCompose s4).compose (easy_serL easy_serEntry)
  exact hcode.compose
    (easy_append a1 (easy_append a2 (easy_append a3 (easy_append a4 (easy_append a5 a6)))))

theorem easy_csz : Easy csz := easy_serCode.compose easy_length

theorem easy_E1 (d : MCode) (h1 : Easy unGuess) (h2 : Easy (px2 d)) : Easy (E1 d) := by
  have hx0 : Easy (fun y : List Bool => (unGuess y).2) := Easy.sndCompose h1
  have hu0 : Easy (fun y : List Bool => (unGuess y).1) := Easy.fstCompose h1
  have hp : Easy (fun y : List Bool => px2 d (unGuess y).2) := hx0.compose h2
  have hn : Easy (fun y : List Bool => (unGuess y).2.length) := hx0.compose easy_length
  have hs : Easy (fun y : List Bool => csz (px2 d (unGuess y).2).2) :=
    (Easy.sndCompose hp).compose easy_csz
  exact (hn.pair hs).pair (hp.pair (hu0.pair hx0))

theorem easy_E2 (d : MCode) (h5 : Easy decT2) : Easy (E2 d) := by
  have hg : Easy (fun s : S2 => s.1.2.1) := Easy.fstCompose (Easy.sndCompose Easy.fst)
  have hu : Easy (fun s : S2 => s.2.2.1) := Easy.fstCompose (Easy.sndCompose Easy.snd)
  have hx : Easy (fun s : S2 => s.2.2.2) := Easy.sndCompose (Easy.sndCompose Easy.snd)
  have ht : Easy (fun s : S2 => s.2.2.1.tail) := hu.compose easy_tail
  have hcut : Easy cutOf := easy_cut ((hg.compose easy_tally).pair ht)
  have hw : Easy (fun s : S2 => (cutOf s).1) := Easy.fstCompose hcut
  have hr : Easy (fun s : S2 => (cutOf s).2) := Easy.sndCompose hcut
  have hd2 : Easy (fun s : S2 => decT2 (cutOf s).2) := hr.compose h5
  have hok : Easy (fun s : S2 => s.2.1.1 && s.1.1) :=
    easy_and (Easy.fstCompose (Easy.fstCompose Easy.snd)) (Easy.fstCompose Easy.fst)
  have hc : Easy (fun s : S2 => s.2.1.2) := Easy.sndCompose (Easy.fstCompose Easy.snd)
  have hT : Easy (fun s : S2 => s.1.2.2) := Easy.sndCompose (Easy.sndCompose Easy.fst)
  have hc' : Easy (fun s : S2 => bif (s.2.1.1 && s.1.1) then s.2.1.2 else d) :=
    easy_bif hok hc (Easy.const d)
  have hT' : Easy (fun s : S2 => bif (s.2.1.1 && s.1.1) then s.1.2.2 else 0) :=
    easy_bif hok hT (Easy.const 0)
  have hy : Easy (fun s : S2 => withGuess (cutOf s).1 s.2.2.2) :=
    (hw.pair hx).compose easy_withGuess
  have hτ : Easy (fun s : S2 => (decT2 (cutOf s).2).2) := Easy.sndCompose hd2
  have hokT : Easy (fun s : S2 => (decT2 (cutOf s).2).1) := Easy.fstCompose hd2
  have hfl : Easy (fun s : S2 => s.2.2.1.headD false) := hu.compose easy_headD
  have haz : Easy (fun s : S2 => allFalse s.2.2.1.tail) := ht.compose easy_allFalse
  exact (hc'.pair (hy.pair (hT'.pair hτ))).pair (hok.pair (hfl.pair (haz.pair hokT)))

/-! ## The budget -/

theorem length_cut_le (q : ℕ) (d : MCode) (x u : List Bool) :
    (cutOf (stateB q d x u)).1.length ≤ G q x.length := by
  have h : (cutOf (stateB q d x u)).1 = u.tail.take (List.replicate (G q x.length) ()).length := rfl
  rw [h, List.length_replicate]
  exact List.length_take_le _ _

theorem csz_px2_le (d : MCode) (x : List Bool) : csz (px2 d x).2 ≤ x.length + csz d := by
  cases hpx : px x with
  | none =>
    simp only [px2, hpx, Option.getD_none]
    omega
  | some c =>
    obtain ⟨r, hr⟩ := px_some hpx
    have h := congrArg List.length hr
    rw [List.length_append] at h
    simp only [px2, hpx, Option.getD_some, csz]
    omega

theorem sq_le_of_le_add (s n k : ℕ) (h : s ≤ n + k) : s ^ 2 ≤ 4 * n ^ 2 + 4 * k ^ 2 := by
  rcases le_total n k with h1 | h1
  · have h2 : s ≤ 2 * k := by omega
    have h3 : s ^ 2 ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  · have h2 : s ≤ 2 * n := by omega
    have h3 : s ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
    omega

/-- The cost of the W1 check on the sanitized input, without the transcript term. -/
theorem check_core_bound (q : ℕ) (d : MCode) (h8 : ∀ c : MCode, size c ≤ 4 * csz c + 4)
    (x u : List Bool) :
    (size (E2 d (stateB q d x u)).1.1 + 1) ^ 2 *
        ((E2 d (stateB q d x u)).1.2.1.length + (E2 d (stateB q d x u)).1.2.2.1 + 1) ≤
      (175 + 3 * (size d + 1) ^ 2) * (x.length ^ 2 + 1) := by
  have hnn : x.length ≤ x.length ^ 2 := Nat.le_self_pow (by norm_num) _
  have hG : G q x.length ≤ x.length ^ 2 := Nat.div_le_self _ _
  have hw := length_cut_le q d x u
  have e1 : (E2 d (stateB q d x u)).1.1 =
      bif ((px2 d x).1 && (arith q (x.length, csz (px2 d x).2)).1) then (px2 d x).2 else d := rfl
  have e2 : (E2 d (stateB q d x u)).1.2.1 = withGuess (cutOf (stateB q d x u)).1 x := rfl
  have e3 : (E2 d (stateB q d x u)).1.2.2.1 =
      bif ((px2 d x).1 && (arith q (x.length, csz (px2 d x).2)).1)
        then x.length ^ 2 / (csz (px2 d x).2 + 1) ^ 2 else 0 := rfl
  rw [e1, e2, e3, length_withGuess]
  generalize (cutOf (stateB q d x u)).1.length = w at hw ⊢
  cases hok : ((px2 d x).1 && (arith q (x.length, csz (px2 d x).2)).1) with
  | false =>
    simp only [cond_false]
    have h1 : 2 * w + 1 + x.length + 0 + 1 ≤ 3 * (x.length ^ 2 + 1) := by omega
    calc (size d + 1) ^ 2 * (2 * w + 1 + x.length + 0 + 1)
        ≤ (size d + 1) ^ 2 * (3 * (x.length ^ 2 + 1)) := Nat.mul_le_mul_left _ h1
      _ = 3 * (size d + 1) ^ 2 * (x.length ^ 2 + 1) := by ring
      _ ≤ (175 + 3 * (size d + 1) ^ 2) * (x.length ^ 2 + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  | true =>
    simp only [cond_true]
    have hgd : (csz (px2 d x).2 + 1) ^ 2 ≤ rootLog q x.length := by
      have h : (arith q (x.length, csz (px2 d x).2)).1 = true := (Bool.and_eq_true_iff.mp hok).2
      exact of_decide_eq_true h
    have hc := h8 (px2 d x).2
    generalize csz (px2 d x).2 = s at hgd hc ⊢
    generalize size (px2 d x).2 = sc at hc ⊢
    have hρ1 : rootLog q x.length ≤ x.length + 1 := by
      have h1 := rootLog_le q x.length
      have h2 := Nat.log_le_self 2 x.length
      omega
    have hρg : rootLog q x.length * G q x.length ≤ x.length ^ 2 := by
      unfold G
      exact Nat.mul_div_le _ _
    have hT : (s + 1) ^ 2 * (x.length ^ 2 / (s + 1) ^ 2) ≤ x.length ^ 2 := Nat.mul_div_le _ _
    have hsc : (sc + 1) ^ 2 ≤ 25 * (s + 1) ^ 2 := by
      have h1 : sc + 1 ≤ 5 * (s + 1) := by omega
      have h2 : (sc + 1) ^ 2 ≤ (5 * (s + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      have h3 : (5 * (s + 1)) ^ 2 = 25 * (s + 1) ^ 2 := by ring
      omega
    -- (s+1)² (2w + n + 2) ≤ ρ (2g + n + 2) ≤ 2n² + (n+1)(n+2)
    have hA : (s + 1) ^ 2 * (2 * w + x.length + 2) ≤ 6 * x.length ^ 2 + 2 := by
      have h1 : (s + 1) ^ 2 * (2 * w + x.length + 2) ≤
          rootLog q x.length * (2 * G q x.length + x.length + 2) :=
        Nat.mul_le_mul hgd (by omega)
      have h2 : rootLog q x.length * (2 * G q x.length + x.length + 2) =
          2 * (rootLog q x.length * G q x.length) + rootLog q x.length * (x.length + 2) := by ring
      have h3 : rootLog q x.length * (x.length + 2) ≤ (x.length + 1) * (x.length + 2) :=
        Nat.mul_le_mul_right _ hρ1
      have h4 : (x.length + 1) * (x.length + 2) = x.length ^ 2 + 3 * x.length + 2 := by ring
      omega
    have hB : (s + 1) ^ 2 * (2 * w + 1 + x.length + x.length ^ 2 / (s + 1) ^ 2 + 1) ≤
        7 * x.length ^ 2 + 2 := by
      have h1 : (s + 1) ^ 2 * (2 * w + 1 + x.length + x.length ^ 2 / (s + 1) ^ 2 + 1) =
          (s + 1) ^ 2 * (2 * w + x.length + 2) +
            (s + 1) ^ 2 * (x.length ^ 2 / (s + 1) ^ 2) := by ring
      omega
    calc (sc + 1) ^ 2 * (2 * w + 1 + x.length + x.length ^ 2 / (s + 1) ^ 2 + 1)
        ≤ 25 * (s + 1) ^ 2 * (2 * w + 1 + x.length + x.length ^ 2 / (s + 1) ^ 2 + 1) :=
          Nat.mul_le_mul_right _ hsc
      _ = 25 * ((s + 1) ^ 2 * (2 * w + 1 + x.length + x.length ^ 2 / (s + 1) ^ 2 + 1)) := by ring
      _ ≤ 25 * (7 * x.length ^ 2 + 2) := Nat.mul_le_mul_left _ hB
      _ ≤ 175 * (x.length ^ 2 + 1) := by omega
      _ ≤ (175 + 3 * (size d + 1) ^ 2) * (x.length ^ 2 + 1) :=
          Nat.mul_le_mul_right _ (by omega)

/-- The constant of the universal verifier's budget. -/
def bigD (d : MCode) (C1 C2 : ℕ) : ℕ :=
  21 + (5 + 4 * csz d ^ 2) + (6 + 21 * C1) +
    (175 + 3 * (size d + 1) ^ 2 + C2 * (6 + 21 * C1)) + 9 + 1

theorem budget_bound (q : ℕ) (d : MCode) (C1 C2 : ℕ)
    (hC1 : ∀ y, size (E1 d y) ≤ C1 * size y) (hC2 : ∀ s, size (E2 d s) ≤ C2 * size s)
    (h8 : ∀ c : MCode, size c ≤ 4 * csz c + 4)
    (x u : List Bool) (hu : u.length = gU x.length) :
    size (withGuess u x) + (x.length ^ 2 + csz (px2 d x).2 ^ 2) + size (stateB q d x u) +
        checkBudget (E2 d (stateB q d x u)).1 +
        size (chk (E2 d (stateB q d x u)).1, (E2 d (stateB q d x u)).2) + 1 ≤
      bigD d C1 C2 * (x.length ^ 2 + 1) := by
  have hnn : x.length ≤ x.length ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY : size (withGuess u x) ≤ 21 * (x.length ^ 2 + 1) := by
    rw [size_bits', length_withGuess, hu, gU]
    omega
  have hs2 := sq_le_of_le_add _ _ _ (csz_px2_le d x)
  have hG : G q x.length ≤ x.length ^ 2 := Nat.div_le_self _ _
  have hTb : x.length ^ 2 / (csz (px2 d x).2 + 1) ^ 2 ≤ x.length ^ 2 := Nat.div_le_self _ _
  have hrest : size (px2 d x, u, x) ≤ C1 * size (withGuess u x) := by
    have h := hC1 (withGuess u x)
    have e : E1 d (withGuess u x) = ((x.length, csz (px2 d x).2), px2 d x, u, x) := by
      simp only [E1, unGuess_withGuess]
    rw [e] at h
    have h' : size (((x.length, csz (px2 d x).2), px2 d x, u, x) :
          (ℕ × ℕ) × (Bool × MCode) × List Bool × List Bool) =
        size (x.length, csz (px2 d x).2) + size (px2 d x, u, x) + 1 := rfl
    omega
  have hS : size (stateB q d x u) ≤ (6 + 21 * C1) * (x.length ^ 2 + 1) := by
    have h1 : size (stateB q d x u) =
        size (arith q (x.length, csz (px2 d x).2)) + size (px2 d x, u, x) + 1 := rfl
    have h2 : size (arith q (x.length, csz (px2 d x).2)) =
        2 * G q x.length + 2 * (x.length ^ 2 / (csz (px2 d x).2 + 1) ^ 2) + 5 := by
      simp only [arith, size_prod, size_bit, size_nat']
      omega
    have h3 : C1 * size (withGuess u x) ≤ C1 * (21 * (x.length ^ 2 + 1)) :=
      Nat.mul_le_mul_left _ hY
    have h4 : (6 + 21 * C1) * (x.length ^ 2 + 1) =
        6 * (x.length ^ 2 + 1) + C1 * (21 * (x.length ^ 2 + 1)) := by ring
    omega
  have hτ : size (E2 d (stateB q d x u)).1.2.2.2 ≤ C2 * ((6 + 21 * C1) * (x.length ^ 2 + 1)) := by
    have h := hC2 (stateB q d x u)
    have h' : size (E2 d (stateB q d x u)).1.2.2.2 ≤ size (E2 d (stateB q d x u)) := by
      simp only [size_prod]
      omega
    exact (h'.trans h).trans (Nat.mul_le_mul_left _ hS)
  have hX := check_core_bound q d h8 x u
  have hcb : checkBudget (E2 d (stateB q d x u)).1 =
      (size (E2 d (stateB q d x u)).1.1 + 1) ^ 2 *
        ((E2 d (stateB q d x u)).1.2.1.length + (E2 d (stateB q d x u)).1.2.2.1 + 1) +
      size (E2 d (stateB q d x u)).1.2.2.2 := rfl
  have h5 : size (chk (E2 d (stateB q d x u)).1, (E2 d (stateB q d x u)).2) ≤ 9 := by
    simp only [size_prod, size_bit]
    omega
  have hD : bigD d C1 C2 * (x.length ^ 2 + 1) =
      21 * (x.length ^ 2 + 1) + (5 + 4 * csz d ^ 2) * (x.length ^ 2 + 1) +
        (6 + 21 * C1) * (x.length ^ 2 + 1) +
        ((175 + 3 * (size d + 1) ^ 2) * (x.length ^ 2 + 1) +
          C2 * ((6 + 21 * C1) * (x.length ^ 2 + 1))) + 9 * (x.length ^ 2 + 1) +
        (x.length ^ 2 + 1) := by
    unfold bigD
    ring
  have h2 : x.length ^ 2 + csz (px2 d x).2 ^ 2 ≤ (5 + 4 * csz d ^ 2) * (x.length ^ 2 + 1) := by
    have e : (5 + 4 * csz d ^ 2) * (x.length ^ 2 + 1) =
        5 * x.length ^ 2 + 5 + 4 * csz d ^ 2 * x.length ^ 2 + 4 * csz d ^ 2 := by ring
    have : 0 ≤ 4 * csz d ^ 2 * x.length ^ 2 := Nat.zero_le _
    omega
  rw [hD, hcb]
  omega

/-! ## The task and the machine -/

/-- The inputs of the universal verifier: `(x, u)` with a guess of the right length. -/
abbrev Dom := {i : List Bool × List Bool // i.2.length = gU i.1.length}

open Classical in
/-- **The universal verifier as one task**, from the open pieces. -/
theorem accU_task (q : ℕ) (d : MCode)
    (h1 : Easy unGuess) (h2 : Easy (px2 d)) (h5 : Easy decT2)
    (h6 : Computes (fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) (arith q))
    (h7 : Task checkBudget send (fun i : MCode × List Bool × ℕ × List Entry =>
      send (decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2))))
    (h8 : ∀ c : MCode, size c ≤ 4 * csz c + 4) :
    Task (fun i : Dom => i.val.1.length ^ 2) (fun i => send (withGuess i.val.2 i.val.1))
      (fun i => send (decide (accU q i.val.1 i.val.2))) := by
  have hE1 := easy_E1 d h1 h2
  have hE2 := easy_E2 d h5
  obtain ⟨C1, hC1⟩ := hE1.length
  obtain ⟨C2, hC2⟩ := hE2.length
  have T1 : Task (fun i : Dom => size (withGuess i.val.2 i.val.1))
      (fun i => send (withGuess i.val.2 i.val.1))
      (fun i => Tree.fork (send (i.val.1.length, csz (px2 d i.val.1).2))
        (send (px2 d i.val.1, i.val.2, i.val.1))) :=
    Task.conform (Task.on hE1 (fun i : Dom => withGuess i.val.2 i.val.1)) (fun _ => rfl)
      (fun _ => rfl) (fun i => by
        show send (E1 d (withGuess i.val.2 i.val.1)) = _
        simp only [E1, unGuess_withGuess]
        rfl)
  have T2 : Task (fun i : Dom => i.val.1.length ^ 2 + csz (px2 d i.val.1).2 ^ 2)
      (fun i => Tree.fork (send (i.val.1.length, csz (px2 d i.val.1).2))
        (send (px2 d i.val.1, i.val.2, i.val.1)))
      (fun i => send (stateB q d i.val.1 i.val.2)) :=
    Task.left (Task.on h6 (fun i : Dom => (i.val.1.length, csz (px2 d i.val.1).2)))
      (fun i : Dom => send (px2 d i.val.1, i.val.2, i.val.1))
  have T3 : Task (fun i : Dom => size (stateB q d i.val.1 i.val.2))
      (fun i => send (stateB q d i.val.1 i.val.2))
      (fun i => Tree.fork (send (E2 d (stateB q d i.val.1 i.val.2)).1)
        (send (E2 d (stateB q d i.val.1 i.val.2)).2)) :=
    Task.on hE2 (fun i : Dom => stateB q d i.val.1 i.val.2)
  have T4 : Task (fun i : Dom => checkBudget (E2 d (stateB q d i.val.1 i.val.2)).1)
      (fun i => Tree.fork (send (E2 d (stateB q d i.val.1 i.val.2)).1)
        (send (E2 d (stateB q d i.val.1 i.val.2)).2))
      (fun i => send (chk (E2 d (stateB q d i.val.1 i.val.2)).1,
        (E2 d (stateB q d i.val.1 i.val.2)).2)) :=
    Task.left (Task.on h7 (fun i : Dom => (E2 d (stateB q d i.val.1 i.val.2)).1))
      (fun i : Dom => send (E2 d (stateB q d i.val.1 i.val.2)).2)
  have T5 : Task (fun i : Dom => size (chk (E2 d (stateB q d i.val.1 i.val.2)).1,
        (E2 d (stateB q d i.val.1 i.val.2)).2))
      (fun i => send (chk (E2 d (stateB q d i.val.1 i.val.2)).1,
        (E2 d (stateB q d i.val.1 i.val.2)).2))
      (fun i => send (accUb q d i.val.1 i.val.2)) :=
    Task.on (Easy.finite E3) (fun i : Dom => (chk (E2 d (stateB q d i.val.1 i.val.2)).1,
      (E2 d (stateB q d i.val.1 i.val.2)).2))
  have Tall := (((T1.compose T2).compose T3).compose T4).compose T5
  refine Task.conform (Task.bound Tall (bigD d C1 C2) (fun i => ?_)) (fun _ => rfl)
    (fun _ => rfl) (fun i => ?_)
  · exact budget_bound q d C1 C2 hC1 hC2 h8 i.val.1 i.val.2 i.property
  · congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact accUb_iff q d _ _ i.property

open Classical in
/-- From the task to the machine: `compile_task`, the model bridge, the time bound. -/
theorem accU_machine_of_task (q : ℕ)
    (h : Task (fun i : Dom => i.val.1.length ^ 2) (fun i => send (withGuess i.val.2 i.val.1))
      (fun i => send (decide (accU q i.val.1 i.val.2)))) :
    ∃ (U : C1Challenge.Machine) (b : ℕ), ∀ (x : List Bool) (u : Fin (gU x.length) → Bool),
      HaltsWithin U (withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
        (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length) := by
  obtain ⟨M, K, hM⟩ := compile_task (fun i : Dom => i.val.1.length ^ 2)
    (fun i => withGuess i.val.2 i.val.1) (fun i => decide (accU q i.val.1 i.val.2)) h
  refine ⟨ofOAI M, K * 11, fun x u => ?_⟩
  have hu : (List.ofFn u).length = gU x.length := List.length_ofFn
  have h1 := hM ⟨(x, List.ofFn u), hu⟩
  obtain ⟨t, ht, c, h2, h3, h4⟩ := haltsWithin_ofOAI M _ _ _ h1
  refine ⟨t, ht.trans ?_, c, h2, h3, h4⟩
  show K * ((withGuess (List.ofFn u) x).length + x.length ^ 2 + 1) ≤
    K * 11 * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length
  have hnn : x.length ≤ x.length ^ 2 := Nat.le_self_pow (by norm_num) _
  have hl : (withGuess (List.ofFn u) x).length + x.length ^ 2 + 1 ≤ 11 * (x.length ^ 2 + 1) := by
    rw [length_withGuess, hu, gU]
    omega
  calc K * ((withGuess (List.ofFn u) x).length + x.length ^ 2 + 1)
      ≤ K * (11 * (x.length ^ 2 + 1)) := Nat.mul_le_mul_left _ hl
    _ = K * 11 * (x.length ^ 2 + 1) := by ring
    _ ≤ _ := Nat.le_add_right _ _

open Classical in
/-- **`accU_machine` from the six open pieces** (the statement of `Hierarchy.accU_machine`). -/
theorem accU_machine_of (q : ℕ) (d : MCode)
    (h1 : Easy unGuess) (h2 : Easy (px2 d)) (h5 : Easy decT2)
    (h6 : Computes (fun i : ℕ × ℕ => i.1 ^ 2 + i.2 ^ 2) (arith q))
    (h7 : Task checkBudget send (fun i : MCode × List Bool × ℕ × List Entry =>
      send (decide (Check i.1 i.2.1 i.2.2.1 i.2.2.2))))
    (h8 : ∀ c : MCode, size c ≤ 4 * csz c + 4) :
    ∃ (U : C1Challenge.Machine) (b : ℕ), ∀ (x : List Bool) (u : Fin (gU x.length) → Bool),
      HaltsWithin U (withGuess (List.ofFn u) x) (decide (accU q x (List.ofFn u)))
        (b * (x.length ^ 2 + 1) + (withGuess (List.ofFn u) x).length) :=
  accU_machine_of_task q (accU_task q d h1 h2 h5 h6 h7 h8)

end P1Hier.UM
