import P1SolGreedy.C5Words
import P1ChkFinal.BatchLink
import P1Dispatch.TaskBridge

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

theorem slots_le_size_levelRow (D : Dims) (ℓ : ℕ) :
    (D.lv ℓ).slots ≤ size (levelRow D ℓ) := by
  simp only [levelRow, size_prod, size_tally, tally_length]
  omega

theorem c5RootRequests_width (D : Dims) (ℓ Y : ℕ) :
    ∀ r ∈ c5RootRequests D ℓ Y, P1Batch.bval r.2 ≤ size (levelRow D ℓ) := by
  intro r h
  unfold c5RootRequests at h
  rcases List.mem_cons.mp h with rfl | hs
  · simp only [fieldReq, bval_bin]
    exact width_le_size_levelRow D ℓ .colour
  · rcases List.mem_append.mp hs with ho | hi
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ho
      simp only [fieldReq, bval_bin]
      exact width_le_size_levelRow D ℓ .outAddr
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hi
      simp only [fieldReq, bval_bin]
      exact width_le_size_levelRow D ℓ .inAddr

theorem c5ColourRequests_width (D : Dims) (ℓ Y : ℕ) (zs : List ℕ) :
    ∀ r ∈ c5ColourRequests D ℓ Y zs, P1Batch.bval r.2 ≤ size (levelRow D ℓ) := by
  intro r h
  obtain ⟨Z, _, rfl⟩ := List.mem_map.mp h
  simp only [fieldReq, bval_bin]
  exact width_le_size_levelRow D ℓ .colour

def c5Bound (q : C5Context) (u : List Bool) : Prop :=
  let s := c5Next (q, (c5Root q).map (P1Batch.fetch u))
  P1Batch.total (c5Root q) ≤ 3 * (size q + 1) ^ 2 ∧
    P1Batch.total (c5Colours s) ≤ 3 * (size q + 1) ^ 2

/-- Both rounds have a quadratic size bound from the public format, independent of the witness bits. -/
theorem c5Totals_at (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y : NumberWord)
    (hlen : P1Batch.bval len = u.length) :
    c5Bound (len, true, Y, levelRow D ℓ) u := by
  let q : C5Context := (len, true, Y, levelRow D ℓ)
  let root := c5RootRequests D ℓ (P1Batch.bval Y)
  let zs := (root.map (P1Batch.fetch u)).tail
  let s := c5Next (q, (c5Root q).map (P1Batch.fetch u))
  change P1Batch.total (c5Root q) ≤ _ ∧ P1Batch.total (c5Colours s) ≤ _
  have hn : size (levelRow D ℓ) ≤ size q + 1 := by
    simp only [q, size_prod]
    omega
  have hd := (slots_le_size_levelRow D ℓ).trans hn
  have hfac : 1 + 2 * (D.lv ℓ).slots ≤ 3 * (size q + 1) := by omega
  have hrLen : root.length = 1 + 2 * (D.lv ℓ).slots := by
    simp only [root, c5RootRequests, List.length_cons, List.length_append, List.length_map, List.length_range]
    omega
  have hzsLen : zs.length = 2 * (D.lv ℓ).slots := by
    simp only [zs, List.length_tail, List.length_map, hrLen]
    omega
  have hf : (c5Root q).map (P1Batch.fetch u) = root.map (P1Batch.fetch u) :=
    c5Root_at _ _ _ _ _ hlen
  constructor
  · change P1Batch.total (clipRequests (len, c5RawRoot (true, Y, levelRow D ℓ))) ≤ _
    rw [clipRequests_total, total_of_requestNumbers (c5RawRoot_values D ℓ Y)]
    calc
      P1Batch.total root ≤ root.length * size (levelRow D ℓ) :=
        total_le_of_width_le _ _ (c5RootRequests_width D ℓ _)
      _ ≤ (3 * (size q + 1)) * (size q + 1) := Nat.mul_le_mul (hrLen.symm ▸ hfac) hn
      _ = 3 * (size q + 1) ^ 2 := by rw [pow_two, Nat.mul_assoc]
  · have hz : s.2.2 = zs := by simp only [s, c5Next, hf, zs]
    change P1Batch.total (clipRequests (len,
      colourRequests ((rowSection .colour (levelRow D ℓ), Y), s.2.2))) ≤ _
    rw [clipRequests_total, hz, total_of_requestNumbers (colourRequests_values D ℓ Y zs)]
    let cs := c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)
    have hcs : cs.length ≤ 3 * (size q + 1) := by
      simp only [cs, c5ColourRequests, List.length_map, hzsLen]
      omega
    calc
      P1Batch.total cs ≤ cs.length * size (levelRow D ℓ) :=
        total_le_of_width_le _ _ (c5ColourRequests_width D ℓ _ _)
      _ ≤ (3 * (size q + 1)) * (size q + 1) := Nat.mul_le_mul hcs hn
      _ = 3 * (size q + 1) ^ 2 := by rw [pow_two, Nat.mul_assoc]

theorem c5Totals (D : Dims) (u : List Bool) (m : ℕ) (i : NumberWord) (hm : m = u.length) :
    c5Bound (setupC5 (fmtGreedy D m, i)) u := by
  let base := setupBase (fmtGreedy D m, i)
  let q := setupC5 (fmtGreedy D m, i)
  change c5Bound q u
  obtain ⟨hv, _, hr⟩ := setupBase_spec D m i
  change base.1 = true ↔ ShrinkIdx D (P1Batch.bval i) at hv
  change base.2.2 = _ at hr
  by_cases h : ShrinkIdx D (P1Batch.bval i)
  · rw [ite_eq_left h.1] at hr
    have eq : q = (bin m, true, base.2.1, levelRow D (P1Batch.bval i % 2 ^ levBits D)) :=
      Prod.ext rfl (Prod.ext (hv.mpr h) (Prod.ext rfl hr))
    have hlen : P1Batch.bval (bin m) = u.length := (bval_bin m).trans hm
    exact eq.symm ▸ c5Totals_at D u (P1Batch.bval i % 2 ^ levBits D) (bin m) base.2.1 hlen
  · unfold c5Bound
    have hf : base.1 = false := Bool.eq_false_iff.mpr fun hh => h (hv.mp hh)
    have hq : q.2.1 = false := hf
    simp only [c5Root, c5RawRoot, hq, Bool.cond_false, clipRequests, Code.polyPush, List.map_nil,
      c5Colours, c5Next, List.tail_nil, colourRequests, P1Batch.total, List.sum_nil, Nat.zero_le, and_self]

end P1SolGreedy.SolDemand

namespace P1SolGreedy

open SolDemand Classical

set_option maxHeartbeats 1200000 in
/-- D8 Task for C5. Every data-dependent read is clipped to the public witness length. -/
theorem taskC5 (dims : ℕ → Dims) (M K : ℕ → ℕ)
    (hb : BatchHyp) (hl : LenHyp) (hf : FmtHypGreedy dims M) :
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val) (fun p => send p.val)
      (fun p => send (decide (C5fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2)))) := by
  let setup (z : IndexWord) := setupC5 (formatIndex dims M z)
  have hp : Poly setup := (formatIndex_poly dims M hf).compose setupC5_poly
  let q (p : QDom M K) := setup (SetupIdx p)
  let u (p : QDom M K) := p.val.2.1
  let s (p : QDom M K) := c5Next (q p, (c5Root (q p)).map (P1Batch.fetch (u p)))
  have hs : Dom smallSize (fun p : QDom M K => size (q p)) :=
    (hp.length.map SetupIdx).sub index_size
  have hsmall : Dom smallSize (fun p : QDom M K => 3 * (size (q p) + 1) ^ 2) :=
    (Dom.const _ 3).mul ((hs.add (Dom.const _ 1)).pow 2)
  have hlen (p : QDom M K) : P1Batch.bval (q p).1 = (u p).length := by
    change P1Batch.bval (bin (M (P1Batch.bval (bin p.val.1.length)))) = _
    rw [bval_bin, bval_bin]
    exact p.property.1.symm
  have totals (p : QDom M K) :
      P1Batch.total (c5Root (q p)) ≤ 3 * (size (q p) + 1) ^ 2 ∧
      P1Batch.total (c5Colours (s p)) ≤ 3 * (size (q p) + 1) ^ 2 := by
    have hq : q p = setupC5 (fmtGreedy (dims p.val.1.length) (M p.val.1.length), p.val.2.2) := by
      simp only [q, setup, SetupIdx, formatIndex, bval_bin]
    change c5Bound (q p) (u p)
    exact hq.symm ▸ c5Totals (dims p.val.1.length) (u p) (M p.val.1.length) p.val.2.2 p.property.1.symm
  have ha₁ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ c5Root (q p)) :
      P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  have ha₂ (p : QDom M K) (r : P1Batch.Req) (hr : r ∈ c5Colours (s p)) :
      P1Batch.bval r.1 ≤ (u p).length :=
    (clipRequests_bound _ _ hr).trans_eq (hlen p)
  let ck (p : QDom M K) := decide (C5fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))
  have hc (p : QDom M K) : ck p = decideC5 (s p, (c5Colours (s p)).map (P1Batch.fetch (u p))) :=
    (c5Evaluate_correct dims M p.val.1 p.val.2.1 p.val.2.2 p.property.1).symm
  obtain ⟨t, ht, T⟩ := prepareWitness (M := M) (K := K) hl setup hp
  obtain ⟨b, hb', T'⟩ := twoBatchCheck hb (fun p : QDom M K => send p.val) u q smallSize _
    c5Root c5Next c5Colours decideC5 ck T c5Root_poly c5Next_poly c5Colours_poly decideC5_poly
    hs (hsmall.mono (fun p => (totals p).1)) ha₁ (hsmall.mono (fun p => (totals p).2)) ha₂ hc
  apply pack_budget (E := 5) (ht.add hb')
  exact T'.bound 1 (fun p => by dsimp only [u]; omega)

/-- Raw-register form for D8 family 4. -/
theorem progC5 (dims : ℕ → Dims) (M K : ℕ → ℕ) (hl : LenHyp) (hf : FmtHypGreedy dims M) :
    ∃ (Rc : Prog Ltr) (c C : ℕ), ∀ p : QDom M K,
      P1Int.ProgAnswers Rc P1Dispatch.answer (P1Int.inputRegs Ltr.bit p.val.1 p.val.2.1 p.val.2.2)
        (decide (C5fam dims p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))) (C * (budget c p.val + 1)) := by
  obtain ⟨c, h⟩ := taskC5 dims M K batchHyp hl hf
  obtain ⟨Rc, C, hRc⟩ := P1Dispatch.ofTask_tight' (fun p : QDom M K => p.val)
    (fun p => budget c p.val) (fun x u i => decide (C5fam dims x u i)) h
  exact ⟨Rc, c, C, hRc⟩

#print axioms taskC5
#print axioms progC5

end P1SolGreedy
