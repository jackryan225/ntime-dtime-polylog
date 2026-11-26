import P1SolGreedy.GreedyReaders
import P1SolGreedy.C5Reads

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code
open P1Wit P1ChkGreedy P1ChkFinal

namespace P1SolGreedy.SolDemand

abbrev C5Context := NumberWord × BaseQuery
abbrev C5State := C5Context × NumberWord × List NumberWord

def setupC5 (p : PublicFmt × NumberWord) : C5Context :=
  (p.1.2.1, setupBase p)

theorem setupC5_poly : Poly setupC5 := by
  unfold setupC5
  have h := setupBase_poly
  fun_prop

/-- Read one numbered slot from a section given the binary index of slot zero. -/
def slotRequest (p : (P1Batch.Req × NumberWord) × NumberWord) : P1Batch.Req :=
  fieldWords (p.1.1, Bits.add (p.1.2, p.2))

@[fun_prop] theorem slotRequest_poly : Poly slotRequest := by
  unfold slotRequest
  fun_prop

def slotRequests (p : (P1Batch.Req × NumberWord) × List NumberWord) : List P1Batch.Req :=
  Code.polyPush slotRequest p

@[fun_prop] theorem slotRequests_poly : Poly slotRequests := Poly.push (([], []), []) [] slotRequest_poly

def c5RawRoot (q : BaseQuery) : List P1Batch.Req :=
  let Y := q.2.1
  let r := q.2.2
  let first := Carry.times0 (Y, r.2.2.1)
  let ports := wordRange r.2.2.2.1
  bif q.1 then
    fieldWords (rowSection .colour r, Y) ::
      (slotRequests ((rowSection .outAddr r, first), ports) ++
        slotRequests ((rowSection .inAddr r, first), ports))
  else []

@[fun_prop] theorem c5RawRoot_poly : Poly c5RawRoot := by
  unfold c5RawRoot
  dsimp only
  fun_prop

def c5Root (q : C5Context) : List P1Batch.Req := clipRequests (q.1, c5RawRoot q.2)

theorem c5Root_poly : Poly c5Root := by unfold c5Root; fun_prop

theorem c5RawRoot_values (D : Dims) (ℓ : ℕ) (Y : NumberWord) :
    (c5RawRoot (true, Y, levelRow D ℓ)).map requestNumbers =
      (c5RootRequests D ℓ (P1Batch.bval Y)).map requestNumbers := by
  have hw : (levelRow D ℓ).2.2.2.1 = tally (D.lv ℓ).slots := rfl
  have hs : (levelRow D ℓ).2.2.1 = bin (D.lv ℓ).slots := rfl
  have hr (m : Mem) :
      (slotRequests ((rowSection m (levelRow D ℓ), Carry.times0 (Y, (levelRow D ℓ).2.2.1)),
        wordRange (levelRow D ℓ).2.2.2.1)).map requestNumbers =
      ((List.range (D.lv ℓ).slots).map fun k =>
        fieldReq D (secLev ℓ m) (P1Batch.bval Y * (D.lv ℓ).slots + k)).map requestNumbers := by
    rw [hw, wordRange_tally, hs]
    simp only [slotRequests, Code.polyPush, List.map_map, Function.comp_def]
    congr 1
    funext k
    simp only [slotRequest, requestNumbers_rowField, bval_add, bval_mul, bval_born, bval_bin]
  simp only [c5RawRoot, c5RootRequests, Bool.cond_true, List.map_cons, List.map_append,
    requestNumbers_rowField, hr]

theorem tailPoly {T : Type} [Codec T] : Poly (List.tail : List T → List T) := by
  have h : (List.tail : List T → List T) = (fun l =>
      List.casesOn (motive := fun _ => List T) l [] (fun _ t => t)) := by
    funext l
    cases l <;> rfl
  rw [h]
  exact (Easy.listCase (X := T) ([] : List T) Easy.snd).poly

def c5Next (p : C5Context × List NumberWord) : C5State :=
  (p.1, p.2.headD [], p.2.tail)

theorem c5Next_poly : Poly c5Next := by
  unfold c5Next
  exact Easy.fst.poly.pair ((Easy.snd.poly.compose (Code.Iter.leader ([] : NumberWord)).poly).pair
    (Easy.snd.poly.compose tailPoly))

def colourRequest (p : (P1Batch.Req × NumberWord) × NumberWord) : P1Batch.Req :=
  fieldWords (p.1.1, minNumber (p.2, p.1.2))

@[fun_prop] theorem colourRequest_poly : Poly colourRequest := by unfold colourRequest; fun_prop

def colourRequests (p : (P1Batch.Req × NumberWord) × List NumberWord) : List P1Batch.Req :=
  Code.polyPush colourRequest p

@[fun_prop] theorem colourRequests_poly : Poly colourRequests :=
  Poly.push (([], []), []) [] colourRequest_poly

def c5Colours (s : C5State) : List P1Batch.Req :=
  let q := s.1.2
  clipRequests (s.1.1, colourRequests ((rowSection .colour q.2.2, q.2.1), s.2.2))

theorem c5Colours_poly : Poly c5Colours := by
  unfold c5Colours
  dsimp only
  fun_prop

theorem colourRequests_values (D : Dims) (ℓ : ℕ) (Y : NumberWord) (zs : List NumberWord) :
    (colourRequests ((rowSection .colour (levelRow D ℓ), Y), zs)).map requestNumbers =
      (c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)).map requestNumbers := by
  simp only [colourRequests, Code.polyPush, c5ColourRequests, List.map_map, Function.comp_def,
    colourRequest, requestNumbers_rowField, minNumber_value]

def maskedColour (p : (NumberWord × NumberWord) × (NumberWord × NumberWord)) : NumberWord :=
  bif Carry.lt_ (p.2.1, p.1.1) then
    (bif Carry.lt_ (p.2.2, p.1.2) then p.2.2 else [])
  else []

@[fun_prop] theorem maskedColour_poly : Poly maskedColour := by unfold maskedColour; fun_prop

def maskColours (p : (NumberWord × NumberWord) × List (NumberWord × NumberWord)) : List NumberWord :=
  Code.polyPush maskedColour p

@[fun_prop] theorem maskColours_poly : Poly maskColours := Poly.push ([], []) ([], []) maskedColour_poly

@[fun_prop] theorem zipNumberWords_poly : Poly (Code.zipFair ([] : NumberWord) ([] : NumberWord)) :=
  (Code.easy_zip _ _).poly

def decideC5 (p : C5State × List NumberWord) : Bool :=
  let q := p.1.1.2
  let r := q.2.2
  let cap := true :: r.2.2.1
  bif q.1 then
    leastMissingWords (p.1.2.1, cap,
      maskColours ((q.2.1, cap), Code.zipFair [] [] (p.1.2.2, p.2)),
      wordRange r.2.2.2.2.1)
  else true

theorem decideC5_poly : Poly decideC5 := by
  have h := leastMissingWords_poly
  unfold decideC5
  dsimp only
  fun_prop

theorem bval_colourCap (D : Dims) (ℓ : ℕ) :
    P1Batch.bval (true :: (levelRow D ℓ).2.2.1) = 2 * (D.lv ℓ).slots + 1 := by
  change 1 + 2 * P1Batch.bval (bin (D.lv ℓ).slots) = _
  rw [bval_bin, Nat.add_comm]

theorem c5_forbidden_bval (D : Dims) (u : List Bool) (ℓ : ℕ) (Y : NumberWord)
    (zs : List NumberWord) :
    let cap := true :: (levelRow D ℓ).2.2.1
    let colours := (c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)).map (P1Batch.fetch u)
    (maskColours ((Y, cap), Code.zipFair [] [] (zs, colours))).map P1Batch.bval =
      (zs.map P1Batch.bval).map (mcol D u ℓ (D.lv ℓ).slots (P1Batch.bval Y)) := by
  let f (Z : NumberWord) := P1Batch.fetch u (fieldReq D (secLev ℓ .colour)
    (min (P1Batch.bval Z) (P1Batch.bval Y)))
  have hf := Code.fair (id : NumberWord → NumberWord) f zs [] []
  simp only [List.map_id, id_eq] at hf
  have hcolour : (c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)).map (P1Batch.fetch u) =
      zs.map f := by
    simp only [c5ColourRequests, List.map_map, Function.comp_def, f]
  dsimp only
  rw [hcolour, hf]
  simp only [maskColours, Code.polyPush, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro Z _
  unfold maskedColour mcol
  rw [less_spec]
  by_cases h : P1Batch.bval Z < P1Batch.bval Y
  · have hv : P1Batch.bval (f Z) = rdColour D u ℓ (P1Batch.bval Z) := by
      rw [bval_bitsVal]
      dsimp only [f]
      rw [← readField_eq, min_eq_left h.le]
      rfl
    simp only [h, decide_true, Bool.cond_true, less_spec, bval_colourCap, hv, ite_true]
    by_cases hc : rdColour D u ℓ (P1Batch.bval Z) < 2 * (D.lv ℓ).slots + 1
    · simp only [hc, decide_true, Bool.cond_true, ite_true, hv]
    · simp only [hc, decide_false, Bool.cond_false, ite_false, P1Batch.bval]
  · simp only [h, decide_false, Bool.cond_false, ite_false, P1Batch.bval]

theorem c5Root_at (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y : NumberWord)
    (hlen : P1Batch.bval len = u.length) :
    (c5Root (len, true, Y, levelRow D ℓ)).map (P1Batch.fetch u) =
      (c5RootRequests D ℓ (P1Batch.bval Y)).map (P1Batch.fetch u) := by
  unfold c5Root
  rw [clipRequests_fetch _ _ hlen]
  exact fetches_of_requestNumbers _ (c5RawRoot_values D ℓ Y)

theorem c5Colours_at (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y col : NumberWord)
    (zs : List NumberWord) (hlen : P1Batch.bval len = u.length) :
    (c5Colours ((len, true, Y, levelRow D ℓ), col, zs)).map (P1Batch.fetch u) =
      (c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)).map (P1Batch.fetch u) := by
  unfold c5Colours
  rw [clipRequests_fetch _ _ hlen]
  exact fetches_of_requestNumbers _ (colourRequests_values D ℓ Y zs)

def c5Evaluate (q : C5Context) (u : List Bool) : Bool :=
  let s := c5Next (q, (c5Root q).map (P1Batch.fetch u))
  decideC5 (s, (c5Colours s).map (P1Batch.fetch u))

theorem c5Evaluate_at (D : Dims) (u : List Bool) (ℓ : ℕ) (len Y : NumberWord)
    (hlen : P1Batch.bval len = u.length) :
    c5Evaluate (len, true, Y, levelRow D ℓ) u = true ↔ C5chk D u ℓ (P1Batch.bval Y) := by
  let q : C5Context := (len, true, Y, levelRow D ℓ)
  let root := (c5RootRequests D ℓ (P1Batch.bval Y)).map (P1Batch.fetch u)
  let col := root.headD []
  let zs := root.tail
  have hr : (c5Root q).map (P1Batch.fetch u) = root := c5Root_at _ _ _ _ _ hlen
  have hraw := c5_root_reads D u ℓ (P1Batch.bval Y)
  have hc : P1Batch.bval col = rdColour D u ℓ (P1Batch.bval Y) := by
    rw [bval_bitsVal]
    exact congrArg Prod.fst hraw
  have hz : zs.map P1Batch.bval =
      ((List.range (D.lv ℓ).slots).map fun k => rdOutAddr D u ℓ (P1Batch.bval Y) k) ++
      ((List.range (D.lv ℓ).slots).map fun k => rdInAddr D u ℓ (P1Batch.bval Y) k) := by
    calc
      zs.map P1Batch.bval = zs.map bitsVal := List.map_congr_left (fun w _ => bval_bitsVal w)
      _ = _ := by
        have h := congrArg Prod.snd hraw
        simpa only [c5RootDecode, root, zs] using h
  let colours := (c5ColourRequests D ℓ (P1Batch.bval Y) (zs.map P1Batch.bval)).map (P1Batch.fetch u)
  let cap := true :: (levelRow D ℓ).2.2.1
  let candidates := wordRange (levelRow D ℓ).2.2.2.2.1
  let forbidden := maskColours ((Y, cap), Code.zipFair [] [] (zs, colours))
  have hforbid : forbidden.map P1Batch.bval = c5vals D u ℓ (P1Batch.bval Y) := by
    change (maskColours ((Y, cap), Code.zipFair [] [] (zs, colours))).map P1Batch.bval = _
    rw [c5_forbidden_bval, hz]
    simp only [c5vals, List.map_append, List.map_map, Function.comp_def]
  have hcap : P1Batch.bval cap = 2 * (D.lv ℓ).slots + 1 := bval_colourCap D ℓ
  have hcomplete (k : ℕ) (hk : k < P1Batch.bval cap) : k ∈ candidates.map P1Batch.bval := by
    change k ∈ (wordRange (tally (2 * (D.lv ℓ).slots + 1))).map P1Batch.bval
    rw [wordRange_tally, List.map_map]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr (hcap ▸ hk), bval_born k⟩
  change c5Evaluate q u = true ↔ _
  unfold c5Evaluate
  rw [hr]
  change decideC5 ((q, col, zs), (c5Colours (q, col, zs)).map (P1Batch.fetch u)) = true ↔ _
  rw [c5Colours_at D u ℓ len Y col zs hlen]
  change leastMissingWords (col, cap, forbidden, candidates) = true ↔ _
  rw [leastMissingWords_spec _ _ _ _ hcomplete, hc, hcap, hforbid]
  rfl

open Classical in
theorem c5Evaluate_correct (dims : ℕ → Dims) (M : ℕ → ℕ) (x u i : List Bool)
    (hlen : u.length = M x.length) :
    c5Evaluate (setupC5 (formatIndex dims M (bin x.length, i))) u =
      decide (C5fam dims x u (P1Batch.bval i)) := by
  let D := dims x.length
  let m := M x.length
  let q := setupBase (fmtGreedy D m, i)
  let ℓ := P1Batch.bval i % 2 ^ levBits D
  let Y := P1Batch.bval i / 2 ^ levBits D
  let len := bin m
  have hctx : setupC5 (formatIndex dims M (bin x.length, i)) = (len, q) := by
    simp only [setupC5, formatIndex, bval_bin, D, m, len, q, fmtGreedy]
  obtain ⟨hv, hY, hp⟩ := setupBase_spec D m i
  change q.1 = true ↔ ShrinkIdx D (P1Batch.bval i) at hv
  change P1Batch.bval q.2.1 = Y at hY
  change q.2.2 = (if ℓ ≤ D.top then levelRow D ℓ else defaultRow) at hp
  rw [hctx, Bool.eq_iff_iff, decide_eq_true_eq]
  by_cases h : ShrinkIdx D (P1Batch.bval i)
  · have hflag := hv.mpr h
    rw [ite_eq_left h.1] at hp
    have he : q = (true, q.2.1, levelRow D ℓ) := Prod.ext hflag (Prod.ext rfl hp)
    conv_lhs => rw [he]
    rw [c5Evaluate_at _ _ _ _ _ (by rw [bval_bin, hlen]), hY]
    change C5chk D u ℓ Y ↔ ShrinkIdx D (P1Batch.bval i) → C5chk D u ℓ Y
    exact ⟨fun h₅ _ => h₅, fun h₅ => h₅ h⟩
  · have hflag : q.1 = false := Bool.eq_false_iff.mpr fun hh => h (hv.mp hh)
    have hm : c5Evaluate (len, q) u = true := by
      simp only [c5Evaluate, decideC5, c5Next, hflag, Bool.cond_false]
    exact ⟨fun _ h' => (h h').elim, fun _ => hm⟩

end P1SolGreedy.SolDemand
