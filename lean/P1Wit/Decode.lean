import P1Wit.Layout

/-!
# P1Wit.Decode: the readers invert the encoder (task P6)

Lane P1-lean-W2-P6. Uses only `P1Wit.Layout`.

* `decode_enc`: in the witness `enc D m F z`, the reader of every stored field returns the stored content
  (when every content fits into its field, `Fields.InRange`); one corollary per field family (`rdTrit_enc`, ...).
* `payload_enc`, `tail_enc`: the payload part is `z` followed by zeros.
* `enc_congr`, `enc_injective`: `enc` depends only on the stored fields, and determines them and `z`.
* `enc_dec` (reconstruction, for P9 uniqueness): a bit list of length `m` whose bits after `fixedLen + zl` are all
  `false` is `enc` of its own fields `dec D u` and of its payload of length `zl`.
* `enc_length`, `ofFn_encFn`: the witness has length `m`, and `List.ofFn (encFn D m F z) = enc D m F z`.
-/

namespace P1Wit

/-! ## Index arithmetic -/

theorem idx_lt {y b k c : ℕ} (hy : y < b) (hk : k < c) : y * c + k < b * c := by
  calc y * c + k < y * c + c := by omega
    _ = (y + 1) * c := by ring
    _ ≤ b * c := Nat.mul_le_mul_right _ hy

theorem idx_div {y k c : ℕ} (hk : k < c) : (y * c + k) / c = y := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < c), Nat.div_eq_of_lt hk, Nat.zero_add]

theorem idx_mod {y k c : ℕ} (hk : k < c) : (y * c + k) % c = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

theorem div_mul_add_mod (i c : ℕ) : i / c * c + i % c = i := by
  rw [Nat.mul_comm]; exact Nat.div_add_mod i c

/-! ## Section kinds -/

namespace Dims

variable (D : Dims)

theorem kind_trit : D.kind secTrit = .trit := by simp [kind, secTrit]
theorem kind_start : D.kind secStart = .start := by simp [kind, secStart]
theorem kind_prev : D.kind secPrev = .prevOwn := by simp [kind, secPrev]
theorem kind_next : D.kind secNext = .nextOwn := by simp [kind, secNext]
theorem kind_guess : D.kind secGuess = .guess := by simp [kind, secGuess]

theorem kind_secLev {ℓ : ℕ} (k : Mem) (h : ℓ ≤ D.top) : D.kind (secLev ℓ k) = .lev ℓ k := by
  have hk := k.toNat_lt
  have e1 : (secLev ℓ k - 5) / 12 = ℓ := by unfold secLev; omega
  have e2 : (secLev ℓ k - 5) % 12 = k.toNat := by unfold secLev; omega
  have e3 : secLev ℓ k < 5 + 12 * (D.top + 1) := by unfold secLev; omega
  have n0 : ¬ secLev ℓ k = 0 := by unfold secLev; omega
  have n1 : ¬ secLev ℓ k = 1 := by unfold secLev; omega
  have n2 : ¬ secLev ℓ k = 2 := by unfold secLev; omega
  have n3 : ¬ secLev ℓ k = 3 := by unfold secLev; omega
  have n4 : ¬ secLev ℓ k = 4 := by unfold secLev; omega
  unfold kind
  simp only [n0, n1, n2, n3, n4, e3, e1, e2, Mem.ofCode_toNat, ↓reduceIte]

theorem kind_Omega : D.kind D.secOmega = .Omega := by
  unfold kind secOmega
  split_ifs <;> first | rfl | omega

theorem kind_chain : D.kind D.secChain = .chain := by
  unfold kind secChain
  split_ifs <;> first | rfl | omega

/-! ### From the kind back to the section number -/

theorem eq_of_kind_trit {s : ℕ} (h : D.kind s = .trit) : s = secTrit := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secTrit; omega)

theorem eq_of_kind_start {s : ℕ} (h : D.kind s = .start) : s = secStart := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secStart; omega)

theorem eq_of_kind_prev {s : ℕ} (h : D.kind s = .prevOwn) : s = secPrev := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secPrev; omega)

theorem eq_of_kind_next {s : ℕ} (h : D.kind s = .nextOwn) : s = secNext := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secNext; omega)

theorem eq_of_kind_guess {s : ℕ} (h : D.kind s = .guess) : s = secGuess := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secGuess; omega)

theorem eq_of_kind_Omega {s : ℕ} (h : D.kind s = .Omega) : s = D.secOmega := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secOmega; omega)

theorem eq_of_kind_chain {s : ℕ} (h : D.kind s = .chain) : s = D.secChain := by
  unfold kind at h
  split_ifs at h <;> (try cases h) <;> (unfold secChain; omega)

theorem eq_of_kind_lev {s ℓ : ℕ} {k : Mem} (h : D.kind s = .lev ℓ k) : s = secLev ℓ k := by
  unfold kind at h
  split_ifs at h with h0 h1 h2 h3 h4 h5 <;> (try cases h)
  unfold secLev
  rw [Mem.toNat_ofNat _ (Nat.mod_lt _ (by norm_num))]
  omega

theorem secLev_lt_nSec {ℓ : ℕ} (k : Mem) (h : ℓ ≤ D.top) : secLev ℓ k < D.nSec := by
  have := k.toNat_lt
  unfold secLev nSec; omega

theorem secOmega_lt_nSec : D.secOmega < D.nSec := by unfold secOmega nSec; omega
theorem secChain_lt_nSec : D.secChain < D.nSec := by unfold secChain nSec; omega

theorem count_secLev {ℓ : ℕ} (k : Mem) (h : ℓ ≤ D.top) : D.count (secLev ℓ k) = (D.lv ℓ).count k := by
  simp only [count, D.kind_secLev k h]

theorem width_secLev {ℓ : ℕ} (k : Mem) (h : ℓ ≤ D.top) :
    D.width (secLev ℓ k) = D.levWidth (D.lv ℓ) k := by
  simp only [width, D.kind_secLev k h]

end Dims

/-! ## The generic reading lemma -/

theorem fixedBits_length (D : Dims) (F : Fields) : (fixedBits D F).length = D.fixedLen :=
  fixedCat_length _ _ _ _

theorem readField_enc_mod (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) {s i : ℕ} (hs : s < D.nSec)
    (hi : i < D.count s) : readField D (enc D m F z) s i = F.val D s i % 2 ^ D.width s := by
  unfold readField enc fixedBits Dims.off
  rw [List.append_assoc]
  exact read_fixedCat D.count D.width (F.val D) hs hi _

/-- **P6 `decode_enc`.** Every stored field is read back exactly. -/
theorem decode_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D) {s i : ℕ}
    (hs : s < D.nSec) (hi : i < D.count s) : readField D (enc D m F z) s i = F.val D s i := by
  rw [readField_enc_mod D m F z hs hi, Nat.mod_eq_of_lt (hF s hs i hi)]

/-! ## One reader per field family -/

section Readers

variable (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D)
include hF

theorem rdTrit_enc {i ρ : ℕ} (hi : i < D.I * D.N) (hρ : ρ < D.r) : rdTrit D (enc D m F z) i ρ = F.trit i ρ := by
  have hc : i * D.r + ρ < D.count secTrit := by
    simp only [Dims.count, D.kind_trit]; exact idx_lt hi hρ
  unfold rdTrit
  rw [decode_enc D m F z hF (by unfold Dims.nSec secTrit; omega) hc]
  simp only [Fields.val, D.kind_trit, idx_div hρ, idx_mod hρ]

theorem rdStart_enc {ι ρ : ℕ} (hι : ι < D.I) (hρ : ρ < D.r) : rdStart D (enc D m F z) ι ρ = F.start ι ρ := by
  have hc : ι * D.r + ρ < D.count secStart := by
    simp only [Dims.count, D.kind_start]; exact idx_lt hι hρ
  unfold rdStart
  rw [decode_enc D m F z hF (by unfold Dims.nSec secStart; omega) hc]
  simp only [Fields.val, D.kind_start, idx_div hρ, idx_mod hρ]

theorem rdPrev_enc {ι ρ δ : ℕ} (hι : ι < D.I) (hρ : ρ < D.r) (hδ : δ < 3) :
    rdPrev D (enc D m F z) ι ρ δ = F.prevOwn ι ρ δ := by
  have hc : (ι * D.r + ρ) * 3 + δ < D.count secPrev := by
    simp only [Dims.count, D.kind_prev]; exact idx_lt (idx_lt hι hρ) hδ
  unfold rdPrev
  rw [decode_enc D m F z hF (by unfold Dims.nSec secPrev; omega) hc]
  simp only [Fields.val, D.kind_prev, idx_div hδ, idx_mod hδ, idx_div hρ, idx_mod hρ]

theorem rdNext_enc {ι ρ δ : ℕ} (hι : ι < D.I) (hρ : ρ < D.r) (hδ : δ < 3) :
    rdNext D (enc D m F z) ι ρ δ = F.nextOwn ι ρ δ := by
  have hc : (ι * D.r + ρ) * 3 + δ < D.count secNext := by
    simp only [Dims.count, D.kind_next]; exact idx_lt (idx_lt hι hρ) hδ
  unfold rdNext
  rw [decode_enc D m F z hF (by unfold Dims.nSec secNext; omega) hc]
  simp only [Fields.val, D.kind_next, idx_div hδ, idx_mod hδ, idx_div hρ, idx_mod hρ]

theorem rdGuess_enc {Q : ℕ} (hQ : Q < D.nGB) : rdGuess D (enc D m F z) Q = F.guess Q := by
  have hc : Q < D.count secGuess := by simp only [Dims.count, D.kind_guess]; exact hQ
  unfold rdGuess
  rw [decode_enc D m F z hF (by unfold Dims.nSec secGuess; omega) hc]
  simp only [Fields.val, D.kind_guess]

variable {ℓ : ℕ} (hℓ : ℓ ≤ D.top)
include hℓ

theorem rdLayout_enc (hs : (D.lv ℓ).shrink = true) : rdLayout D (enc D m F z) ℓ = F.layout ℓ := by
  have hc : 0 < D.count (secLev ℓ .layout) := by
    rw [D.count_secLev _ hℓ]; simp [LevelDims.count, hs]
  unfold rdLayout
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal]

theorem rd_slot_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) (c : Mem)
    (hc : c = .outAddr ∨ c = .outDisp ∨ c = .outFar ∨ c = .inAddr ∨ c = .inDisp ∨ c = .inFar) :
    readField D (enc D m F z) (secLev ℓ c) (y * (D.lv ℓ).slots + k) =
      F.levVal (D.lv ℓ) ℓ c (y * (D.lv ℓ).slots + k) := by
  have hc' : y * (D.lv ℓ).slots + k < D.count (secLev ℓ c) := by
    rw [D.count_secLev _ hℓ]
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> exact idx_lt hy hk
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc']
  simp only [Fields.val, D.kind_secLev _ hℓ]

theorem rdOutAddr_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdOutAddr D (enc D m F z) ℓ y k = F.outAddr ℓ y k := by
  unfold rdOutAddr
  rw [rd_slot_enc D m F z hF hℓ hy hk .outAddr (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdOutDisp_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdOutDisp D (enc D m F z) ℓ y k = F.outDisp ℓ y k := by
  unfold rdOutDisp
  rw [rd_slot_enc D m F z hF hℓ hy hk .outDisp (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdOutFar_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdOutFar D (enc D m F z) ℓ y k = F.outFar ℓ y k := by
  unfold rdOutFar
  rw [rd_slot_enc D m F z hF hℓ hy hk .outFar (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdInAddr_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdInAddr D (enc D m F z) ℓ y k = F.inAddr ℓ y k := by
  unfold rdInAddr
  rw [rd_slot_enc D m F z hF hℓ hy hk .inAddr (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdInDisp_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdInDisp D (enc D m F z) ℓ y k = F.inDisp ℓ y k := by
  unfold rdInDisp
  rw [rd_slot_enc D m F z hF hℓ hy hk .inDisp (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdInFar_enc {y k : ℕ} (hy : y < (D.lv ℓ).bases) (hk : k < (D.lv ℓ).slots) :
    rdInFar D (enc D m F z) ℓ y k = F.inFar ℓ y k := by
  unfold rdInFar
  rw [rd_slot_enc D m F z hF hℓ hy hk .inFar (by simp)]
  simp only [Fields.levVal, idx_div hk, idx_mod hk]

theorem rdWidth_enc {y l k : ℕ} (hy : y < (D.lv ℓ).bases) (hl : l < (D.lv ℓ).lanes)
    (hk : k < (D.lv ℓ).slots) : rdWidth D (enc D m F z) ℓ y l k = F.width ℓ y l k := by
  have hc : (y * (D.lv ℓ).lanes + l) * (D.lv ℓ).slots + k < D.count (secLev ℓ .width) := by
    rw [D.count_secLev _ hℓ]; exact idx_lt (idx_lt hy hl) hk
  unfold rdWidth
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal, idx_div hk, idx_mod hk, idx_div hl, idx_mod hl]

theorem rdColour_enc (hs : (D.lv ℓ).shrink = true) {y : ℕ} (hy : y < (D.lv ℓ).bases) :
    rdColour D (enc D m F z) ℓ y = F.colour ℓ y := by
  have hc : y < D.count (secLev ℓ .colour) := by
    rw [D.count_secLev _ hℓ]; simp only [LevelDims.count, hs, ↓reduceIte]; exact hy
  unfold rdColour
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal]

theorem rdOffset_enc (hs : (D.lv ℓ).shrink = true) {y : ℕ} (hy : y < (D.lv ℓ).bases) :
    rdOffset D (enc D m F z) ℓ y = F.offset ℓ y := by
  have hc : y < D.count (secLev ℓ .offset) := by
    rw [D.count_secLev _ hℓ]; simp only [LevelDims.count, hs, ↓reduceIte]; exact hy
  unfold rdOffset
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal]

theorem rdEnergy_enc (hs : (D.lv ℓ).shrink = true) {y c : ℕ} (hy : y < (D.lv ℓ).bases) (hc2 : c < 2) :
    rdEnergy D (enc D m F z) ℓ y c = F.energy ℓ y c := by
  have hc : y * 2 + c < D.count (secLev ℓ .energy) := by
    rw [D.count_secLev _ hℓ]; simp only [LevelDims.count, hs, ↓reduceIte]; exact idx_lt hy hc2
  unfold rdEnergy
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal, idx_div hc2, idx_mod hc2]

theorem rdTerms_enc {y key c : ℕ} (hy : y < (D.lv ℓ).bases) (hkey : key < (D.lv ℓ).termKeys)
    (hc2 : c < (D.lv ℓ).termArity + 1) : rdTerms D (enc D m F z) ℓ y key c = F.terms ℓ y key c := by
  have hc : (y * (D.lv ℓ).termKeys + key) * ((D.lv ℓ).termArity + 1) + c < D.count (secLev ℓ .terms) := by
    rw [D.count_secLev _ hℓ]; exact idx_lt (idx_lt hy hkey) hc2
  unfold rdTerms
  rw [decode_enc D m F z hF (D.secLev_lt_nSec _ hℓ) hc]
  simp only [Fields.val, D.kind_secLev _ hℓ, Fields.levVal, idx_div hc2, idx_mod hc2, idx_div hkey,
    idx_mod hkey]

end Readers

theorem rdOmega_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D) {y : ℕ}
    (hy : y < (D.lv D.top).bases) : rdOmega D (enc D m F z) y = F.Omega y := by
  have hc : y < D.count D.secOmega := by simp only [Dims.count, D.kind_Omega]; exact hy
  unfold rdOmega
  rw [decode_enc D m F z hF D.secOmega_lt_nSec hc]
  simp only [Fields.val, D.kind_Omega]

theorem rdChain_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (hF : F.InRange D) {j : ℕ}
    (hj : j < D.chainLen) : rdChain D (enc D m F z) j = F.chain j := by
  have hc : j < D.count D.secChain := by simp only [Dims.count, D.kind_chain]; exact hj
  unfold rdChain
  rw [decode_enc D m F z hF D.secChain_lt_nSec hc]
  simp only [Fields.val, D.kind_chain]

/-! ## The payload part -/

theorem drop_fixedLen_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) :
    rdPayload D (enc D m F z) = z ++ List.replicate (m - (D.fixedLen + z.length)) false := by
  unfold rdPayload enc
  rw [List.append_assoc, List.drop_left' (fixedBits_length D F)]

theorem payload_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) :
    (rdPayload D (enc D m F z)).take z.length = z := by
  rw [drop_fixedLen_enc, List.take_left' rfl]

theorem tail_enc (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) :
    ∀ b ∈ (enc D m F z).drop (D.fixedLen + z.length), b = false := by
  intro b hb
  have e : (enc D m F z).drop (D.fixedLen + z.length) = List.replicate (m - (D.fixedLen + z.length)) false := by
    unfold enc
    rw [← List.drop_drop, List.append_assoc, List.drop_left' (fixedBits_length D F), List.drop_left' rfl]
  rw [e] at hb
  exact List.eq_of_mem_replicate hb

/-! ## Length, congruence, injectivity -/

theorem enc_length (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (h : D.fixedLen + z.length ≤ m) :
    (enc D m F z).length = m := by
  unfold enc
  simp only [List.length_append, fixedBits_length, List.length_replicate]
  omega

theorem enc_congr (D : Dims) (m : ℕ) {F F' : Fields} (h : F.Agree D F') (z : List Bool) :
    enc D m F z = enc D m F' z := by
  unfold enc fixedBits
  rw [fixedCat_congr D.count D.width (F.val D) (F'.val D) D.nSec h]

/-- **P6 `enc_injective`.** The witness determines every stored field (for contents in range) and the payload
(of the given length; the length of `z` is a function of the stored widths, `ℓ(σ, ι)`). -/
theorem enc_injective {D : Dims} {m : ℕ} {F F' : Fields} {z z' : List Bool}
    (hF : F.InRange D) (hF' : F'.InRange D) (hz : z.length = z'.length)
    (h : enc D m F z = enc D m F' z') : F.Agree D F' ∧ z = z' := by
  refine ⟨fun s hs i hi => ?_, ?_⟩
  · rw [← decode_enc D m F z hF hs hi, ← decode_enc D m F' z' hF' hs hi, h]
  · rw [← payload_enc D m F z, ← payload_enc D m F' z', h, hz]

/-! ## Reconstruction (for the uniqueness count, task P9) -/

/-- Reading every field of `u` gives the field contents `dec D u`. -/
theorem dec_val (D : Dims) (u : List Bool) {s i : ℕ} (hi : i < D.count s) :
    (dec D u).val D s i = readField D u s i := by
  rcases hk : D.kind s with _ | _ | _ | _ | _ | ⟨ℓ, k⟩ | _ | _ | _
  · rw [D.eq_of_kind_trit hk]
    simp only [Fields.val, D.kind_trit, dec, rdTrit, div_mul_add_mod]
  · rw [D.eq_of_kind_start hk]
    simp only [Fields.val, D.kind_start, dec, rdStart, div_mul_add_mod]
  · rw [D.eq_of_kind_prev hk]
    simp only [Fields.val, D.kind_prev, dec, rdPrev, div_mul_add_mod]
  · rw [D.eq_of_kind_next hk]
    simp only [Fields.val, D.kind_next, dec, rdNext, div_mul_add_mod]
  · rw [D.eq_of_kind_guess hk]
    simp only [Fields.val, D.kind_guess, dec, rdGuess]
  · simp only [Fields.val, hk]
    have hs := D.eq_of_kind_lev hk
    subst hs
    cases k with
    | layout =>
      have hi0 : i = 0 := by
        simp only [Dims.count, hk, LevelDims.count] at hi
        split at hi <;> omega
      subst hi0
      rfl
    | outAddr => simp only [Fields.levVal, dec, rdOutAddr, div_mul_add_mod]
    | outDisp => simp only [Fields.levVal, dec, rdOutDisp, div_mul_add_mod]
    | outFar => simp only [Fields.levVal, dec, rdOutFar, div_mul_add_mod]
    | inAddr => simp only [Fields.levVal, dec, rdInAddr, div_mul_add_mod]
    | inDisp => simp only [Fields.levVal, dec, rdInDisp, div_mul_add_mod]
    | inFar => simp only [Fields.levVal, dec, rdInFar, div_mul_add_mod]
    | width => simp only [Fields.levVal, dec, rdWidth, div_mul_add_mod]
    | colour => simp only [Fields.levVal, dec, rdColour]
    | offset => simp only [Fields.levVal, dec, rdOffset]
    | energy => simp only [Fields.levVal, dec, rdEnergy, div_mul_add_mod]
    | terms => simp only [Fields.levVal, dec, rdTerms, div_mul_add_mod]
  · rw [D.eq_of_kind_Omega hk]
    simp only [Fields.val, D.kind_Omega, dec, rdOmega]
  · rw [D.eq_of_kind_chain hk]
    simp only [Fields.val, D.kind_chain, dec, rdChain]
  · have h0 : D.count s = 0 := by simp only [Dims.count, hk]
    omega

theorem fixedBits_dec (D : Dims) (u : List Bool) (h : D.fixedLen ≤ u.length) :
    fixedBits D (dec D u) = u.take D.fixedLen := by
  unfold fixedBits
  rw [fixedCat_congr D.count D.width ((dec D u).val D)
    (fun s i => readNat u (offAt D.count D.width s + i * D.width s) (D.width s)) D.nSec
    (fun s _ i hi => dec_val D u hi)]
  exact fixedCat_read u D.count D.width D.nSec h

/-- **Reconstruction.** A bit list of length `m` whose bits after `fixedLen + zl` are all `false` is the witness of
its own fields and of its payload of length `zl`. -/
theorem enc_dec (D : Dims) (m zl : ℕ) (u : List Bool) (hu : u.length = m) (hm : D.fixedLen + zl ≤ m)
    (hz : ∀ b ∈ u.drop (D.fixedLen + zl), b = false) :
    u = enc D m (dec D u) ((rdPayload D u).take zl) := by
  have hlen : ((rdPayload D u).take zl).length = zl := by
    unfold rdPayload; simp only [List.length_take, List.length_drop]; omega
  have h3 : u.drop (D.fixedLen + zl) = List.replicate (m - (D.fixedLen + zl)) false := by
    rw [List.eq_replicate_iff]
    exact ⟨by simp only [List.length_drop]; omega, hz⟩
  have h4 : (u.drop D.fixedLen).drop zl = u.drop (D.fixedLen + zl) := by rw [List.drop_drop]
  unfold enc
  rw [fixedBits_dec D u (by omega), hlen, ← h3, ← h4]
  unfold rdPayload
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem getD_false_eq : ∀ (l : List Bool) (i : ℕ) (h : i < l.length), l.getD i false = l[i]
  | [], i, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: bs, i + 1, h => getD_false_eq bs i (by simp only [List.length_cons] at h; omega)

/-- The witness as a function `Fin m → Bool` spells the list `enc D m F z`. -/
theorem ofFn_encFn (D : Dims) (m : ℕ) (F : Fields) (z : List Bool) (h : D.fixedLen + z.length ≤ m) :
    List.ofFn (encFn D m F z) = enc D m F z := by
  have hl := enc_length D m F z h
  apply List.ext_getElem
  · rw [List.length_ofFn, hl]
  · intro i h1 h2
    simp only [List.getElem_ofFn, encFn]
    exact getD_false_eq _ i h2

/-! ## The function form `Fin m → Bool` (the witnesses of `P1Int.LemmaP` and `P1Int.P11.CountSetup`) -/

theorem getD_ofFn {m : ℕ} (u : Fin m → Bool) (i : Fin m) : (List.ofFn u).getD i false = u i := by
  rw [getD_false_eq _ i (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

/-- **P6 `enc_injective`, function form.** -/
theorem encFn_injective {D : Dims} {m : ℕ} {F F' : Fields} {z z' : List Bool}
    (hF : F.InRange D) (hF' : F'.InRange D) (hz : z.length = z'.length)
    (hm : D.fixedLen + z.length ≤ m) (h : encFn D m F z = encFn D m F' z') : F.Agree D F' ∧ z = z' := by
  apply enc_injective hF hF' hz
  rw [← ofFn_encFn D m F z hm, ← ofFn_encFn D m F' z' (by rw [← hz]; exact hm), h]

/-- **Reconstruction, function form.** A witness `u : Fin m → Bool` whose bits after `fixedLen + zl` are all
`false` is the witness of its own fields and of its payload of length `zl`. -/
theorem encFn_dec (D : Dims) {m : ℕ} (zl : ℕ) (u : Fin m → Bool) (hm : D.fixedLen + zl ≤ m)
    (hz : ∀ i : Fin m, D.fixedLen + zl ≤ i.val → u i = false) :
    u = encFn D m (dec D (List.ofFn u)) ((rdPayload D (List.ofFn u)).take zl) := by
  have hz' : ∀ b ∈ (List.ofFn u).drop (D.fixedLen + zl), b = false := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
    rw [List.getElem_drop, List.getElem_ofFn] at hjb
    rw [← hjb]
    have hj' : D.fixedLen + zl + j < m := by
      simp only [List.length_drop, List.length_ofFn] at hj; omega
    exact hz ⟨_, hj'⟩ (by simp)
  have e := enc_dec D m zl (List.ofFn u) (List.length_ofFn) hm hz'
  funext i
  unfold encFn
  rw [← e, getD_ofFn]

/-! ## Agreement on the stored fields gives agreement of σ, ι and the chain (for the tuple injectivity) -/

theorem agree_trit {D : Dims} {F F' : Fields} (hF : F.InRange D) (hF' : F'.InRange D) (h : F.Agree D F')
    {i ρ : ℕ} (hi : i < D.I * D.N) (hρ : ρ < D.r) : F.trit i ρ = F'.trit i ρ := by
  rw [← rdTrit_enc D 0 F [] hF hi hρ, ← rdTrit_enc D 0 F' [] hF' hi hρ, enc_congr D 0 h]

theorem agree_terms {D : Dims} {F F' : Fields} (hF : F.InRange D) (hF' : F'.InRange D) (h : F.Agree D F')
    {ℓ y key c : ℕ} (hℓ : ℓ ≤ D.top) (hy : y < (D.lv ℓ).bases) (hkey : key < (D.lv ℓ).termKeys)
    (hc : c < (D.lv ℓ).termArity + 1) : F.terms ℓ y key c = F'.terms ℓ y key c := by
  rw [← rdTerms_enc D 0 F [] hF hℓ hy hkey hc, ← rdTerms_enc D 0 F' [] hF' hℓ hy hkey hc, enc_congr D 0 h]

theorem agree_chain {D : Dims} {F F' : Fields} (hF : F.InRange D) (hF' : F'.InRange D) (h : F.Agree D F')
    {j : ℕ} (hj : j < D.chainLen) : F.chain j = F'.chain j := by
  rw [← rdChain_enc D 0 F [] hF hj, ← rdChain_enc D 0 F' [] hF' hj, enc_congr D 0 h]

/-- **Tuple injectivity (glue for `P1Int.P11.CountSetup.hinj`).** If the typed codes `fields t` of a tuple `t`
fit their fields, the payload fits, the stored fields determine the payload length (`ℓ(σ, ι)` from the widths)
and the stored fields with the payload determine the tuple, then `t ↦ encFn D m (fields t) (pay t)` is
injective. -/
theorem encFn_comp_injective {T : Type*} (D : Dims) (m : ℕ) (fields : T → Fields) (pay : T → List Bool)
    (hR : ∀ t, (fields t).InRange D) (hm : ∀ t, D.fixedLen + (pay t).length ≤ m)
    (hlen : ∀ t t', (fields t).Agree D (fields t') → (pay t).length = (pay t').length)
    (hsep : ∀ t t', (fields t).Agree D (fields t') → pay t = pay t' → t = t') :
    Function.Injective (fun t => encFn D m (fields t) (pay t)) := by
  intro t t' h
  have h' : encFn D m (fields t) (pay t) = encFn D m (fields t') (pay t') := h
  have e : enc D m (fields t) (pay t) = enc D m (fields t') (pay t') := by
    rw [← ofFn_encFn D m _ _ (hm t), ← ofFn_encFn D m _ _ (hm t'), h']
  have hA : (fields t).Agree D (fields t') := fun s hs i hi => by
    rw [← decode_enc D m _ _ (hR t) hs hi, ← decode_enc D m _ _ (hR t') hs hi, e]
  exact hsep t t' hA (enc_injective (hR t) (hR t') (hlen t t' hA) e).2

end P1Wit
