import P1SolFactor.HalfPacking
import P1Net.Glue

namespace P1SolFactor.SolHalf

open OAI.DepthThreeLowerBound OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression P1Net
open scoped Classical

noncomputable section

variable (V : FiniteMultiTapeMachine) (B I : ℕ) [NeZero I] {h a : ℕ}
  (σ : Fin (I * 2 ^ h) → V.K → Fin 3) (ha : 4 ≤ 2 ^ a)

local notation "X" => rnState V B I σ ha
local notation "Wx" => strWidth V B
local notation "Wt" => tupWidth V B
local notation "Vertex" => Fin I × Loc V.K h

theorem slotWidth_out_netWidth (v : Vertex) (s : Fin 4) (lane : BitWord h) :
    slotWidth X ((v, false), lane) false (s.castLE ha) = netWidth I σ Wx Wx Wt ((v, s), lane) :=
  (preGraph I σ).regularize_width ha (netWidth I σ Wx Wx Wt) v s lane

theorem slotWidth_out_mated {v v' : Vertex} {s s' : Fin 4}
    (hm : netMate I σ (v, s) = some (v', s')) (lane : BitWord h) :
    slotWidth X ((v, false), lane) false (s.castLE ha) = baseWidth Wx Wx Wt v.2 s := by
  rw [slotWidth_out_netWidth]
  simp only [netWidth, hm, Option.some_ne_none, ite_false]

theorem slotWidth_in_mated {v v' : Vertex} {s s' : Fin 4}
    (hm : netMate I σ (v, s) = some (v', s')) (lane : BitWord h) :
    slotWidth X ((v, false), lane) true (s.castLE ha) = baseWidth Wx Wx Wt v'.2 s' := by
  have he := inEdge_regularize_mate (preGraph I σ) ha (netWidth I σ Wx Wx Wt) hm false lane
  change edgeWidth X (inEdge X ((v, false), lane) (s.castLE ha)) = _
  rw [he]
  exact slotWidth_out_mated V B I σ ha (netMate_symm I σ hm) _

theorem slotWidth_in_unmated (v : Vertex) (s : Fin 4)
    (hm : netMate I σ (v, s) = none) (lane : BitWord h) :
    slotWidth X ((v, false), lane) true (s.castLE ha) = 0 := by
  let G := preGraph I σ
  have hG : G.mate (v, s) = none := hm
  have hs : (X).slots.base.target.symm ((v, false), s.castLE ha) = ((v, true), s.castLE ha) := by
    change G.slotMap ha ((v, false), s.castLE ha) = _
    simp only [PreGraph.slotMap, PreGraph.slot4_castLE, hG, Bool.not_false]
  change edgeWidth X (inEdge X ((v, false), lane) (s.castLE ha)) = _
  simp only [inEdge, hs]
  exact G.regularize_width_twin ha (netWidth I σ Wx Wx Wt) v (s.castLE ha) _

private theorem baseWidth_le_string (l : Loc V.K h) (s : Fin 4)
    (hcenter : l = .tabC → s ≠ 0) (hpath : ∀ c, l = .tabP c → s ≠ 1) :
    baseWidth Wx Wx Wt l s ≤ Wx := by
  cases l with
  | tabC => simp [baseWidth, hcenter rfl]
  | tabP c =>
    have h1 := hpath c rfl
    cases c <;> simp [baseWidth, h1] <;> split <;> omega
  | portIn k d => simp [baseWidth]; split <;> omega
  | portOut k d => simp [baseWidth]; split <;> omega
  | rt k c π => simp [baseWidth]; split <;> omega
  | st c π => simp [baseWidth]; split <;> omega
  | eIn => simp [baseWidth]; split <;> omega
  | eOut => simp [baseWidth]; split <;> omega

theorem slotWidth_out_le_string (v : Vertex) (s : Fin 4) (lane : BitWord h)
    (hcenter : v.2 = .tabC → s ≠ 0) (hpath : ∀ c, v.2 = .tabP c → s ≠ 1) :
    slotWidth X ((v, false), lane) false (s.castLE ha) ≤ Wx := by
  rw [slotWidth_out_netWidth]
  unfold netWidth
  split
  · exact Nat.zero_le _
  · exact baseWidth_le_string V B v.2 s hcenter hpath

/-- Tuple payloads can enter a site only through slot zero of a table path. -/
theorem slotWidth_in_le_string (v : Vertex) (s : Fin 4) (lane : BitWord h)
    (hinput : ∀ c, v.2 = .tabP c → s ≠ 0) :
    slotWidth X ((v, false), lane) true (s.castLE ha) ≤ Wx := by
  cases hm : netMate I σ (v, s) with
  | none =>
    rw [slotWidth_in_unmated V B I σ ha v s hm lane]
    exact Nat.zero_le _
  | some q =>
    obtain ⟨⟨ι', l'⟩, s'⟩ := q
    rw [slotWidth_in_mated V B I σ ha hm lane]
    apply baseWidth_le_string
    · intro hloc hslot
      change l' = .tabC at hloc
      subst l'
      subst s'
      have hp := netMate_symm I σ hm
      have he : (((ι', .tabP (firstExt V.K)), 0) : Vertex × Fin 4) = (v, s) := by
        simpa [netMate, locMate] using hp
      exact hinput _ (congrArg (fun p : Vertex × Fin 4 => p.1.2) he).symm (congrArg Prod.snd he).symm
    · intro c hloc hslot
      change l' = .tabP c at hloc
      subst l'
      subst s'
      have hp := netMate_symm I σ hm
      cases hd : nextExt c with
      | none => simp [netMate, locMate, hd, interMate] at hp
      | some d =>
        have he : (((ι', .tabP d), 0) : Vertex × Fin 4) = (v, s) := by
          simpa [netMate, locMate, hd] using hp
        exact hinput _ (congrArg (fun p : Vertex × Fin 4 => p.1.2) he).symm (congrArg Prod.snd he).symm

theorem center_slot_width (ι : Fin I) (lane : BitWord h) :
    slotWidth X (((ι, .tabC), false), lane) false ((0 : Fin 4).castLE ha) = Wt := by
  have hm : netMate I σ (((ι, .tabC), 0) : Vertex × Fin 4) = some ((ι, .tabP (firstExt V.K)), 0) := by
    simp [netMate, locMate]
  rw [slotWidth_out_mated V B I σ ha hm lane]
  simp [baseWidth]

theorem pin_slot_width (ι : Fin I) (k : V.K) (δ : Fin 3) (lane : BitWord h) :
    slotWidth X (((ι, .portIn k δ), false), lane) false ((0 : Fin 4).castLE ha) = Wx := by
  have hm : netMate I σ (((ι, .portIn k δ), 0) : Vertex × Fin 4) = some ((ι, .rt k (rcol0 h) (code3 δ)), 2) := by
    simp [netMate, locMate]
  rw [slotWidth_out_mated V B I σ ha hm lane]
  simp [baseWidth]

theorem path_tuple_slot_width (ι : Fin I) (c : Ext V.K) (lane : BitWord h) :
    slotWidth X (((ι, .tabP c), false), lane) true ((0 : Fin 4).castLE ha) = Wt := by
  cases hp : prevExt c with
  | none =>
    have hm : netMate I σ (((ι, .tabP c), 0) : Vertex × Fin 4) = some ((ι, .tabC), 0) := by
      simp [netMate, locMate, hp]
    rw [slotWidth_in_mated V B I σ ha hm lane]
    simp [baseWidth]
  | some d =>
    have hm : netMate I σ (((ι, .tabP c), 0) : Vertex × Fin 4) = some ((ι, .tabP d), 1) := by
      simp [netMate, locMate, hp]
    rw [slotWidth_in_mated V B I σ ha hm lane]
    simp [baseWidth]

end

end P1SolFactor.SolHalf
