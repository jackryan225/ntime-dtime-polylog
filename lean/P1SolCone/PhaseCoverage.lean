import P1SolCone.PhaseWalk

namespace P1SolCone.SolCone

open OAI.Computability.VPVNP OAI.Computability.VPVNP.Compression
open P1Wit P1ChkFinal

theorem walkAddresses_mono {f g : ℕ → List ℕ} {xs ys : List ℕ}
    (h : xs ⊆ ys) (hfg : ∀ z, f z ⊆ g z) (r : ℕ) :
    walkAddresses f xs r ⊆ walkAddresses g ys r := by
  induction r with
  | zero => exact h
  | succ r ih =>
    intro q hq
    simp only [walkAddresses, List.mem_append, List.mem_flatMap] at hq ⊢
    rcases hq with e | ⟨x,e,n⟩
    · exact Or.inl (ih e)
    · exact Or.inr ⟨x,ih e,hfg x n⟩

theorem walkAddresses_prefix (f : ℕ → List ℕ) (roots : List ℕ) {r s : ℕ} (h : r ≤ s) :
    walkAddresses f roots r ⊆ walkAddresses f roots s := by
  induction h with
  | refl => exact List.Subset.refl _
  | step _ ih =>
    intro a ha
    exact List.mem_append_left _ (ih ha)

theorem rawWalk_covers_neighbor (f : ℕ → List ℕ) (roots : List ℕ) {x : ℕ} (hx : x ∈ roots)
    {r : ℕ} (hr : 0 < r) : ∀ y ∈ x :: f x, y ∈ walkAddresses f roots r := by
  intro y hy
  apply walkAddresses_prefix f roots hr
  rcases List.mem_cons.mp hy with rfl | hn
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x,hx,hn⟩)

theorem bfs_walkAddresses (f : ℕ → List ℕ) (x r : ℕ) : bfs f x r = walkAddresses f [x] r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [bfs, walkAddresses, ih]

theorem bfs_subset_walkAddresses {f g : ℕ → List ℕ} {x : ℕ} {roots : List ℕ}
    (hx : x ∈ roots) (h : ∀ z, f z ⊆ g z) {r s : ℕ} (hrs : r ≤ s) :
    bfs f x r ⊆ walkAddresses g roots s := by
  rw [bfs_walkAddresses]
  have root : [x] ⊆ roots := by
    intro z hz
    have hzx : z = x := List.mem_singleton.mp hz
    rw [hzx]
    exact hx
  intro y hy
  exact walkAddresses_prefix g roots hrs
    (walkAddresses_mono root h r hy)

def validRawNeighbors (D : Dims) (u : List Bool) (l z : ℕ) : List ℕ :=
  if z < (D.lv l).bases then actualRawNeighbors D u l z else []

theorem validRawNeighbors_subset (D : Dims) (u : List Bool) (l z : ℕ) :
    validRawNeighbors D u l z ⊆ actualRawNeighbors D u l z := by
  unfold validRawNeighbors
  split
  · exact List.Subset.refl _
  · intro a ha
    cases ha

private theorem range_map_eq_ofFn {A : Type*} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem validRawNeighbors_shrink (D : Dims) (u : List Bool) (l a g : ℕ)
    (hs : (D.lv l).slots = 2 ^ a) :
    validRawNeighbors D u l = nbOf shrinkNbrs (decS a g D u l) := by
  funext z
  unfold validRawNeighbors decS nbOf
  dsimp only
  by_cases hz : z < (D.lv l).bases
  · simp only [if_pos hz, actualRawNeighbors, hs, range_map_eq_ofFn]
    rfl
  · simp only [if_neg hz]
    rfl

theorem validRawNeighbors_refresh (D : Dims) (u : List Bool) (l a g dH : ℕ)
    (hs : (D.lv l).slots = 2 ^ a) :
    validRawNeighbors D u l = nbOf refreshNbrs (decR a g dH D u l) := by
  funext z
  unfold validRawNeighbors decR nbOf
  dsimp only
  by_cases hz : z < (D.lv l).bases
  · simp only [if_pos hz, actualRawNeighbors, hs, range_map_eq_ofFn]
    rfl
  · simp only [if_neg hz]
    rfl

end P1SolCone.SolCone
