import P1ChkFinal.GreedyShrinkTarget

open P1Wit P1ChkGreedy P1SolGreedy

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000 in
theorem P1SolGreedy.greedyShrinkStage {𝕜 : Type*} [Field 𝕜] {factor : ℝ}
    (B : OAI.Computability.VPVNP.MotifBlocks.FixedBlock 𝕜 OAI.Computability.VPVNP.Compression.ShrinkMotif.demandSource
      OAI.Computability.VPVNP.Compression.ShrinkMotif.demandTarget OAI.Computability.VPVNP.Compression.ShrinkMotif.supply
      (OAI.Computability.VPVNP.MotifGrid.realWidths OAI.Computability.VPVNP.Compression.ShrinkMotif.demandMass)
      (OAI.Computability.VPVNP.MotifGrid.realWidths OAI.Computability.VPVNP.Compression.ShrinkMotif.supplyMass)
      (31 / 16) factor) :
    P1ChkFinal.GreedyStep.ShrinkStageTarget B := by
  intro a g ℓ X Dn ag x u hℓ hS hN hslots hag hpan
  have h9chk := C9chk_iff (Dn x.length) u ℓ X hN
  have h9 : C9fam Dn x u ℓ ↔ C9u (Dn x.length) u ℓ X :=
    ⟨fun h => h9chk.mp (h ⟨hℓ, hS⟩), fun h _ => h9chk.mpr h⟩
  unfold P1ChkFinal.GreedyStep.ShrinkTrue
  constructor
  · rintro ⟨h5, h6, h7, h8, h9fam⟩
    obtain ⟨s, ht⟩ := (C7fam_certifies B Dn ag x u hℓ hS hN hslots hag hpan h5 h6).mp h7
    exact ⟨colours_of_C5fam Dn x u hℓ hS hN hslots hpan h5,
      offsets_of_C6fam Dn ag x u hℓ hS hN hag hpan h6, s, ht,
      (C8fam_certifies B Dn ag x u hℓ hS hN hslots hag hpan h5 h6 s ht).mp h8,
      h9.mp h9fam⟩
  · rintro ⟨hc, ho, s, ht, he, hl⟩
    have hrec := SolDemand.recTrue_of_panelMatch (X := X) hpan
    have h5 : ∀ Y < ((Dn x.length).lv ℓ).bases, C5fam Dn x u (encIdx (Dn x.length) ℓ Y) := by
      apply (C5fam_level Dn x u hℓ hS).mpr
      intro Y hY
      obtain ⟨y, rfl⟩ := P1ChkFinal.exists_addr_eq X (hY.trans_le hN.le)
      exact (C5chk_iff' hrec hslots y).mpr ((C5u_iff (Dn x.length) u ℓ X).mpr hc y)
    have h6 : ∀ Y < ((Dn x.length).lv ℓ).bases, C6fam Dn ag x u (encIdx (Dn x.length) ℓ Y) := by
      apply (C6fam_level Dn ag x u hℓ hS).mpr
      rw [hag]
      intro Y hY
      obtain ⟨y, rfl⟩ := P1ChkFinal.exists_addr_eq X (hY.trans_le hN.le)
      exact (C6chk_iff hrec y).mpr ((C6u_iff (Dn x.length) u ℓ X).mpr ho y)
    exact ⟨h5, h6,
      (C7fam_certifies B Dn ag x u hℓ hS hN hslots hag hpan h5 h6).mpr ⟨s, ht⟩,
      (C8fam_certifies B Dn ag x u hℓ hS hN hslots hag hpan h5 h6 s ht).mpr he,
      h9.mpr hl⟩

#print axioms P1SolGreedy.greedyShrinkStage
