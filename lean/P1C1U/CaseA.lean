import P1C1U.Transpose
import P1C1U.PhysicalRuns

namespace P1C1U.AstraC1U

theorem displaySimulation : DisplaySimulation := by
  intro M
  refine ⟨Physical.machine M, 3, ?_⟩
  intro N T recN x
  obtain ⟨⟨s, hs⟩, sound⟩ := recN x
  constructor
  · exact Physical.realize M x _ _ s (by omega)
  · intro seed out h
    obtain ⟨v⟩ := Physical.reflects M x _ out seed h
    exact sound out v

end P1C1U.AstraC1U

theorem P1C1U.caseA (price : OAI.Computability.MultitapeWeakETH.PriceTwo) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool, C1Challenge.coNTIMELinLog L ∧
      ¬ C1Challenge.NTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  P1C1U.AstraC1U.caseA_of_displaySimulation P1C1U.AstraC1U.displaySimulation price

#print axioms P1C1U.caseA
