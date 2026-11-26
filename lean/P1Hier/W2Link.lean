import P1Hier.W2
import P1Int.Links

/-!
# P1Hier.W2Link: same-statement check of W2 against the shared interface `P1Int.ParityHierarchy`

Copies of `P1Int/Interfaces.lean` and `P1Int/Links.lean` (unchanged, from research/p1/lean/Interfaces)
are compiled in the hier project for this check only.
-/

namespace P1Hier

/-- **W2 as the shared Prop**, from lane hierB's two parsers. -/
theorem parityHierarchy_of_parsers (d : MCode)
    (h2 : OAI.Computability.IntegerMultiplication.Code.Easy (UM.px2 d))
    (h5 : OAI.Computability.IntegerMultiplication.Code.Easy UM.decT2) : P1Int.ParityHierarchy :=
  P1Int.parityHierarchy_hier.mp (parity_hierarchy_of_parsers d h2 h5)

/-- **`P1Int.ParityHierarchy`, closed through copy A's route** (`Hierarchy.parity_hierarchy_of` with
the machine of `W2.lean`). Lane hierB's `UM.parityHierarchy_closed` is a second, independent term. -/
theorem parityHierarchy : P1Int.ParityHierarchy :=
  P1Int.parityHierarchy_hier.mp parity_hierarchy

/-- Both closures prove the same Prop. -/
example : type_of% @parityHierarchy = type_of% @UM.parityHierarchy_closed := rfl

end P1Hier

#print axioms P1Hier.parityHierarchy_of_parsers
#print axioms P1Hier.parityHierarchy
#print axioms P1Hier.UM.parityHierarchy_closed
