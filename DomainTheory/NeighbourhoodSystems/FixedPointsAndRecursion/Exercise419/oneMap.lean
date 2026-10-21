/-ai
The test one from the sequence domain to the truth domain is the approximable map obtained by lifting head values that send the empty string and a false-headed string to false and a true-headed string to true, with bottom in place of the empty-string value on partial elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_bot_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation15

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

/-- **Example 4.4 — `one`.** `one(Λ) = false`, `one(0x) = false`, `one(1x) = true`, strict. -/
def oneMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥)

end DomainTheory.NeighbourhoodSystems.Exercise419
