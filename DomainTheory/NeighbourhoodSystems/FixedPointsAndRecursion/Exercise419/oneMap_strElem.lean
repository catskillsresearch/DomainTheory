/-ai
On a total element, the test one returns the total head value that is false on the empty string and on a false-headed string, and true on a true-headed string.

The equality is the total-element equation of the lift, applied to the head data of the test one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_bot_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.oneMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation15

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

@[simp] theorem oneMap_strElem (σ : Str) :
    oneMap.toElementMap (strElem σ) = headValC T 𝕗 𝕗 𝕥 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ

end DomainTheory.NeighbourhoodSystems.Exercise419
