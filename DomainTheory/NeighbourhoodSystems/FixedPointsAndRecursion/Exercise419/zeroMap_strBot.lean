module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_nil
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_false
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_true
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.headValC_bot_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.liftC_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.T
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.emptyMap_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.zeroMap_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation14
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic.notation15

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44

variable {β : Type*}

@[simp] theorem zeroMap_strBot (σ : Str) :
    zeroMap.toElementMap (strBot σ) = headValC T T.bot 𝕥 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ

end DomainTheory.NeighbourhoodSystems.Exercise419
