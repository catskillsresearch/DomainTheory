module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strBot_le_strBot_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strBot_le_strElem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.strElem_le_strElem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.not_strElem_le_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_true
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.SLe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

/-- `SLe` characterizes the element order on `shapeElem`. -/
theorem shapeElem_le_iff {b b' : Bool} {σ σ' : Str} :
    shapeElem b σ ≤ shapeElem b' σ' ↔ SLe b σ b' σ' := by
  cases b <;> cases b' <;>
    simp only [shapeElem_true, shapeElem_false, SLe, strElem_le_strElem_iff,
      strBot_le_strBot_iff, strBot_le_strElem_iff, true_and]
  · exact ⟨fun h => absurd h not_strElem_le_strBot, fun h => absurd h (by simp)⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
