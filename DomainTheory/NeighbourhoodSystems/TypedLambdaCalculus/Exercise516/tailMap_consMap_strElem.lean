module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


variable {β : Type*}


/-- `tail(b(σ)) = σ`. -/
theorem tailMap_consMap_strElem (b : Bool) (σ : Str) :
    tailMap.toElementMap ((consMap b).toElementMap (strElem σ)) = strElem σ := by
  rw [consMap_strElem, tailMap_strElem]; rfl

end DomainTheory.NeighbourhoodSystems.Exercise516
