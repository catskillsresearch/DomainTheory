/-ai
On a principal element of the function space, the fixed-point operator returns the least fixed point of the least approximable map of that principal.

This is the principal-element clause of the extension of a monotone action on finite elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}



open ApproximableMap


/-- On a finite element `↑F`, `fix` returns `fix(↑F)` (the least fixed point of the least map of
`F`). -/
theorem fixMap_toElementMap_principal (V : NeighborhoodSystem α)
    {W : Set (ApproximableMap V V)} (hW : (funSpace V V).mem W) :
    (fixMap V).toElementMap ((funSpace V V).principal hW) =
      (toApproxMap ((funSpace V V).principal hW)).fixElement :=
  toElementMap_ofMono_principal _ _ W hW

end DomainTheory.NeighbourhoodSystems
