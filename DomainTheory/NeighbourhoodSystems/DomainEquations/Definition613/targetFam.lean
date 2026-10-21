/-ai
The target-side neighbourhood family of the image of a subsystem D of E is the set of those subsets of the carrier of the image of E whose transport along the equality of the image carriers is a neighbourhood of the image of D.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneAt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.MonotoneOnDomains

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w

/-- The **target-side neighbourhood family** of the image `T(D)` of a subsystem `h : D ◁ E`, viewed
over `T(E)`'s carrier (using `MonotoneAt.carrier_eq` to transport neighbourhoods of `T(D)` to that
carrier). This is the data on which "`λD. T(D)` is approximable" is expressed. -/
def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}

end DomainTheory.NeighbourhoodSystems
