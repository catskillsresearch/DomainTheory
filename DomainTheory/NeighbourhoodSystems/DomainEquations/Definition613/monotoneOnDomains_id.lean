module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w




/-- The **identity functor is monotone on domains**: it fixes objects and maps, so `T(D) ◁ T(E)` is
just `D ◁ E` and the projection pair is unchanged. -/
theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩

end DomainTheory.NeighbourhoodSystems
