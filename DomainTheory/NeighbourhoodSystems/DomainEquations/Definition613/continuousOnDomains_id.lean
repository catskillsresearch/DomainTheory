/-ai
The identity endofunctor on domains is continuous on domains.

It is monotone on domains by the corresponding fact for the identity. For a nonempty directed family of subsystems whose neighbourhoods union to a subsystem U, unfolding the target-side family of the identity and membership in a union reduces the required equality to the hypothesis that the neighbourhoods of U are exactly the neighbourhoods belonging to some member of the family.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.monotoneOnDomains_id

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- The **identity functor is continuous on domains**: `targetFam` reduces to the plain neighbourhood
family, so directed-union preservation is exactly the hypothesis `hU` that `U` is the union. -/
theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_iUnion, exists_prop]
  exact hU Y

end DomainTheory.NeighbourhoodSystems
