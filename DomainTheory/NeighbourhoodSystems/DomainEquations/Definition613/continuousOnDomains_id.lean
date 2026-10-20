module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition68
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613.monotoneOnDomains_id

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe w







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
