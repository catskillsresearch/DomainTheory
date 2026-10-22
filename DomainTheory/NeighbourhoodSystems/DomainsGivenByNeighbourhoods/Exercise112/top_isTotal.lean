/-ai
The limit element of the final-segment system is total.

Any element above the limit still lies below the limit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.le_top

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `top` is a total (maximal) element. -/
theorem top_isTotal : neighborhoodSystem.IsTotal top :=
  fun y _ => le_top y

end DomainTheory.NeighbourhoodSystems.Exercise112
