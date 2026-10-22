/-ai
The set of points excluded by a cofinite filter is the set of natural numbers whose singleton complements belong to the filter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- The set of points *excluded* by a filter `x`: `toExcluded x = {n ∣ {n}ᶜ ∈ x}`. -/
def toExcluded (x : cofiniteSystem.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

end Cofinite

end DomainTheory.NeighbourhoodSystems
