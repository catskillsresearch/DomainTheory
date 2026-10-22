/-ai
A natural number lies in the excluded-point set of a cofinite filter exactly when the complement of its singleton belongs to the filter.

The two sides are definitionally identical.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.cofiniteSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.mem_ofExcluded
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise116.toExcluded

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem mem_toExcluded {x : cofiniteSystem.Element} {n : ℕ} :
    n ∈ toExcluded x ↔ x.mem ({n}ᶜ) := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems
