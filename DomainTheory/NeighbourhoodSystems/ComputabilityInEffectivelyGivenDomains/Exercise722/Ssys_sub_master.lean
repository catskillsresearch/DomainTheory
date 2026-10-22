module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.InS
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.mem_concat

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-- Every member of `S` is a subset of `Σ`. -/
theorem Ssys_sub_master {X : Set (List Bool)} (_h : InS X) : X ⊆ Set.univ :=
  Set.subset_univ _

end Exercise722

end DomainTheory.NeighbourhoodSystems
