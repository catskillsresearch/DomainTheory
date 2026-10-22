module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


/-- `{a}{b} = {a ++ b}`: concatenation of singletons is the singleton of the concatenation. -/
theorem concat_singleton (a b : List Bool) : concat {a} {b} = {a ++ b} := by
  ext w
  simp only [mem_concat, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a', rfl, b', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, b, rfl, rfl⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
