/-ai
The neighbourhood system of binary sequences is the nested-or-disjoint system of all finite strings whose neighbourhoods are cones or singletons. The master is the whole space, which is nonempty and equals the cone of the empty string, and every neighbourhood is contained in it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.memC
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44.nestedOrDisjoint

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example44

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB

/-- **Example 4.4 (Scott 1981, PRG-19).** The neighbourhood system `C` of finite or infinite binary
sequences on `Δ = Σ*`. -/
abbrev C : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memC Set.univ
    ⟨[], Set.mem_univ _⟩ (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint
    (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Example44
