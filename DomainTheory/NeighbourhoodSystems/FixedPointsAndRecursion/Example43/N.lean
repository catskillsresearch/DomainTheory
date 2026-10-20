module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Example 4.3 (Scott 1981, PRG-19).** The natural-number neighbourhood system `N` on `Δ = ℕ`. -/
abbrev N : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memN Set.univ Set.univ_nonempty memN_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Example43
