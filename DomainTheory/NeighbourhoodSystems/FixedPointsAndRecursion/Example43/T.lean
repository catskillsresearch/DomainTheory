/-ai
The truth domain of this example is the two-token truth domain of Example 1.2.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The two-token truth domain `T` of Example 1.2 (= `Example23.T`). -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T

end DomainTheory.NeighbourhoodSystems.Example43
