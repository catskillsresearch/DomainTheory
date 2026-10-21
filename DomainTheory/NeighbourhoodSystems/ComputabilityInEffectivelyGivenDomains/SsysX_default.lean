/-ai
The default neighbourhood for codes that are junk or have empty syntax is the master set of all bit lists.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Default neighbourhood for junk / empty-syntax indices: the master `Σ = Set.univ`. -/
def SsysX_default : Set (List Bool) := Set.univ

end Exercise722

end DomainTheory.NeighbourhoodSystems
