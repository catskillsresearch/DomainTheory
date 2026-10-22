module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.subU

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- The family of `subU`-self-consistent nbhds already in `t`'s filter. -/
def scFamily (t : U.Element) : Type := {T : Set ℚ // subU.rel T T ∧ t.mem T}

end DomainTheory.NeighbourhoodSystems
