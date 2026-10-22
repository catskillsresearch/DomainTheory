module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.scFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.BasicInst38

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

/-- The principal element witnessed by a member of `scFamily t`. -/
def scPrincipal {t : U.Element} (i : scFamily t) : U.Element :=
  U.principal (t.sub i.2.2)

end DomainTheory.NeighbourhoodSystems
