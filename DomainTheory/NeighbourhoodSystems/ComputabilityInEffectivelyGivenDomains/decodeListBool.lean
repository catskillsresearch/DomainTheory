module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

def decodeListBool (n : ℕ) : Option (List Bool) :=
  (decodeList n).mapM natBool

end Exercise722

end DomainTheory.NeighbourhoodSystems
