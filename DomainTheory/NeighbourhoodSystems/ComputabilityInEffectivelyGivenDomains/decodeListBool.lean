/-ai
Decoding a natural number as a list of booleans decodes it as a list of natural numbers and interprets each entry as a boolean, failing if any entry is not a binary digit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.natBool

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

def decodeListBool (n : ℕ) : Option (List Bool) :=
  (decodeList n).mapM natBool

end Exercise722

end DomainTheory.NeighbourhoodSystems
