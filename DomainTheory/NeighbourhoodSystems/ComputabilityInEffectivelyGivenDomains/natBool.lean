/-ai
The natural-to-boolean interpretation sends 0 to false, 1 to true, and every other natural number to nothing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

def natBool (n : ℕ) : Option Bool :=
  match n with | 0 => some false | 1 => some true | _ => none

end Exercise722

end DomainTheory.NeighbourhoodSystems
