/-ai
The denotation of the expression sigma is distinct from the denotation of containsZero. The one-letter word whose entry is true lies in the former and not in the latter.

The numbered name example_722_regular is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.sigma_ne_containsZero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_regular : @Ne (Set (List Bool))
  (DomainTheory.NeighbourhoodSystems.Exercise722.denote DomainTheory.NeighbourhoodSystems.Exercise722.SExpr.sigma)
  (DomainTheory.NeighbourhoodSystems.Exercise722.denote DomainTheory.NeighbourhoodSystems.Exercise722.containsZero) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.sigma_ne_containsZero

end DomainTheory.NeighbourhoodSystems.Exercise722
