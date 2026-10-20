module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

/-- The one-state DFA recognising `Σ = {0,1}*` (every word accepted). -/
def sigmaDFA : DFA Bool Unit where
  step _ _ := ()
  start := ()
  accept := Set.univ

end Exercise722

end DomainTheory.NeighbourhoodSystems
