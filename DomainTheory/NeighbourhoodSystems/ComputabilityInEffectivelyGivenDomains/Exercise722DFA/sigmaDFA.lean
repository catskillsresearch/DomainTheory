module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option

@[expose] public section

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
