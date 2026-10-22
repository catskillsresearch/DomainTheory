module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


theorem sigmaDFA_accepts_denote : sigmaDFA.accepts = denote .sigma := by
  rw [sigmaDFA_accepts, denote_sigma]

end Exercise722
end DomainTheory.NeighbourhoodSystems
