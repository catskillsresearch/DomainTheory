module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.singleDFA_accepts

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


theorem singleDFA_accepts_denote (σ : List Bool) : (singleDFA σ).accepts = denote (.single σ) := by
  rw [singleDFA_accepts]; exact (denote_single σ).symm

end Exercise722
end DomainTheory.NeighbourhoodSystems
