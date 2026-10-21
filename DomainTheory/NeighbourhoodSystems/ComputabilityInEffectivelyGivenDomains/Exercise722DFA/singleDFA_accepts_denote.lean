/-ai
The automaton for a single word accepts the denotation of the corresponding singleton expression.

Rewrite by exactness of the automaton for that singleton, and reverse the denotation of a singleton expression.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
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
