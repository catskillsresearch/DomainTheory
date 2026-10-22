/-ai
Every word belongs to the denotation of the universal expression.

Membership is membership of the word in the set of all words.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


/-- `denote .sigma = Σ` contains every word. -/
theorem mem_denote_sigma (w : List Bool) : w ∈ denote .sigma := Set.mem_univ w

end Exercise722
end DomainTheory.NeighbourhoodSystems
