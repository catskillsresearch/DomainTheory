/-ai
This module gathers the bounded word enumeration used for the emptiness search of Exercise 7.22. It re-exports the regular-expression development, the list wordsUpTo of Boolean words of length at most n, and the test anyMatchesB, and it meta-imports the basic regular-expression setup. The commentary records that these are the ingredients of the later short-word search.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words.wordsUpTo
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words.anyMatchesB
public meta import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section

/-!
# Exercise 7.22 — bounded word enumeration for emptiness search

Lists every `List Bool` of length at most `n` (`wordsUpTo n`), and provides `anyMatchesB` to test
whether any word in a finite list is accepted by the `matchesB` matcher. The characterisation
`mem_wordsUpTo` is the length bound used later for pumping-based short-word search (Session C4).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


end Exercise722
end DomainTheory.NeighbourhoodSystems
