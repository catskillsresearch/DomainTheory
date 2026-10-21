/-ai
A Boolean word lies in wordsUpTo n if and only if its length is at most n.

The numbered name example_722_words is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words.mem_wordsUpTo

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise722

set_option linter.unusedVariables false

theorem example_722_words : ∀ (n : Nat) {w : List Bool},
  Iff
    (@Membership.mem (List Bool) (List (List Bool)) (@List.instMembership (List Bool))
      (DomainTheory.NeighbourhoodSystems.Exercise722.wordsUpTo n) w)
    (@LE.le Nat instLENat (@List.length Bool w) n) :=
  DomainTheory.NeighbourhoodSystems.Exercise722.mem_wordsUpTo

end DomainTheory.NeighbourhoodSystems.Exercise722
