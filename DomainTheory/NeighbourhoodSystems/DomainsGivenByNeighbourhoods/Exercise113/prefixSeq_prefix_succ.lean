/-ai
The length-n prefix of a path is a prefix of the length-(n + 1) prefix.

The one-element list containing the bit at position n witnesses the prefix, by reflexivity of the appended equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem prefixSeq_prefix_succ (p : ℕ → Bool) (n : ℕ) :
    prefixSeq p n <+: prefixSeq p (n + 1) := ⟨[p n], rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise113
