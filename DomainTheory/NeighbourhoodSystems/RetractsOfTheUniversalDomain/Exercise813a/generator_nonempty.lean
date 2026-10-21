/-ai
Every generator is nonempty.

The power of two at the generator's index has that bit set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem generator_nonempty (i : ℕ) : (generator i).Nonempty := ⟨2 ^ i, by simp⟩

end DomainTheory.NeighbourhoodSystems
