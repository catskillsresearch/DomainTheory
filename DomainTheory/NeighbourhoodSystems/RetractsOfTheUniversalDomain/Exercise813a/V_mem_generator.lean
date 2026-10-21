/-ai
Every generator is a V-neighbourhood.

The generator equals a level set, and that level set is nonempty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.generator_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a.generator_eq_levelSet

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem








theorem V_mem_generator (i : ℕ) : V.mem (generator i) :=
  generator_eq_levelSet i ▸ ⟨i + 1, _, rfl, generator_eq_levelSet i ▸ generator_nonempty i⟩

end DomainTheory.NeighbourhoodSystems
