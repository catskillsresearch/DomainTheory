/-ai
A false-bit embedding of a set of strings is distinct from the master of the lift.

Equality would place the empty string, which belongs to the lift master, inside a tagged bit.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.nil_mem_liftTokMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem embF_ne_liftTokMaster {X : Set Str} : embBit false X ≠ liftTokMaster D := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_liftTokMaster)

end Exercise619

end DomainTheory.NeighbourhoodSystems
