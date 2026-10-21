/-ai
If X is a neighbourhood of the first system, the intersection of the concrete sum master with the false-tagged copy of X equals that copy.

The false-tagged copy of X is already contained in the sum master, so intersecting with the master leaves it unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embF_subset_sumTokMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem sumTokMaster_inter_embF {X : Set Str} (hX : D₀.mem X) :
    sumTokMaster D₀ D₁ ∩ embBit false X = embBit false X :=
  Set.inter_eq_right.mpr (embF_subset_sumTokMaster hX)

end Exercise619

end DomainTheory.NeighbourhoodSystems
