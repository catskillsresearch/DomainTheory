module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.liftTokMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}

theorem embF_subset_liftTokMaster {X : Set Str} (hX : D.mem X) :
    embBit false X ⊆ liftTokMaster D :=
  (embBit_subset.mpr (D.sub_master hX)).trans (Set.subset_insert _ _)

end Exercise619

end DomainTheory.NeighbourhoodSystems
