module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embF_subset_sumTokMaster {X : Set Str} (hX : D₀.mem X) :
    embBit false X ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₀.sub_master hX)).trans (Set.subset_union_left.trans (Set.subset_insert _ _))

end Exercise619

end DomainTheory.NeighbourhoodSystems
