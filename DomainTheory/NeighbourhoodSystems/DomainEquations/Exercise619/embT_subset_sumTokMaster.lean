module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embT_subset_sumTokMaster {Y : Set Str} (hY : D₁.mem Y) :
    embBit true Y ⊆ sumTokMaster D₀ D₁ :=
  (embBit_subset.mpr (D₁.sub_master hY)).trans (Set.subset_union_right.trans (Set.subset_insert _ _))

end Exercise619

end DomainTheory.NeighbourhoodSystems
