module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.embT_subset_sumTokMaster

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem sumTokMaster_inter_embT {Y : Set Str} (hY : D₁.mem Y) :
    sumTokMaster D₀ D₁ ∩ embBit true Y = embBit true Y :=
  Set.inter_eq_right.mpr (embT_subset_sumTokMaster hY)

end Exercise619

end DomainTheory.NeighbourhoodSystems
