module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.nil_mem_sumTokMaster

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

theorem embT_ne_sumTokMaster {Y : Set Str} : embBit true Y ≠ sumTokMaster D₀ D₁ := fun h =>
  nil_not_mem_embBit (h.symm ▸ nil_mem_sumTokMaster)

end Exercise619

end DomainTheory.NeighbourhoodSystems
