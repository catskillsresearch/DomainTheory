/-ai
If Y is a neighbourhood of the second system, the true-tagged copy of Y is contained in the master of the concrete token sum.

The tagged copy of Y sits inside the tagged copy of the master, because Y lies below that master. That copy is the right summand of the union of the two tagged masters, and the union sits inside the master once the empty word is inserted.
ai-/
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
