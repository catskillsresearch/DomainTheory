/-ai
The left projection of the union of two finite sets of sum tokens is the union of their left projections.

By extensionality, an element of the left projection of the union has its left token in the union, hence in one of the two sets, and so lies in the corresponding left projection. Conversely, an element of either left projection has its left token in that set, hence in the union, and so lies in the left projection of the union.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


variable (A : InfoSys α) (B : InfoSys β)


theorem lftFinset_funion (u v : Finset (SumToken α β)) :
    lftFinset (u ∪' v) = lftFinset u ∪' lftFinset v := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ u ∪' v := (mem_lftFinset).1 hx
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_lftFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inl ((mem_lftFinset).1 h)))
    · exact (mem_lftFinset).2 (mem_funion.mpr (Or.inr ((mem_lftFinset).1 h)))

end InfoSys
end DomainTheory.InformationSystems
