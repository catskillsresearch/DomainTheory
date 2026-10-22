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
