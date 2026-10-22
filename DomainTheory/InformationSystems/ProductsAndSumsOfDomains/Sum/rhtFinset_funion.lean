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


theorem rhtFinset_funion (u v : Finset (SumToken α β)) :
    rhtFinset (u ∪' v) = rhtFinset u ∪' rhtFinset v := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ u ∪' v := (mem_rhtFinset).1 hy
    rcases mem_funion.mp this with h | h
    · exact mem_funion.mpr (Or.inl ((mem_rhtFinset).2 h))
    · exact mem_funion.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hy
    rcases mem_funion.mp hy with h | h
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inl ((mem_rhtFinset).1 h)))
    · exact (mem_rhtFinset).2 (mem_funion.mpr (Or.inr ((mem_rhtFinset).1 h)))

end InfoSys
end DomainTheory.InformationSystems
