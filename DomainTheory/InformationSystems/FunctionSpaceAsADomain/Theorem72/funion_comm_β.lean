module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem funion_comm_β (u v : Finset β) : u ∪' v = v ∪' u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

end InfoSys

end DomainTheory.InformationSystems
