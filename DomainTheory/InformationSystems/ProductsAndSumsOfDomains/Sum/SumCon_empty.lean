module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumBot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumEnt
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.sumSystem
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_lft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_rht

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem SumCon_empty : SumCon A B (∅ : Finset (SumToken α β)) :=
  Or.inl ⟨by rw [lftFinset.empty]; exact A.con_empty, by rw [rhtFinset.empty]⟩

end InfoSys
end DomainTheory.InformationSystems
