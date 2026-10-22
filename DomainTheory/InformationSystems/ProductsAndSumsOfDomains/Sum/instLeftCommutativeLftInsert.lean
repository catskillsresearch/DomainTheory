module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeLftInsert :
    LeftCommutative (lftInsert : SumToken α β → Finset α → Finset α) :=
  ⟨fun p q s => by
    cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

end InfoSys

end DomainTheory.InformationSystems
