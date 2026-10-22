module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.IsProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Token type of the product system `A × B`. -/
def ProdToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : α × β // IsProdToken A B p}

end InfoSys

end DomainTheory.InformationSystems
