module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.liftRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def liftPair (u : Finset α) (v : Finset β) : Finset (ProdToken A B) :=
  liftLeft A B u ∪' liftRight A B v

end InfoSys

end DomainTheory.InformationSystems
