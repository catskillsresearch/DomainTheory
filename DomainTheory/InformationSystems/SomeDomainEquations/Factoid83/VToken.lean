module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

inductive VToken where
  | bot : VToken
  | top : VToken
  | pairL : VToken → VToken
  | pairR : VToken → VToken
  deriving DecidableEq

end InfoSys
end DomainTheory.InformationSystems
