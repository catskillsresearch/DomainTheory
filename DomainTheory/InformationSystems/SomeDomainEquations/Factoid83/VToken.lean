/-ai
The data objects of V are a bottom token Δ, a top token ∇, and left and right product copies of a token. Equality of these tokens is decidable.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Data objects of `V`: bottom `Δ`, top `∇`, and product left/right copies. -/
inductive VToken where
  | bot : VToken
  | top : VToken
  | pairL : VToken → VToken
  | pairR : VToken → VToken
  deriving DecidableEq

end InfoSys
end DomainTheory.InformationSystems
