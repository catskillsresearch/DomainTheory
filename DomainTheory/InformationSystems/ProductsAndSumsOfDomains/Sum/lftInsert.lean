/-ai
Left insertion of a sum token into a finite set of elements of the left summand inserts the underlying element when the token is a left token, and acts as the identity when the token is a right token or the sum bottom.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def lftInsert : SumToken α β → Finset α → Finset α
  | .left x => insert x
  | .right _ => id
  | .bot => id

end InfoSys

end DomainTheory.InformationSystems
