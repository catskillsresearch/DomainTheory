/-ai
Right insertion of a sum token into a finite set of elements of the right summand inserts the underlying element when the token is a right token, and acts as the identity when the token is a left token or the sum bottom.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def rhtInsert : SumToken α β → Finset β → Finset β
  | .right y => insert y
  | .left _ => id
  | .bot => id

end InfoSys

end DomainTheory.InformationSystems
