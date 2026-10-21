/-ai
Atom insertion sends an atom token to insertion of the underlying atom into a finite set of atoms, and sends the bottom token and both pair constructors to the identity.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def atomInsert : TreeToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .pairL _ | .pairR _ => id

end InfoSys

end DomainTheory.InformationSystems
