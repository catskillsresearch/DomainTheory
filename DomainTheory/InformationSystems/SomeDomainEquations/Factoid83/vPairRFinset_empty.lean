/-ai
The right projection of the empty finite set of tokens of V is empty.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
















theorem vPairRFinset_empty : vPairRFinset (∅ : Finset VToken) = ∅ := rfl

end InfoSys
end DomainTheory.InformationSystems
