/-ai
Unfolding the bottom token of V yields the bottom token of the product V × V.

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







































theorem vUnfold_bot : vUnfold .bot = prodBot vSystem vSystem := rfl

end InfoSys
end DomainTheory.InformationSystems
