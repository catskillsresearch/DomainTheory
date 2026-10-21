/-ai
The right-hand side of Scott's equation V ≅ V × V equals the product of the information system V with itself.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vRhs_eq_product : vRhs = productSystem vSystem vSystem := rfl

end InfoSys
end DomainTheory.InformationSystems
