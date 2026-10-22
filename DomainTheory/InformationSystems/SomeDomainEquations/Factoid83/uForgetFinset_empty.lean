module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem uForgetFinset_empty : uForgetFinset (∅ : Finset UToken) = ∅ := rfl

end InfoSys
end DomainTheory.InformationSystems
