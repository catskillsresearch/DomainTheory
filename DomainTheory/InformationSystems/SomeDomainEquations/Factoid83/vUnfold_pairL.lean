module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false







































theorem vUnfold_pairL (x : VToken) :
    vUnfold (.pairL x) = ⟨(x, .bot), Or.inr rfl⟩ := rfl

end InfoSys
end DomainTheory.InformationSystems
