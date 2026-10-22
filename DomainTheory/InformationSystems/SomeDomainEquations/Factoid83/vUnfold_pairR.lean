module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vUnfold_pairR (y : VToken) :
    vUnfold (.pairR y) = ⟨(.bot, y), ⟨Or.inl rfl⟩⟩ := rfl

end InfoSys
end DomainTheory.InformationSystems
