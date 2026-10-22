/-ai
Unfolding a right-pair token with payload y yields the product token whose components are the bottom token and y, witnessed because the left component is the bottom token.

The two sides are definitionally equal.
ai-/
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
