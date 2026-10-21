/-ai
Unfolding a left-pair token with payload x yields the product token whose components are x and the bottom token, witnessed because the right component is the bottom token.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem vUnfold_pairL (x : VToken) :
    vUnfold (.pairL x) = ⟨(x, .bot), Or.inr rfl⟩ := rfl

end InfoSys
end DomainTheory.InformationSystems
