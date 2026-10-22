/-ai
The top token does not lie in the forget-finset of any finite set of U-tokens.

Such a membership would be the value of some U-token in the set, and that value being top contradicts the U-token predicate.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem not_mem_uForget_top (u : Finset UToken) : .top ∉ uForgetFinset u := by
  intro ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, _, hp⟩
  exact p.property.out hp

end InfoSys
end DomainTheory.InformationSystems
