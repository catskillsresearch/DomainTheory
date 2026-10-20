module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false























































theorem not_mem_uForget_top (u : Finset UToken) : .top ∉ uForgetFinset u := by
  intro ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, _, hp⟩
  exact p.property hp

end InfoSys
end DomainTheory.InformationSystems
