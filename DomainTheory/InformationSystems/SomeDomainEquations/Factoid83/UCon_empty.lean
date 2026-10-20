module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

























































theorem UCon_empty : UCon (∅ : Finset UToken) := by
  simpa [UCon, uForgetFinset_empty] using not_VEnt_empty_top

end InfoSys
end DomainTheory.InformationSystems
