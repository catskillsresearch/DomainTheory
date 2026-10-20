module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- Consistency for `U`: finite `u ⊆ D_U` with `u ⊬_V ∇` (Scott (9)). -/
def UCon (u : Finset UToken) : Prop :=
  ¬ VEnt (uForgetFinset u) .top

end InfoSys

end DomainTheory.InformationSystems
