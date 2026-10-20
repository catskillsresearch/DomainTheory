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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForget

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

def uForgetInsert : UToken → Finset VToken → Finset VToken :=
  fun t => insert (uForget t)

end InfoSys

end DomainTheory.InformationSystems
