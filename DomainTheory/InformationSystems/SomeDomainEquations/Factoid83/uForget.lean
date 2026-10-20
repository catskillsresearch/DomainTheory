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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

def uForget (t : UToken) : VToken := t.val

end InfoSys

end DomainTheory.InformationSystems
