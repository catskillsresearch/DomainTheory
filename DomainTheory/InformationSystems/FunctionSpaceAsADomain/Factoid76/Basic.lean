module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.constOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


end InfoSys
end DomainTheory.InformationSystems
