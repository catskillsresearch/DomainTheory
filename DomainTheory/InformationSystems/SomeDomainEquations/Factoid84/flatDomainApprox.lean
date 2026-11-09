module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ElementsOfASystem.topElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.DomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

def flatDomainApprox : DomainApprox :=
  ⟨flatMap, flatMap.isDomain⟩

end Factoid84

end DomainTheory.InformationSystems
