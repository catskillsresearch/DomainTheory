module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ElementsOfASystem.topElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.topElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

def RogueApprox (r : ApproximableMap P P) : Prop :=
  r.toElement (barElement 1) = topElement

end Factoid84

end DomainTheory.InformationSystems
