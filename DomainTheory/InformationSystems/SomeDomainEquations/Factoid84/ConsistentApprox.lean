module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ElementsOfASystem.topElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

def ConsistentApprox (r : ApproximableMap P P) : Prop :=
  ¬ ((barElement 1).carrier ⊆ (r.toElement (barElement 0)).carrier)

end Factoid84

end DomainTheory.InformationSystems
