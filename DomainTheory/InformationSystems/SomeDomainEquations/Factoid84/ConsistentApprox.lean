module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- (5) `\bar 1 ⊈ r(\bar 0)` — `1` is excluded as inconsistent at the bottom. -/
def ConsistentApprox (r : ApproximableMap P P) : Prop :=
  ¬ ((barElement 1).carrier ⊆ (r.toElement (barElement 0)).carrier)

end Factoid84

end DomainTheory.InformationSystems
