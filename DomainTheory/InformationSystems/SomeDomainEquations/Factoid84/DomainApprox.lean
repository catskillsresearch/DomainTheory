/-ai
An element of the domain of domains is an approximable map from the powerset system P to itself that satisfies Scott's conditions (1) through (5).
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

/-- Elements of the domain of domains (Scott’s assertion after (1)–(5)). -/
def DomainApprox : Type :=
  { r : ApproximableMap P P // IsDomainApprox r }

end Factoid84

end DomainTheory.InformationSystems
