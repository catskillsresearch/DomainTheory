module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.topElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- (4) `⊤ = r(\bar 1)` — `1` plays the rôle of the rogue `∇`. -/
def RogueApprox (r : ApproximableMap P P) : Prop :=
  r.toElement (barElement 1) = topElement

end Factoid84

end DomainTheory.InformationSystems
