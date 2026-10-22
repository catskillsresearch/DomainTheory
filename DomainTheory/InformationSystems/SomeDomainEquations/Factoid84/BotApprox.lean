module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.botElement

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- (3) `\bar 0 ⊆ r(⊥)` — `0` plays the rôle of `Δ`. -/
def BotApprox (r : ApproximableMap P P) : Prop :=
  (barElement 0).carrier ⊆ (r.toElement botElement).carrier

end Factoid84

end DomainTheory.InformationSystems
