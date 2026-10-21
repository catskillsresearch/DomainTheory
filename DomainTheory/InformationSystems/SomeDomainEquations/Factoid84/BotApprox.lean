/-ai
Scott's bottom condition on an approximable map r from the powerset system P to itself says that the finite element of 0 is contained in the image of the bottom element. The token 0 plays the rôle of the bottom token.
ai-/
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
